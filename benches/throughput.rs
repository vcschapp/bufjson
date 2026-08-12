#[allow(dead_code)]
pub(crate) mod generator;
#[allow(dead_code)]
mod input;

use bufjson::lexical::{
    Token,
    fixed::FixedAnalyzer,
    pipe::{Pipe, PipeAnalyzer},
    read::ReadAnalyzer,
};
use bytes::Bytes;
use criterion::measurement::WallTime;
use criterion::{
    BatchSize, BenchmarkGroup, Criterion, Throughput, black_box, criterion_group, criterion_main,
};
use input::{Focus, INPUTS, Input};
use json_streaming::shared::JsonReadToken;
use serde_json::Value;
use std::convert::Infallible;
use std::sync::OnceLock;
use struson::reader::{JsonReader, JsonStreamReader, ValueType};

macro_rules! read_no_content {
    ($x:expr) => {{
        let mut y = $x;
        loop {
            match y.next() {
                Token::Eof => break,
                Token::Err => panic!("{}", y.err()),
                _ => continue,
            }
        }
    }};
}

macro_rules! read_with_content {
    ($x:expr) => {{
        let mut y = $x;
        loop {
            match y.next() {
                Token::Eof => break,
                Token::Err => panic!("{}", y.err()),
                _ => black_box({
                    let _ = y.content().literal();
                }),
            }
        }
    }};
}

#[derive(Clone, Copy)]
pub enum OtherCrate {
    Jsn,
    JsonStreaming,
    SerdeJson,
    SimdJson,
    Struson,
}

#[derive(Clone, Copy)]
pub enum Target {
    Bufjson,
    OtherCrate(OtherCrate),
}

#[derive(Clone, Copy)]
enum Run {
    /// Input is borrowed; any copy happens inside the timed body (e.g. simd `-copy`'s `to_vec`).
    Borrowed(fn(&Bytes)),
    /// Needs a fresh owned mutable buffer; the copy is done in iter_batched's untimed setup, so
    /// only the parse itself is timed (simd `-nocopy`).
    OwnedMut(fn(&mut [u8])),
}

struct Bench {
    name: &'static str,
    target: Target,
    run: Run,
    supports: fn(&Input) -> bool,
}

fn supports_all(_i: &Input) -> bool {
    true
}

fn supports_no_surrogate(i: &Input) -> bool {
    // json-streaming (as of v1.0.3) mis-encodes Unicode-escape surrogate pairs as CESU-8 rather
    // than valid UTF-8 and then aborts on the invalid bytes it produced (see COMPARE.md, note 1).
    // Skip any input that actually contains a high-surrogate `\u` escape (\uD800..=\uDBFF), whether
    // it is the input's focus (twitterescaped) or merely incidental (the default StrRules emit ~5%
    // `\u` escapes, a fraction of which are surrogate pairs).
    let bytes = i.bytes();
    !bytes.windows(6).any(|w| {
        w[0] == b'\\'
            && w[1] == b'u'
            && w[2].eq_ignore_ascii_case(&b'd')
            && matches!(w[3].to_ascii_uppercase(), b'8' | b'9' | b'A' | b'B')
            && w[4].is_ascii_hexdigit()
            && w[5].is_ascii_hexdigit()
    })
}

fn run_fixed_nocontent(d: &Bytes) {
    read_no_content!(FixedAnalyzer::new(d.as_ref()));
}

fn run_fixed_content(d: &Bytes) {
    read_with_content!(FixedAnalyzer::new(d.as_ref()));
}

fn run_pipe_nocontent(d: &Bytes) {
    read_no_content!(PipeAnalyzer::new(HalfPipe::new((*d).clone())));
}

fn run_pipe_content(d: &Bytes) {
    read_with_content!(PipeAnalyzer::new(HalfPipe::new((*d).clone())));
}

fn run_read_nocontent(d: &Bytes) {
    read_no_content!(ReadAnalyzer::new(d.as_ref()));
}

fn run_read_content(d: &Bytes) {
    read_with_content!(ReadAnalyzer::new(d.as_ref()));
}

fn run_parser_nocontent(d: &Bytes) {
    read_no_content!(FixedAnalyzer::new(d.as_ref()).into_parser());
}

fn run_parser_content(d: &Bytes) {
    read_with_content!(FixedAnalyzer::new(d.as_ref()).into_parser());
}

fn run_serde_parse(d: &Bytes) {
    black_box(serde_json::from_slice::<serde::de::IgnoredAny>(d.as_ref()).unwrap());
}

fn run_serde_value(d: &Bytes) {
    black_box(serde_json::from_slice::<Value>(d.as_ref()).unwrap());
}

fn run_simd_tape(d: &Bytes) {
    let mut v = d.to_vec();
    black_box(simd_json::to_tape(&mut v).unwrap());
}

fn run_simd_value(d: &Bytes) {
    let mut v = d.to_vec();
    black_box(simd_json::to_owned_value(&mut v).unwrap());
}

// In-place simd-json variants: the buffer copy is done by iter_batched's untimed setup (see
// bench_general), so only the parse itself is measured.
fn simd_tape_inplace(b: &mut [u8]) {
    black_box(simd_json::to_tape(b).unwrap());
}

fn simd_value_inplace(b: &mut [u8]) {
    black_box(simd_json::to_owned_value(b).unwrap());
}

// One fresh, throwaway mutable copy per logical run, byte-weighted identically to the timed loops.
fn nocopy_buffers(datas: &[&Bytes], counts: &[usize]) -> Vec<Vec<u8>> {
    datas
        .iter()
        .zip(counts)
        .flat_map(|(d, &cnt)| std::iter::repeat_with(|| d.to_vec()).take(cnt))
        .collect()
}

fn tokio_rt() -> &'static tokio::runtime::Runtime {
    static RT: OnceLock<tokio::runtime::Runtime> = OnceLock::new();
    RT.get_or_init(|| {
        tokio::runtime::Builder::new_current_thread()
            .build()
            .unwrap()
    })
}

fn run_json_streaming_blocking(d: &Bytes) {
    let mut reader = d.as_ref();
    let mut jr = json_streaming::blocking::JsonReader::new(d.len(), &mut reader);
    loop {
        match black_box(jr.next().unwrap()) {
            JsonReadToken::EndOfStream => break,
            _ => continue,
        }
    }
}
fn run_json_streaming_nonblocking(d: &Bytes) {
    tokio_rt().block_on(async {
        let mut reader = d.as_ref();
        let mut jr = json_streaming::nonblocking::JsonReader::new(d.len(), &mut reader);
        loop {
            match black_box(jr.next().await.unwrap()) {
                JsonReadToken::EndOfStream => break,
                _ => continue,
            }
        }
    });
}

fn run_jsn_observing(d: &Bytes) {
    for token in jsn::TokenReader::new(d.as_ref()) {
        black_box(token.unwrap());
    }
}

fn run_jsn_dry_run(d: &Bytes) {
    let mut tokens = jsn::TokenReader::new(d.as_ref()).into_iter();
    black_box(tokens.dry_run().unwrap());
}

fn run_struson(d: &Bytes) {
    let mut jr = JsonStreamReader::new_custom(
        d.as_ref(),
        struson::reader::ReaderSettings {
            track_path: false,
            restrict_number_values: false,
            ..Default::default()
        },
    );
    struson_consume_value(&mut jr);
    jr.consume_trailing_whitespace().unwrap();
}

static GENERAL: &[Bench] = &[
    Bench {
        name: "fixed/nocontent",
        target: Target::Bufjson,
        run: Run::Borrowed(run_fixed_nocontent),
        supports: supports_all,
    },
    Bench {
        name: "fixed/content",
        target: Target::Bufjson,
        run: Run::Borrowed(run_fixed_content),
        supports: supports_all,
    },
    Bench {
        name: "pipe/nocontent",
        target: Target::Bufjson,
        run: Run::Borrowed(run_pipe_nocontent),
        supports: supports_all,
    },
    Bench {
        name: "pipe/content",
        target: Target::Bufjson,
        run: Run::Borrowed(run_pipe_content),
        supports: supports_all,
    },
    Bench {
        name: "read/nocontent",
        target: Target::Bufjson,
        run: Run::Borrowed(run_read_nocontent),
        supports: supports_all,
    },
    Bench {
        name: "read/content",
        target: Target::Bufjson,
        run: Run::Borrowed(run_read_content),
        supports: supports_all,
    },
    Bench {
        name: "parser/nocontent",
        target: Target::Bufjson,
        run: Run::Borrowed(run_parser_nocontent),
        supports: supports_all,
    },
    Bench {
        name: "parser/content",
        target: Target::Bufjson,
        run: Run::Borrowed(run_parser_content),
        supports: supports_all,
    },
    Bench {
        name: "serde_json/parse",
        target: Target::OtherCrate(OtherCrate::SerdeJson),
        run: Run::Borrowed(run_serde_parse),
        supports: supports_all,
    },
    Bench {
        name: "serde_json/value",
        target: Target::OtherCrate(OtherCrate::SerdeJson),
        run: Run::Borrowed(run_serde_value),
        supports: supports_all,
    },
    Bench {
        name: "simd-json/tape-copy",
        target: Target::OtherCrate(OtherCrate::SimdJson),
        run: Run::Borrowed(run_simd_tape),
        supports: supports_all,
    },
    Bench {
        name: "simd-json/tape-nocopy",
        target: Target::OtherCrate(OtherCrate::SimdJson),
        run: Run::OwnedMut(simd_tape_inplace),
        supports: supports_all,
    },
    Bench {
        name: "simd-json/value-copy",
        target: Target::OtherCrate(OtherCrate::SimdJson),
        run: Run::Borrowed(run_simd_value),
        supports: supports_all,
    },
    Bench {
        name: "simd-json/value-nocopy",
        target: Target::OtherCrate(OtherCrate::SimdJson),
        run: Run::OwnedMut(simd_value_inplace),
        supports: supports_all,
    },
    Bench {
        name: "json-streaming/blocking",
        target: Target::OtherCrate(OtherCrate::JsonStreaming),
        run: Run::Borrowed(run_json_streaming_blocking),
        supports: supports_no_surrogate,
    },
    Bench {
        name: "json-streaming/nonblocking",
        target: Target::OtherCrate(OtherCrate::JsonStreaming),
        run: Run::Borrowed(run_json_streaming_nonblocking),
        supports: supports_no_surrogate,
    },
    Bench {
        name: "jsn/observing",
        target: Target::OtherCrate(OtherCrate::Jsn),
        run: Run::Borrowed(run_jsn_observing),
        supports: supports_all,
    },
    Bench {
        name: "jsn/dry-run",
        target: Target::OtherCrate(OtherCrate::Jsn),
        run: Run::Borrowed(run_jsn_dry_run),
        supports: supports_all,
    },
    Bench {
        name: "struson",
        target: Target::OtherCrate(OtherCrate::Struson),
        run: Run::Borrowed(run_struson),
        supports: supports_all,
    },
];

static GRANULAR_SUBJECTS: &[(&str, Run)] = &[
    ("bufjson/fixed", Run::Borrowed(run_fixed_nocontent)),
    ("bufjson/parser", Run::Borrowed(run_parser_nocontent)),
    (
        "competitor/serde_json/parse",
        Run::Borrowed(run_serde_parse),
    ),
    (
        "competitor/simd-json/tape-nocopy",
        Run::OwnedMut(simd_tape_inplace),
    ),
];

static GRANULAR_FOCUSES: &[(&str, Focus)] = &[
    ("Lit", Focus::Lit),
    ("NumExp", Focus::NumExp),
    ("NumFloat", Focus::NumFloat),
    ("NumInt", Focus::NumInt),
    ("StrAscii", Focus::StrAscii),
    ("StrUtf8", Focus::StrUtf8),
    ("StrEscSimple", Focus::StrEscSimple),
    ("StrEscUnicode", Focus::StrEscUnicode),
    ("WhiteCr", Focus::WhiteCr),
    ("WhiteCrLf", Focus::WhiteCrLf),
    ("WhiteLf", Focus::WhiteLf),
    ("WhitePretty", Focus::WhitePretty),
];

fn balanced_run_counts(lens: &[usize]) -> Vec<usize> {
    let max = lens.iter().copied().max().unwrap_or(1);
    lens.iter()
        .map(|&l| ((max as f64 / l.max(1) as f64).round() as usize).max(1))
        .collect()
}

fn subject_path(b: &Bench) -> String {
    match b.target {
        Target::Bufjson => format!("bufjson/{}", b.name),
        Target::OtherCrate(_) => format!("competitor/{}", b.name),
    }
}

fn bench_subject(group: &mut BenchmarkGroup<WallTime>, id: String, datas: &[&Bytes], run: Run) {
    if datas.is_empty() {
        return;
    }
    let lens: Vec<usize> = datas.iter().map(|d| d.len()).collect();
    let counts = balanced_run_counts(&lens);
    let total: u64 = lens
        .iter()
        .zip(&counts)
        .map(|(&l, &c)| (l * c) as u64)
        .sum();
    group.throughput(Throughput::Bytes(total));
    group.bench_function(id, |bn| match run {
        Run::Borrowed(f) => bn.iter(|| {
            for (&d, &cnt) in datas.iter().zip(&counts) {
                for _ in 0..cnt {
                    f(d);
                }
            }
        }),
        Run::OwnedMut(f) => bn.iter_batched(
            || nocopy_buffers(datas, &counts),
            |mut bufs| {
                for buf in &mut bufs {
                    f(buf);
                }
                bufs
            },
            BatchSize::PerIteration,
        ),
    });
}

fn bench_general(c: &mut Criterion) {
    let mut group = c.benchmark_group("general");
    group.sample_size(20);

    for b in GENERAL {
        let datas: Vec<&Bytes> = INPUTS
            .iter()
            .filter(|&i| (b.supports)(i))
            .map(Input::bytes)
            .collect();
        bench_subject(&mut group, subject_path(b), &datas, b.run);
    }
}

fn bench_granular(c: &mut Criterion) {
    let mut group = c.benchmark_group("granular");
    group.sample_size(20);

    for (subj_path, run) in GRANULAR_SUBJECTS {
        for (foc_name, foc) in GRANULAR_FOCUSES {
            let datas: Vec<&Bytes> = INPUTS
                .iter()
                .filter(|i| i.focus().contains(foc))
                .map(Input::bytes)
                .collect();
            bench_subject(&mut group, format!("{subj_path}/{foc_name}"), &datas, *run);
        }
    }
}

criterion_group!(benches, bench_general, bench_granular);
criterion_main!(benches);

fn struson_consume_value(jr: &mut JsonStreamReader<&[u8]>) {
    match jr.peek().unwrap() {
        ValueType::Object => {
            jr.begin_object().unwrap();
            while jr.has_next().unwrap() {
                let _ = black_box(jr.next_name().unwrap());
                struson_consume_value(jr);
            }
            jr.end_object().unwrap();
        }
        ValueType::Array => {
            jr.begin_array().unwrap();
            while jr.has_next().unwrap() {
                struson_consume_value(jr);
            }
            jr.end_array().unwrap();
        }
        ValueType::String => {
            let _ = black_box(jr.next_str().unwrap());
        }
        ValueType::Number => {
            let _ = black_box(jr.next_number_as_str().unwrap());
        }
        ValueType::Boolean => {
            let _ = black_box(jr.next_bool().unwrap());
        }
        ValueType::Null => {
            jr.next_null().unwrap();
        }
    }
}

// A Pipe that provides a view of an input buffer as two `Bytes` values representing the first and
// second halves.
//
// The idea is to simulate a minor amount of splitting input across buffers to make the
// `PipeAnalyzer` benchmark representative of intended real world use cases.
struct HalfPipe([Option<Bytes>; 2]);

impl HalfPipe {
    fn new(input: impl Into<Bytes>) -> Self {
        let mut a = input.into();
        let b = a.split_off(a.len() / 2);

        Self([Some(a), Some(b)])
    }
}

impl Pipe for HalfPipe {
    type Error = Infallible;

    fn recv(&mut self) -> Option<Result<Bytes, Self::Error>> {
        if self.0[0].is_some() {
            self.0[0].take().map(Ok)
        } else if self.0[1].is_some() {
            self.0[1].take().map(Ok)
        } else {
            None
        }
    }
}
