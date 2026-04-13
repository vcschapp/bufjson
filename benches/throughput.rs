pub mod generator;

use bufjson::lexical::{
    Token,
    fixed::FixedAnalyzer,
    pipe::{Pipe, PipeAnalyzer},
    read::ReadAnalyzer,
};
use bytes::Bytes;
use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use generator::{Generator, LineSep, NumRules, StrRules, WhiteRules};
use json_streaming::shared::JsonReadToken;
use rand::{SeedableRng, rngs::StdRng};
use rand_distr::Normal;
use serde_json::Value;
use std::convert::Infallible;

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

fn bench_throughput_bufjson(c: &mut Criterion) {
    const LEN: usize = 100 * 1024; // 100 KiB;

    let mut generator = Generator::default()
        .with_rng(StdRng::seed_from_u64(0x20200824))
        .with_white_rules(WhiteRules::pretty(LineSep::N, b' ', 2));
    let mut json_with_space = Vec::with_capacity(LEN);
    generator.generate(LEN, &mut json_with_space).unwrap();

    generator = Generator::default()
        .with_rng(StdRng::seed_from_u64(0x20230424))
        .with_white_rules(WhiteRules::Off);
    let mut json_no_space = Vec::with_capacity(LEN);
    generator.generate(LEN, &mut json_no_space).unwrap();

    let mut group = c.benchmark_group("throughput_bufjson");
    group.throughput(Throughput::Bytes(LEN as u64));
    group.sample_size(20);

    // Fixed analyzer without content fetch.
    group.bench_function("FixedAnalyzer: no content fetch", |b| {
        b.iter(|| read_no_content!(FixedAnalyzer::new(json_with_space.as_slice())));
        b.iter(|| read_no_content!(FixedAnalyzer::new(json_no_space.as_slice())));
    });

    // Fixed analyzer with content fetch.
    group.bench_function("FixedAnalyzer: content fetch", |b| {
        b.iter(|| read_with_content!(FixedAnalyzer::new(json_with_space.as_slice())));
        b.iter(|| read_with_content!(FixedAnalyzer::new(json_no_space.as_slice())));
    });

    // Pipe analyzer without content fetch.
    group.bench_function("PipeAnalyzer: no content fetch", |b| {
        b.iter(|| read_no_content!(PipeAnalyzer::new(HalfPipe::new(json_with_space.clone()))));
        b.iter(|| read_no_content!(PipeAnalyzer::new(HalfPipe::new(json_no_space.clone()))));
    });

    // Pipe analyzer with content fetch.
    group.bench_function("PipeAnalyzer: content fetch", |b| {
        b.iter(|| read_with_content!(PipeAnalyzer::new(HalfPipe::new(json_with_space.clone()))));
        b.iter(|| read_with_content!(PipeAnalyzer::new(HalfPipe::new(json_no_space.clone()))));
    });

    // Read analyzer without content fetch.
    group.bench_function("ReadAnalyzer: no content fetch", |b| {
        b.iter(|| read_no_content!(ReadAnalyzer::new(json_with_space.as_slice())));
        b.iter(|| read_no_content!(ReadAnalyzer::new(json_no_space.as_slice())));
    });

    // Read analyzer with content fetch.
    group.bench_function("ReadAnalyzer: with content fetch", |b| {
        b.iter(|| read_with_content!(ReadAnalyzer::new(json_with_space.as_slice())));
        b.iter(|| read_with_content!(ReadAnalyzer::new(json_no_space.as_slice())));
    });

    // Parser over fixed analyzer without content fetch.
    group.bench_function("Parser: no content fetch", |b| {
        b.iter(|| read_no_content!(FixedAnalyzer::new(json_with_space.as_slice()).into_parser()));
        b.iter(|| read_no_content!(FixedAnalyzer::new(json_no_space.as_slice()).into_parser()));
    });

    // Parser over fixed analyzer with content fetch.
    group.bench_function("Parser: with content fetch", |b| {
        b.iter(|| read_with_content!(FixedAnalyzer::new(json_with_space.as_slice()).into_parser()));
        b.iter(|| read_with_content!(FixedAnalyzer::new(json_no_space.as_slice()).into_parser()));
    });
}

fn bench_throughput_compare(c: &mut Criterion) {
    const LEN: usize = 100 * 1024; // 100 KiB

    // This will generate random JSON where the numbers are within range of the number types that
    // `serde_json` uses so it doesn't fail to parse.
    let mut g = Generator::default()
        .with_num_rules(NumRules::new(
            Normal::new(4.0, 3.0).unwrap(),
            0.35,
            0.30,
            0.50,
            0.01,
        ))
        .with_rng(StdRng::seed_from_u64(0x2020082420230424));
    let mut buf = Vec::with_capacity(LEN);
    g.generate(LEN, &mut buf).unwrap();

    // Separate dataset for `json-streaming` which cannot handle surrogate pairs in \uXXXX
    // escape sequences (it encodes each half as CESU-8 instead of valid UTF-8).
    let mut g_no_sp = Generator::default()
        .with_num_rules(NumRules::new(
            Normal::new(4.0, 3.0).unwrap(),
            0.35,
            0.30,
            0.50,
            0.01,
        ))
        .with_str_rules(StrRules::default().avoid_surrogate_pairs())
        .with_rng(StdRng::seed_from_u64(0x2020082420230424));
    let mut buf_no_sp = Vec::with_capacity(LEN);
    g_no_sp.generate(LEN, &mut buf_no_sp).unwrap();

    let mut group = c.benchmark_group("throughput_compare");
    group.throughput(Throughput::Bytes(LEN as u64));
    group.sample_size(20);

    // Fixed analyzer without content fetch.
    group.bench_function("FixedAnalyzer: no content fetch", |b| {
        b.iter(|| read_no_content!(FixedAnalyzer::new(buf.as_slice())));
    });

    // `serde_json` parse into schemaless in-memory value.
    group.bench_function("serde_json", |b| {
        b.iter(|| {
            let _: Value = serde_json::from_slice(&buf).unwrap();
        })
    });

    // `json-streaming` blocking reader, consuming all tokens.
    group.bench_function("json-streaming: blocking", |b| {
        b.iter(|| {
            let mut reader = buf_no_sp.as_slice();
            let mut jr = json_streaming::blocking::JsonReader::new(LEN, &mut reader);
            loop {
                match black_box(jr.next().unwrap()) {
                    JsonReadToken::EndOfStream => break,
                    _ => continue,
                }
            }
        })
    });

    // `json-streaming` nonblocking reader via tokio, consuming all tokens.
    let rt = tokio::runtime::Builder::new_current_thread()
        .build()
        .unwrap();
    group.bench_function("json-streaming: nonblocking", |b| {
        b.iter(|| {
            rt.block_on(async {
                let mut reader = buf_no_sp.as_slice();
                let mut jr = json_streaming::nonblocking::JsonReader::new(LEN, &mut reader);
                loop {
                    match black_box(jr.next().await.unwrap()) {
                        JsonReadToken::EndOfStream => break,
                        _ => continue,
                    }
                }
            })
        })
    });
}

criterion_group!(benches, bench_throughput_bufjson, bench_throughput_compare);
criterion_main!(benches);

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
