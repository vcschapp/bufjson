pub mod generator;

use bufjson::lexical::{Token, fixed::FixedAnalyzer, read::ReadAnalyzer};
use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use generator::{Generator, LineSep, NumRules, WhiteRules};
use rand::{SeedableRng, rngs::StdRng};
use rand_distr::Normal;
use serde_json::Value;

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
}

criterion_group!(benches, bench_throughput_bufjson, bench_throughput_compare);
criterion_main!(benches);
