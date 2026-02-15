mod generator;

use bufjson::{
    lexical::{Token, fixed::FixedAnalyzer, read::ReadAnalyzer},
    syntax::Parser,
};
use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};
use generator::{Generator, LineSep, WhiteRules};
use rand::{SeedableRng, rngs::StdRng};

macro_rules! read_no_content {
    ($x:ident) => {
        loop {
            match $x.next() {
                Token::Eof => break,
                Token::Err => panic!("{}", $x.err()),
                _ => continue,
            }
        }
    };
}

macro_rules! read_with_content {
    ($x:ident) => {
        loop {
            match $x.next() {
                Token::Eof => break,
                Token::Err => panic!("{}", $x.err()),
                _ => black_box({
                    let _ = $x.content().literal();
                }),
            }
        }
    };
}

fn bench_throughput(c: &mut Criterion) {
    const LEN: usize = 5 * 1024; // 5 MiB;

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

    let mut group = c.benchmark_group("throughput");
    group.throughput(Throughput::Bytes(2 * LEN as u64));
    group.sample_size(10);

    // Fixed analyzer without content fetch.
    group.bench_function("FixedAnalyzer: no content fetch", |b| {
        let mut an = FixedAnalyzer::new(json_with_space.as_slice());
        b.iter(|| read_no_content!(an));

        let mut an = FixedAnalyzer::new(json_no_space.as_slice());
        b.iter(|| read_no_content!(an));
    });

    // Fixed analyzer with content fetch.
    group.bench_function("FixedAnalyzer: content fetch", |b| {
        let mut an = FixedAnalyzer::new(json_with_space.as_slice());
        b.iter(|| read_with_content!(an));

        let mut an = FixedAnalyzer::new(json_no_space.as_slice());
        b.iter(|| read_with_content!(an));
    });

    // Read analyzer without content fetch.
    group.bench_function("ReadAnalyzer: no content fetch", |b| {
        let mut an = ReadAnalyzer::new(json_with_space.as_slice());
        b.iter(|| read_no_content!(an));

        let mut an = ReadAnalyzer::new(json_no_space.as_slice());
        b.iter(|| read_no_content!(an));
    });

    // Read analyzer with content fetch.
    group.bench_function("ReadAnalyzer: with content fetch", |b| {
        let mut an = ReadAnalyzer::new(json_with_space.as_slice());
        b.iter(|| read_with_content!(an));

        let mut an = ReadAnalyzer::new(json_no_space.as_slice());
        b.iter(|| read_with_content!(an));
    });

    // Parser over fixed analyzer without content fetch.
    group.bench_function("Parser: no content fetch", |b| {
        let mut parser = FixedAnalyzer::new(json_with_space.as_slice()).into_parser();
        b.iter(|| read_no_content!(parser));

        let mut parser = FixedAnalyzer::new(json_no_space.as_slice()).into_parser();
        b.iter(|| read_no_content!(parser));
    });

    // Parser over fixed analyzer with content fetch.
    group.bench_function("Parser: with content fetch", |b| {
        let mut parser = FixedAnalyzer::new(json_with_space.as_slice()).into_parser();
        b.iter(|| read_with_content!(parser));

        let mut parser = FixedAnalyzer::new(json_no_space.as_slice()).into_parser();
        b.iter(|| read_with_content!(parser));
    });
}

criterion_group!(benches, bench_throughput);
criterion_main!(benches);
