mod generator;

use bufjson::lexical::fixed::FixedAnalyzer;
use bufjson::syntax::Parser;
use criterion::{Criterion, black_box, criterion_group, criterion_main};

// TODO: delete me
fn sample_json() -> &'static str {
    r#"{"foo":"bar","baz":[null,123]}"#
}

fn parse_json(c: &mut Criterion) {
    c.bench_function("parse_sample", |b| {
        let json = sample_json();
        b.iter(|| {
            let mut parser = Parser::new(FixedAnalyzer::new(json.as_bytes()));
            while !black_box(parser.next()).is_terminal() {
                black_box(parser.content());
            }
        });
    });
}

criterion_group!(benches, parse_json);
criterion_main!(benches);
