use crate::generator::{Generator, LineSep, NumRules, Root, StrRules, ValueDist, WhiteRules};
use bytes::Bytes;
use rand::{RngExt, SeedableRng, rngs::StdRng};
use rand_distr::Normal;
use std::sync::OnceLock;

/// An aspect of JSON that an input is focused on benchmarking, meaning an aspect of JSON that an
/// input can meaningfully probe for, not merely something the input happens to contain.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Focus {
    Lit,
    Num,
    NumFloat,
    NumExp,
    NumInt,
    Str,
    StrAscii,
    StrEscSimple,
    StrEscUnicode,
    StrUtf8,
    White,
    WhiteCr,
    WhiteCrLf,
    WhiteLf,
    WhitePretty,
}

/// A token-density bucket, derived from an input's `token_density` (tokens per KiB).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DensityBucket {
    Low,
    Medium,
    High,
}

/// Upper bound (exclusive) of the Low bucket / lower bound of Medium.
pub const DENSITY_LOW_MAX: f64 = 50.0;
/// Lower bound (exclusive) of the High bucket / upper bound of Medium.
pub const DENSITY_HIGH_MIN: f64 = 200.0;

pub const ALL_DENSITY_BUCKETS: [DensityBucket; 3] = [
    DensityBucket::Low,
    DensityBucket::Medium,
    DensityBucket::High,
];

impl DensityBucket {
    pub fn label(&self) -> &'static str {
        match self {
            DensityBucket::Low => "low_lt_50",
            DensityBucket::Medium => "medium_50_200",
            DensityBucket::High => "high_gt_200",
        }
    }
}

pub enum Source {
    File {
        name: &'static str,
        sha256: &'static str,
    },
    Generated {
        name: &'static str,
        generator: fn() -> std::io::Result<Bytes>,
    },
}

pub(crate) struct Input {
    source: Source,
    desc: &'static str,
    focus: &'static [Focus],
    token_density: f64,
    bytes: OnceLock<Bytes>,
}

impl Input {
    const fn file(
        name: &'static str,
        sha256: &'static str,
        desc: &'static str,
        focus: &'static [Focus],
        token_density: f64,
    ) -> Self {
        Self {
            source: Source::File { name, sha256 },
            desc,
            focus,
            token_density,
            bytes: OnceLock::new(),
        }
    }

    const fn generated(
        name: &'static str,
        generator: fn() -> std::io::Result<Bytes>,
        desc: &'static str,
        focus: &'static [Focus],
        token_density: f64,
    ) -> Self {
        Self {
            source: Source::Generated { name, generator },
            desc,
            focus,
            token_density,
            bytes: OnceLock::new(),
        }
    }

    pub fn name(&self) -> &'static str {
        match &self.source {
            Source::File { name, .. } | Source::Generated { name, .. } => name,
        }
    }

    pub fn focus(&self) -> &[Focus] {
        self.focus
    }

    pub fn token_density(&self) -> f64 {
        self.token_density
    }

    pub fn density_bucket(&self) -> DensityBucket {
        let d = self.token_density;
        if d < DENSITY_LOW_MAX {
            DensityBucket::Low
        } else if d <= DENSITY_HIGH_MIN {
            DensityBucket::Medium
        } else {
            DensityBucket::High
        }
    }

    pub fn bytes(&self) -> &Bytes {
        self.bytes.get_or_init(|| {
            let r: std::io::Result<Bytes> = match &self.source {
                Source::File { name, sha256 } => std::fs::read(format!(
                    "{}/benches/data/{}",
                    env!("CARGO_MANIFEST_DIR"),
                    name
                ))
                .map(Bytes::from)
                .inspect(|b| assert_sha256(name, sha256, b.as_ref())),
                Source::Generated { generator, .. } => generator(),
            };

            r.unwrap_or_else(|e| panic!("could not read input `{}`: {e}", self.name()))
        })
    }
}

fn generate_bytes<R: RngExt>(mut generator: Generator<R>, len: usize) -> std::io::Result<Bytes> {
    let mut buf = Vec::with_capacity(len);
    generator.generate(len, &mut buf)?;

    Ok(Bytes::from(buf))
}

fn assert_sha256(name: &str, expected: &str, bytes: &[u8]) {
    use sha2::{Digest, Sha256};
    use std::fmt::Write;

    let mut actual = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        let _ = write!(actual, "{byte:02x}");
    }

    assert_eq!(actual, expected, "SHA-256 mismatch for input file `{name}`");
}

pub(crate) static INPUTS: [Input; 18] = [
    // File-based inputs. Keep sorted in name order. Do not rename the files to follow any kind of
    // normalized naming scheme, since the goal is to use the same filenames and file content as
    // other projects to maximize the amount of signal the benchmarks produce.
    Input::file(
        "canada.json",
        "f83b3b354030d5dd58740c68ac4fecef64cb730a0d12a90362a7f23077f50d78",
        "Canada's national border as a GeoJSON feature",
        &[Focus::NumFloat],
        152.11,
    ),
    Input::file(
        "citm_catalog.json",
        "a73e7a883f6ea8de113dff59702975e60119b4b58d451d518a929f31c92e2059",
        "Box-office catalog of events, venues, and seats",
        &[Focus::NumInt, Focus::WhitePretty, Focus::WhiteLf],
        125.88,
    ),
    Input::file(
        "github_events.json",
        "c9eebb2cf2d46649059e9d48700919bacb3e8e0fb58452065a1a9de7778fd22e",
        "Page from GitHub's public activity feed",
        &[Focus::WhitePretty, Focus::WhiteLf],
        112.91,
    ),
    Input::file(
        "mesh.json",
        "45bc8bf429340a874a7af8ea7056d60497402f80f55dba1e6ecc4ca8f1e46aff",
        "Geometry of a 3D model, minified (same data as `mesh.pretty.json`)",
        &[Focus::NumInt, Focus::NumFloat],
        320.25,
    ),
    Input::file(
        "mesh.pretty.json",
        "b08b8b1881b131f82f8a6b8f8b0226235488154d7363cc8302153e724776ae8e",
        "Geometry of a 3D model, pretty-printed (same data as `mesh.json`)",
        &[Focus::WhitePretty, Focus::WhiteLf],
        151.60,
    ),
    Input::file(
        "numbers.json",
        "82e9ddfe00963110ed8a0704e7df4d1ad1af9c0f336d1b24431ebc63cf430a2b",
        "Bare array of ten thousand (and one) numbers; all have a decimal, only one has an exponent",
        &[Focus::NumFloat],
        136.46,
    ),
    Input::file(
        "twitter.json",
        "a08b769f32b95f426cbc3abafcec65c1a19d3eb544d4ddf320eae142c99efc5d",
        "Search response from Twitter's API (same logical data as `twitterescaped.json`)",
        &[Focus::Str],
        136.35,
    ),
    Input::file(
        "twitterescaped.json",
        "2a288b5af4691c55b6f40fa534225b3e08b8d8b7f7ca4ed29bc5c7c81566ed4a",
        r#"Search response from Twitter's API with multi-byte UTF-8 characters converted to `\u` escapes (same logical data as `twitter.json`)"#,
        &[Focus::StrEscUnicode],
        100.62,
    ),
    // Generated inputs for additional coverage. Keep sorted in name order.
    Input::generated(
        "generated:ascii",
        || {
            generate_bytes(
                Generator::default()
                    .with_rng(StdRng::seed_from_u64(0xA5C11))
                    .with_root(Root::Arr)
                    .with_value_dist(ValueDist::new(0.0, 0.0, 0.0, 0.0, 1.0))
                    .with_str_rules(StrRules::new(
                        Normal::new(10.0, 10.0).unwrap(),
                        Normal::new(30.0, 60.0).unwrap(),
                        0.0,
                        0.0,
                        0.0,
                        0.0,
                        false,
                    ))
                    .with_white_rules(WhiteRules::Off),
                100 * 1024,
            )
        },
        "Generated benchmark input focused on pure ASCII strings",
        &[Focus::StrAscii],
        46.85,
    ),
    Input::generated(
        "generated:default_no_space",
        || {
            generate_bytes(
                Generator::default()
                    .with_rng(StdRng::seed_from_u64(0x20230424))
                    .with_white_rules(WhiteRules::Off),
                100 * 1024,
            )
        },
        r#"Original generated benchmark input, formerly known as `json_no_space`"#,
        &[],
        19.58,
    ),
    Input::generated(
        "generated:default_with_space",
        || {
            generate_bytes(
                Generator::default()
                    .with_rng(StdRng::seed_from_u64(0x20200824))
                    .with_white_rules(WhiteRules::pretty(LineSep::N, b' ', 2)),
                100 * 1024,
            )
        },
        r#"Original generated benchmark input, formerly known as `json_with_space`"#,
        &[],
        27.51,
    ),
    Input::generated(
        "generated:escaped_simple",
        || {
            generate_bytes(
                Generator::default()
                    .with_rng(StdRng::seed_from_u64(0x5CE))
                    .with_root(Root::Arr)
                    .with_value_dist(ValueDist::new(0.0, 0.0, 0.0, 0.0, 1.0))
                    .with_str_rules(StrRules::new(
                        Normal::new(10.0, 10.0).unwrap(),
                        Normal::new(30.0, 60.0).unwrap(),
                        0.0,
                        1.0,
                        0.0,
                        0.0,
                        false,
                    ))
                    .with_white_rules(WhiteRules::Off),
                100 * 1024,
            )
        },
        r#"Generated benchmark input dominated by simple escapes (\n, \t, \" …)"#,
        &[Focus::StrEscSimple],
        46.67,
    ),
    Input::generated(
        "generated:integers",
        || {
            generate_bytes(
                Generator::default()
                    .with_rng(StdRng::seed_from_u64(0x1))
                    .with_root(Root::Arr)
                    .with_value_dist(ValueDist::new(0.0, 0.0, 1.0, 0.0, 0.0)) // all numbers
                    .with_num_rules(NumRules::new(
                        Normal::new(12.0, 4.0).unwrap(),
                        0.15,
                        0.05,
                        0.0, // no fractions
                        0.0, // no exponents
                        false,
                    ))
                    .with_white_rules(WhiteRules::Off),
                100 * 1024,
            )
        },
        "Generated benchmark input focused on integer numbers (no fraction or exponent)",
        &[Focus::NumInt],
        170.85,
    ),
    Input::generated(
        "generated:literals",
        || {
            generate_bytes(
                Generator::default()
                    .with_rng(StdRng::seed_from_u64(0x117))
                    .with_root(Root::Arr)
                    .with_value_dist(ValueDist::new(0.0, 1.0, 0.0, 0.0, 0.0)) // all literals
                    .with_white_rules(WhiteRules::Off),
                100 * 1024,
            )
        },
        "Generated benchmark input focused on the literals true, false, and null",
        &[Focus::Lit],
        384.11,
    ),
    Input::generated(
        "generated:scientific",
        || {
            generate_bytes(
                Generator::default()
                    .with_rng(StdRng::seed_from_u64(0x5C1))
                    .with_root(Root::Arr)
                    .with_value_dist(ValueDist::new(0.0, 0.0, 1.0, 0.0, 0.0)) // all numbers
                    .with_num_rules(NumRules::new(
                        Normal::new(18.0, 3.0).unwrap(),
                        0.15,
                        0.02,
                        0.13,
                        0.85,
                        false,
                    ))
                    .with_white_rules(WhiteRules::Off),
                25 * 1024,
            )
        },
        "Generated benchmark input focused on scientific notation numbers (e/E notation)",
        &[Focus::NumExp],
        112.84,
    ),
    Input::generated(
        "generated:utf_8",
        || {
            generate_bytes(
                Generator::default()
                    .with_rng(StdRng::seed_from_u64(0x07F8))
                    .with_root(Root::Arr)
                    .with_value_dist(ValueDist::new(0.0, 0.0, 0.0, 0.0, 1.0))
                    .with_str_rules(StrRules::new(
                        Normal::new(10.0, 10.0).unwrap(),
                        Normal::new(30.0, 60.0).unwrap(),
                        0.0,
                        0.0,
                        0.0,
                        0.90,
                        false,
                    ))
                    .with_white_rules(WhiteRules::Off),
                100 * 1024,
            )
        },
        "Generated benchmark input very high percentage of non-ASCII string bytes",
        &[Focus::StrUtf8],
        46.67,
    ),
    Input::generated(
        "generated:white_cr",
        || {
            generate_bytes(
                Generator::default()
                    .with_rng(StdRng::seed_from_u64(0x0D))
                    .with_value_dist(ValueDist::new(0.10, 0.20, 0.15, 0.15, 0.40))
                    .with_str_rules(StrRules::new(
                        Normal::new(10.0, 10.0).unwrap(),
                        Normal::new(10.0, 12.0).unwrap(),
                        0.1,
                        0.0,
                        0.05,
                        0.05,
                        false,
                    ))
                    .with_white_rules(WhiteRules::pretty(LineSep::R, b'\t', 2)),
                100 * 1024,
            )
        },
        "Generated benchmark input focused on carriage return line breaks (shorter string values and a slightly higher literal share raise token density)",
        &[Focus::WhiteCr, Focus::WhitePretty],
        73.49,
    ),
    Input::generated(
        "generated:white_crlf",
        || {
            generate_bytes(
                Generator::default()
                    .with_rng(StdRng::seed_from_u64(0x0D0A))
                    .with_value_dist(ValueDist::new(0.05, 0.20, 0.60, 0.10, 0.05))
                    .with_num_rules(NumRules::new(
                        Normal::new(2.0, 1.5).unwrap(),
                        0.15,
                        0.20,
                        0.0,
                        0.0,
                        false,
                    ))
                    .with_white_rules(WhiteRules::pretty(LineSep::Rn, b' ', 2)),
                100 * 1024,
            )
        },
        "Generated benchmark input focused on Windows-style line breaks (short numbers with higher number and literal weighting raise token density)",
        &[Focus::WhiteCrLf, Focus::WhitePretty],
        79.59,
    ),
];
