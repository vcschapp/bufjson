#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
perf_orchestrate.py -- fixed-N perf-measurement orchestrator for bufjson.

Answers two questions rigorously across a 3x3 matrix (3 program variants x 3
lexical analyzers):

  * Q-H1        : "Is there more work per byte?"  (instructions/byte,
                  cycles/byte, dcache-misses/byte)
  * Q-READ-STALLS: "What is the source of ReadAnalyzer's stalls, per byte?"
                  (dcache-miss/byte, dcache-miss%, IPC)

Variants (git SHAs):
    baseline  eeab453
    branchy   4e6af3a
    simple    26fa6b9

Analyzers: fixed, pipe, read.

How it works
------------
For each variant it creates a detached ``git worktree`` OUTSIDE the repo,
injects the fixed-N harness (``examples/perf_harness.rs``, embedded below in
``HARNESS_SRC``), builds it ``--release`` with a per-worktree target dir, then
drives it under ``perf stat`` while pinned to a single core with
``taskset -c 3``.

Two perf counter groups are measured SEPARATELY (they are distinct ``perf stat``
invocations so counters are not multiplexed):

    GroupA: task-clock, cycles, instructions, branches, branch-misses
    GroupB: instructions, L1-icache-load-misses, iTLB-load-misses,
            L1-dcache-loads, L1-dcache-load-misses

Counter availability is PROBED up front and unavailable counters degrade
gracefully to ``n/a`` (e.g. ``stalled-cycles-*`` are unsupported on this host,
which is why they are not part of the groups).

Measurements are INTERLEAVED to cancel slow thermal/frequency drift: the loop
order is round -> group -> analyzer -> variant, with *variant innermost* so the
three variants of a given (analyzer, group) are always measured back-to-back.
A throwaway warm-up harness run precedes every measured ``perf stat``.

Frequency control
------------------
Running as root is NOT required. If run as root, the CPU frequency is locked
(disable turbo via intel_pstate/no_turbo and set the ``performance`` cpufreq
governor) and the ORIGINAL state is restored on exit (including on error/trap).
If not root, it proceeds with taskset pinning only and reports per-byte / ratio
metrics, which are frequency-invariant and therefore valid regardless.

Privilege handling under sudo
-----------------------------
Only the sysfs frequency-lock writes need root. When launched via ``sudo``,
EVERY other child process (git worktree add/remove/prune, ``cargo build``,
``perf stat`` and the harness binary) is dropped back to the ORIGINAL invoking
user (SUDO_USER) via subprocess ``user=``/``group=`` plus a reconstructed
``env=`` (HOME=user home, ~/.cargo/bin on PATH, CARGO_HOME/RUSTUP_HOME passed
through). This makes the rustup ``cargo`` shim resolve the toolchain and avoids
creating root-owned artifacts in ~/.cargo or the repo's .git/worktrees. Running
as *real* root without sudo (SUDO_USER unset) is refused with a clear message.
See ``compute_privilege_context`` / ``privilege_kwargs``.

Usage
-----
    ./perf_orchestrate.py                # no-fetch (default), rounds=6, N=20000
    ./perf_orchestrate.py --fetch        # exercise content-fetch code path
    ./perf_orchestrate.py --n 5000 --rounds 3
    ./perf_orchestrate.py --dry-run      # print the interleave schedule only
    ./perf_orchestrate.py --smoke        # tiny end-to-end proof (1 cell)

The heavy pure logic (perf parsing, per-byte math, table formatting, schedule
generation, root/frequency handling, counter probing) lives in module-level
functions so it can be unit tested with no root and no benchmark run. See
``test_perf_orchestrate.py``.
"""

import argparse
import atexit
import math
import os
import pwd
import shutil
import subprocess
import sys
import tempfile

# --------------------------------------------------------------------------- #
# Constants / configuration                                                   #
# --------------------------------------------------------------------------- #

# bytes processed per harness iteration: two 100 KiB inputs => 2 * 102400.
BYTES_PER_ITER = 204800

# (name, sha) for each program variant, in canonical order.
VARIANTS = [
    ("baseline", "eeab453"),
    ("branchy", "4e6af3a"),
    ("simple", "26fa6b9"),
]

ANALYZERS = ["fixed", "pipe", "read"]

# perf counter groups, measured as SEPARATE `perf stat` invocations.
GROUP_EVENTS = {
    "A": ["task-clock", "cycles", "instructions", "branches", "branch-misses"],
    "B": [
        "instructions",
        "L1-icache-load-misses",
        "iTLB-load-misses",
        "L1-dcache-loads",
        "L1-dcache-load-misses",
    ],
}
GROUPS = ["A", "B"]

# sysfs paths for (root-only) frequency locking.
NO_TURBO_PATH = "/sys/devices/system/cpu/intel_pstate/no_turbo"
GOVERNOR_GLOB = "/sys/devices/system/cpu/cpu*/cpufreq/scaling_governor"

DEFAULT_N = 20000
DEFAULT_ROUNDS = 6
DEFAULT_REPS = 1
DEFAULT_CPU = 3

# The fixed-N harness, injected verbatim into each worktree's
# examples/perf_harness.rs. Kept as a constant so no Cargo.toml edit is needed
# (Cargo auto-discovers examples/).
HARNESS_SRC = r'''// Fixed-N perf-measurement harness for bufjson.
//
// This file is injected by perf_orchestrate.py into a per-SHA git worktree. It
// is an auto-discovered Cargo example (examples/perf_harness.rs) so that no
// Cargo.toml edit is required to build it.
//
// CLI (positional, exact order):
//     perf_harness <fixed|pipe|read> <N> <nofetch|fetch>
//
// Behavior:
//   * Silent on success; exits 0.
//   * Any malformed argument => exits 2.
//   * No timing or printing in the hot loop; `black_box` guards prevent the
//     optimizer from eliding work.
//   * Each iteration processes BOTH generated inputs (with-space then
//     no-space), so bytes_per_iteration = 2 * LEN = 204800.

#[path = "../benches/generator.rs"]
mod generator;

use bufjson::lexical::{
    Token,
    fixed::FixedAnalyzer,
    pipe::{Pipe, PipeAnalyzer},
    read::ReadAnalyzer,
};
use bytes::Bytes;
use generator::{Generator, LineSep, WhiteRules};
use rand::{SeedableRng, rngs::StdRng};
use std::{convert::Infallible, hint::black_box, process::ExitCode};

// 100 KiB per input. Two inputs are processed per iteration, giving a
// bytes_per_iteration of 2 * LEN = 204800. The orchestrator relies on this
// exact value to compute total bytes = N * 204800.
const LEN: usize = 100 * 1024;

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

// Verbatim copy of HalfPipe from benches/throughput.rs: presents an input
// buffer as two `Bytes` halves to make the PipeAnalyzer path representative of
// real-world split-buffer use.
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

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 3 {
        return ExitCode::from(2);
    }

    let analyzer = args[0].as_str();
    if !matches!(analyzer, "fixed" | "pipe" | "read") {
        return ExitCode::from(2);
    }

    let n: u64 = match args[1].parse() {
        Ok(n) => n,
        Err(_) => return ExitCode::from(2),
    };

    let fetch = match args[2].as_str() {
        "nofetch" => false,
        "fetch" => true,
        _ => return ExitCode::from(2),
    };

    // Generate both inputs once, using the same seeds and whitespace rules as
    // benches/throughput.rs so results are comparable.
    let mut g = Generator::default()
        .with_rng(StdRng::seed_from_u64(0x20200824))
        .with_white_rules(WhiteRules::pretty(LineSep::N, b' ', 2));
    let mut with_space = Vec::with_capacity(LEN);
    g.generate(LEN, &mut with_space).unwrap();

    let mut g = Generator::default()
        .with_rng(StdRng::seed_from_u64(0x20230424))
        .with_white_rules(WhiteRules::Off);
    let mut no_space = Vec::with_capacity(LEN);
    g.generate(LEN, &mut no_space).unwrap();

    let with_space = black_box(with_space);
    let no_space = black_box(no_space);

    // Prepare the pipe inputs as `bytes::Bytes` ONCE, before the measured
    // N-iteration loop. `Bytes::from(Vec<u8>)` takes ownership zero-copy, so
    // the single `.clone()` of each 100 KiB Vec here is a one-time copy OUTSIDE
    // the loop (the owned Vecs must stay alive for the fixed/read paths). Inside
    // the loop the pipe path then does only an O(1) `Bytes::clone()` (an atomic
    // refcount bump, NOT a 100 KiB memcpy) plus HalfPipe's O(1) `split_off`, so
    // no variant-independent input copy pollutes the per-byte counters.
    let with_space_bytes = black_box(Bytes::from(with_space.clone()));
    let no_space_bytes = black_box(Bytes::from(no_space.clone()));

    for _ in 0..n {
        match (analyzer, fetch) {
            ("fixed", false) => {
                read_no_content!(FixedAnalyzer::new(with_space.as_slice()));
                read_no_content!(FixedAnalyzer::new(no_space.as_slice()));
            }
            ("fixed", true) => {
                read_with_content!(FixedAnalyzer::new(with_space.as_slice()));
                read_with_content!(FixedAnalyzer::new(no_space.as_slice()));
            }
            ("pipe", false) => {
                // O(1) Bytes::clone (refcount bump) + O(1) HalfPipe split_off;
                // no 100 KiB Vec copy inside the measured loop.
                read_no_content!(PipeAnalyzer::new(HalfPipe::new(with_space_bytes.clone())));
                read_no_content!(PipeAnalyzer::new(HalfPipe::new(no_space_bytes.clone())));
            }
            ("pipe", true) => {
                read_with_content!(PipeAnalyzer::new(HalfPipe::new(with_space_bytes.clone())));
                read_with_content!(PipeAnalyzer::new(HalfPipe::new(no_space_bytes.clone())));
            }
            ("read", false) => {
                read_no_content!(ReadAnalyzer::new(with_space.as_slice()));
                read_no_content!(ReadAnalyzer::new(no_space.as_slice()));
            }
            ("read", true) => {
                read_with_content!(ReadAnalyzer::new(with_space.as_slice()));
                read_with_content!(ReadAnalyzer::new(no_space.as_slice()));
            }
            _ => unreachable!(),
        }
    }

    ExitCode::SUCCESS
}
'''


# --------------------------------------------------------------------------- #
# Pure function: perf stat CSV parsing                                        #
# --------------------------------------------------------------------------- #

# Sentinels perf uses when a counter did not run / is unavailable.
_NOT_SUPPORTED = "<not supported>"
_NOT_COUNTED = "<not counted>"


def _perf_rows(text):
    """Yield (raw_value, event_name) tuples from `perf stat -x,` stderr text.

    The `-x,` machine-readable format emits one comma-separated record per
    event where field 0 is the value and field 2 is the event name (field 1 is
    the unit, which may be empty). Comment/blank lines are skipped. Trailing
    fields (run%, metric, stddev with -r) are ignored, so the parser is robust
    across perf versions.
    """
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split(",")
        if len(parts) < 3:
            continue
        event = parts[2].strip()
        if not event:
            continue
        yield parts[0].strip(), event


def parse_perf_stat(text):
    """Parse `perf stat -x,` stderr into ``{event_name: float | None}``.

    ``<not counted>`` / ``<not supported>`` / unparseable values map to None.
    """
    counters = {}
    for raw, event in _perf_rows(text):
        if raw in (_NOT_SUPPORTED, _NOT_COUNTED, ""):
            counters[event] = None
            continue
        try:
            counters[event] = float(raw)
        except ValueError:
            counters[event] = None
    return counters


def event_status(text, event):
    """Return 'ok' | 'not-supported' | 'missing' for ``event`` in perf output."""
    for raw, name in _perf_rows(text):
        if name == event:
            return "not-supported" if raw == _NOT_SUPPORTED else "ok"
    return "missing"


def filter_supported(events, probe_output_by_event):
    """Split ``events`` into (supported, unsupported).

    ``probe_output_by_event`` maps each event name to the perf stderr produced
    by probing that single event (e.g. against ``true``). This is a pure
    function so it can be unit tested without running perf.
    """
    supported, unsupported = [], []
    for ev in events:
        text = probe_output_by_event.get(ev, "")
        if event_status(text, ev) == "ok":
            supported.append(ev)
        else:
            unsupported.append(ev)
    return supported, unsupported


# --------------------------------------------------------------------------- #
# Pure function: per-byte metric math                                         #
# --------------------------------------------------------------------------- #

def total_bytes(n):
    """Total bytes processed by a run of N iterations."""
    return n * BYTES_PER_ITER


def _get(counters, name):
    v = counters.get(name)
    return v


def compute_metrics(counters, total_bytes_val):
    """Derive per-byte and ratio metrics from a single counters dict.

    Only metrics whose required counters are present (and non-zero where used
    as a denominator) are emitted; everything else is simply absent from the
    returned dict (rendered as ``n/a`` downstream). Works for either counter
    group -- each metric depends on counters from a single group only, so no
    cross-group pairing is required.
    """
    b = float(total_bytes_val)
    m = {}

    ins = _get(counters, "instructions")
    cyc = _get(counters, "cycles")
    branches = _get(counters, "branches")
    branch_misses = _get(counters, "branch-misses")
    dloads = _get(counters, "L1-dcache-loads")
    dmiss = _get(counters, "L1-dcache-load-misses")
    imiss = _get(counters, "L1-icache-load-misses")
    itlb = _get(counters, "iTLB-load-misses")
    taskclock_ms = _get(counters, "task-clock")

    if ins is not None and b:
        m["instructions_per_byte"] = ins / b
    if cyc is not None and b:
        m["cycles_per_byte"] = cyc / b
    if ins is not None and cyc:
        m["ipc"] = ins / cyc
    if branch_misses is not None and branches:
        m["branch_miss_pct"] = 100.0 * branch_misses / branches
    if dmiss is not None and dloads:
        m["dcache_miss_pct"] = 100.0 * dmiss / dloads
    if dmiss is not None and b:
        m["dcache_misses_per_byte"] = dmiss / b
    if imiss is not None and b:
        m["icache_misses_per_byte"] = imiss / b
    if itlb is not None and b:
        m["itlb_misses_per_byte"] = itlb / b
    # Frequency-sensitive metrics (only meaningful when frequency is locked).
    if taskclock_ms and cyc is not None:
        m["ghz"] = cyc / (taskclock_ms * 1e6)
    if taskclock_ms:
        seconds = taskclock_ms / 1e3
        if seconds:
            m["throughput_gib_s"] = b / seconds / (1024 ** 3)
    return m


def mean_stddev(values):
    """Return (mean, sample_stddev) of the non-None values, or (None, None)."""
    vals = [v for v in values if v is not None]
    if not vals:
        return (None, None)
    mean = sum(vals) / len(vals)
    if len(vals) > 1:
        var = sum((v - mean) ** 2 for v in vals) / (len(vals) - 1)
        sd = math.sqrt(var)
    else:
        sd = 0.0
    return (mean, sd)


def aggregate_metric_series(metric_dicts):
    """Aggregate a list of per-round metric dicts into ``{metric: (mean, sd)}``."""
    keys = set()
    for d in metric_dicts:
        keys.update(d.keys())
    out = {}
    for k in keys:
        out[k] = mean_stddev([d.get(k) for d in metric_dicts])
    return out


# --------------------------------------------------------------------------- #
# Pure function: equal-width Markdown table formatting                        #
# --------------------------------------------------------------------------- #

def format_markdown_table(headers, rows, aligns=None):
    """Render a Markdown table where every cell in a column shares one width.

    Each column is padded to the max width of its header and data cells.
    ``aligns`` is a list of 'left' | 'right' (numeric columns use 'right').
    The alignment/separator row is padded to the identical per-column width so
    that, visually, every cell in a column is exactly equal width.
    """
    ncol = len(headers)
    if aligns is None:
        aligns = ["left"] * ncol
    if len(aligns) != ncol:
        raise ValueError("aligns length must match headers length")

    headers = [str(h) for h in headers]
    srows = [[str(c) for c in row] for row in rows]

    widths = [len(headers[i]) for i in range(ncol)]
    for row in srows:
        for i in range(ncol):
            widths[i] = max(widths[i], len(row[i]))

    def pad(s, i):
        return s.rjust(widths[i]) if aligns[i] == "right" else s.ljust(widths[i])

    def render(cells):
        return "| " + " | ".join(pad(cells[i], i) for i in range(ncol)) + " |"

    def sep_cell(i):
        w = widths[i]
        if aligns[i] == "right":
            return "-" * (w - 1) + ":" if w >= 1 else ":"
        return "-" * w

    sep = "| " + " | ".join(sep_cell(i) for i in range(ncol)) + " |"
    lines = [render(headers), sep] + [render(r) for r in srows]
    return "\n".join(lines)


def column_segment_widths(table_text):
    """Return, per column, the set of inter-pipe segment widths across all rows.

    Used by tests to assert that every cell in a column is equal width. A
    correctly formatted table yields exactly one width per column.
    """
    per_col = {}
    for line in table_text.splitlines():
        if not line.startswith("|"):
            continue
        # Strip the leading and trailing pipe, then split into cell segments.
        segments = line.split("|")[1:-1]
        for i, seg in enumerate(segments):
            per_col.setdefault(i, set()).add(len(seg))
    return per_col


# --------------------------------------------------------------------------- #
# Pure function: interleave schedule generation                               #
# --------------------------------------------------------------------------- #

def build_schedule(rounds, analyzers=ANALYZERS, variants=VARIANTS, groups=GROUPS):
    """Build the drift-cancelling interleave schedule.

    Loop order (outer -> inner): round -> group -> analyzer -> variant, with
    *variant innermost* so the three variants of a given (analyzer, group) are
    measured back-to-back, cancelling slow drift when comparing variants.

    Returns a list of cell dicts with keys: round, group, analyzer, variant,
    sha.
    """
    schedule = []
    for r in range(rounds):
        for group in groups:
            for analyzer in analyzers:
                for (variant, sha) in variants:
                    schedule.append(
                        {
                            "round": r,
                            "group": group,
                            "analyzer": analyzer,
                            "variant": variant,
                            "sha": sha,
                        }
                    )
    return schedule


# --------------------------------------------------------------------------- #
# Pure function: CLI parsing                                                   #
# --------------------------------------------------------------------------- #

def build_arg_parser():
    p = argparse.ArgumentParser(
        prog="perf_orchestrate.py",
        description="Fixed-N perf-measurement orchestrator for bufjson "
        "(3 variants x 3 analyzers).",
    )
    p.add_argument(
        "--fetch",
        action="store_true",
        help="exercise the content-fetch code path (default: no-fetch).",
    )
    p.add_argument("--n", type=int, default=DEFAULT_N,
                   help="iterations N per harness run (default: %(default)s).")
    p.add_argument("--rounds", type=int, default=DEFAULT_ROUNDS,
                   help="measured interleave rounds (default: %(default)s).")
    p.add_argument("--reps", type=int, default=DEFAULT_REPS,
                   help="perf stat -r repeats per measured cell "
                   "(default: %(default)s).")
    p.add_argument("--cpu", type=int, default=DEFAULT_CPU,
                   help="core to pin to via taskset (default: %(default)s).")
    p.add_argument("--out", default=None,
                   help="write the Markdown report to this file (also printed).")
    p.add_argument("--dry-run", action="store_true",
                   help="print the interleave schedule and exit (no build/run).")
    p.add_argument("--smoke", action="store_true",
                   help="tiny end-to-end proof: one worktree, one cell.")
    return p


def parse_cli(argv):
    return build_arg_parser().parse_args(argv)


# --------------------------------------------------------------------------- #
# Pure function: perf command builder + harness arg contract                  #
# --------------------------------------------------------------------------- #

def harness_args(analyzer, n, fetch):
    """The exact positional argument vector the harness expects."""
    return [analyzer, str(n), "fetch" if fetch else "nofetch"]


def build_perf_cmd(events, binary, analyzer, n, fetch, reps=1, cpu=3):
    """Build the `perf stat` command vector for one measured cell.

        perf stat -x, -r <reps> -e <events> -- taskset -c <cpu> \\
            <binary> <analyzer> <N> <fetch>
    """
    return (
        [
            "perf", "stat", "-x,",
            "-r", str(reps),
            "-e", ",".join(events),
            "--",
            "taskset", "-c", str(cpu),
            binary,
        ]
        + harness_args(analyzer, n, fetch)
    )


# --------------------------------------------------------------------------- #
# Root detection + frequency control (root-only, fully restorable)            #
# --------------------------------------------------------------------------- #

class Sysfs:
    """Thin, mockable wrapper over the sysfs files we touch."""

    def read(self, path):
        try:
            with open(path, "r") as f:
                return f.read().strip()
        except OSError:
            return None

    def write(self, path, value):
        try:
            with open(path, "w") as f:
                f.write(str(value))
            return True
        except OSError:
            return False

    def list_governors(self):
        import glob
        return sorted(glob.glob(GOVERNOR_GLOB))


class FreqController:
    """Locks/restores CPU frequency, but ONLY when running as root.

    Both the effective uid and the sysfs accessor are injected so the branch
    can be unit tested for root and non-root WITHOUT being root and WITHOUT
    touching real /sys files.
    """

    def __init__(self, euid, sysfs=None, log=print):
        self.euid = euid
        self.sysfs = sysfs if sysfs is not None else Sysfs()
        self.log = log
        self._saved = {}
        self.applied = False

    def is_root(self):
        return self.euid == 0

    def apply(self):
        """Lock frequency if root. Returns True iff locking was applied."""
        if not self.is_root():
            self.log(
                "NOTICE: not running as root -- skipping CPU frequency lock.\n"
                "        Proceeding with taskset core-pinning only. The reported\n"
                "        per-byte and ratio metrics (instructions/byte, "
                "cycles/byte,\n"
                "        IPC, dcache-miss%, dcache-misses/byte) are "
                "frequency-invariant\n"
                "        and therefore valid. Only absolute GHz / throughput "
                "would need\n"
                "        a locked frequency."
            )
            return False

        no_turbo = self.sysfs.read(NO_TURBO_PATH)
        if no_turbo is not None:
            self._saved[NO_TURBO_PATH] = no_turbo
            self.sysfs.write(NO_TURBO_PATH, "1")

        for gov_path in self.sysfs.list_governors():
            cur = self.sysfs.read(gov_path)
            if cur is not None:
                self._saved[gov_path] = cur
                self.sysfs.write(gov_path, "performance")

        self.applied = True
        self.log("Locked CPU frequency (turbo disabled, performance governor).")
        return True

    def restore(self):
        """Restore every saved sysfs value. Safe to call multiple times."""
        for path, value in list(self._saved.items()):
            self.sysfs.write(path, value)
        if self._saved:
            self.log("Restored original CPU frequency settings.")
        self._saved = {}
        self.applied = False


# --------------------------------------------------------------------------- #
# Formatting helpers for the report                                           #
# --------------------------------------------------------------------------- #

def fmt_mean_sd(pair, prec=4):
    mean, sd = pair
    if mean is None:
        return "n/a"
    return "{:.{p}f}\u00b1{:.{p}f}".format(mean, sd, p=prec)


def fmt_delta_pct(base_mean, other_mean):
    if base_mean is None or other_mean is None or base_mean == 0:
        return "n/a"
    return "{:+.2f}%".format(100.0 * (other_mean - base_mean) / base_mean)


def _matrix_table(agg, metric, title, prec):
    """Build a rows=analyzer x cols=variant mean+/-sd table for one metric."""
    headers = ["analyzer"] + [v for (v, _) in VARIANTS]
    aligns = ["left"] + ["right"] * len(VARIANTS)
    rows = []
    for analyzer in ANALYZERS:
        row = [analyzer]
        for (variant, _) in VARIANTS:
            pair = agg.get((analyzer, variant), {}).get(metric, (None, None))
            row.append(fmt_mean_sd(pair, prec))
        rows.append(row)
    return "#### {}\n\n{}\n".format(title, format_markdown_table(headers, rows, aligns))


def _delta_table(agg, metric, title):
    """Delta-vs-baseline % table for one metric (baseline column = 0)."""
    headers = ["analyzer"] + [v for (v, _) in VARIANTS]
    aligns = ["left"] + ["right"] * len(VARIANTS)
    base_variant = VARIANTS[0][0]
    rows = []
    for analyzer in ANALYZERS:
        base = agg.get((analyzer, base_variant), {}).get(metric, (None, None))[0]
        row = [analyzer]
        for (variant, _) in VARIANTS:
            if variant == base_variant:
                row.append("0.00% (base)")
            else:
                other = agg.get((analyzer, variant), {}).get(metric, (None, None))[0]
                row.append(fmt_delta_pct(base, other))
        rows.append(row)
    return "#### {}\n\n{}\n".format(title, format_markdown_table(headers, rows, aligns))


def build_report(agg, args, freq_locked):
    """Assemble the full Markdown report from aggregated metrics.

    ``agg`` maps (analyzer, variant) -> {metric: (mean, sd)}. Pure function.
    """
    out = []
    out.append("# bufjson fixed-N perf report\n")
    mode = "fetch" if args.fetch else "no-fetch"
    out.append(
        "N={n} iterations x {bpi} bytes/iter = {gib:.2f} GiB per run; "
        "rounds={rounds}, reps={reps}, content-fetch={mode}; "
        "pinned to core {cpu}; frequency-locked={fl}.\n".format(
            n=args.n, bpi=BYTES_PER_ITER,
            gib=total_bytes(args.n) / (1024 ** 3),
            rounds=args.rounds, reps=args.reps, mode=mode, cpu=args.cpu,
            fl=freq_locked,
        )
    )
    if not freq_locked:
        out.append(
            "> Frequency was NOT locked (not root). Per-byte and ratio metrics "
            "below are frequency-invariant and valid; absolute GHz/throughput "
            "are omitted or should be treated as indicative only.\n"
        )

    out.append("\n## Q-H1: is there more work per byte?\n")
    out.append(_matrix_table(agg, "instructions_per_byte",
                             "instructions / byte (mean\u00b1stddev)", 4))
    out.append(_delta_table(agg, "instructions_per_byte",
                            "instructions / byte: \u0394 vs baseline"))
    out.append(_matrix_table(agg, "cycles_per_byte",
                             "cycles / byte (mean\u00b1stddev)", 4))
    out.append(_matrix_table(agg, "dcache_misses_per_byte",
                             "dcache-misses / byte (mean\u00b1stddev)", 6))

    out.append("\n## Q-READ-STALLS: source of ReadAnalyzer stalls, per byte\n")
    out.append(_matrix_table(agg, "ipc", "IPC = instructions / cycle "
                             "(mean\u00b1stddev)", 4))
    out.append(_matrix_table(agg, "dcache_miss_pct",
                             "L1 dcache miss %% (mean\u00b1stddev)".replace("%%", "%"),
                             4))
    out.append(_matrix_table(agg, "dcache_misses_per_byte",
                             "dcache-misses / byte (mean\u00b1stddev)", 6))

    # Wide supporting-counter table.
    out.append("\n## Supporting per-byte counters (all analyzers x variants)\n")
    sup_metrics = [
        ("instructions_per_byte", "ins/byte", 4),
        ("cycles_per_byte", "cyc/byte", 4),
        ("ipc", "IPC", 4),
        ("branch_miss_pct", "branch-miss%", 4),
        ("dcache_miss_pct", "dcache-miss%", 4),
        ("dcache_misses_per_byte", "dcache-miss/byte", 6),
        ("icache_misses_per_byte", "icache-miss/byte", 6),
        ("itlb_misses_per_byte", "iTLB-miss/byte", 6),
    ]
    headers = ["analyzer", "variant"] + [lbl for (_, lbl, _) in sup_metrics]
    aligns = ["left", "left"] + ["right"] * len(sup_metrics)
    rows = []
    for analyzer in ANALYZERS:
        for (variant, _) in VARIANTS:
            row = [analyzer, variant]
            for (mk, _lbl, prec) in sup_metrics:
                pair = agg.get((analyzer, variant), {}).get(mk, (None, None))
                row.append(fmt_mean_sd(pair, prec))
            rows.append(row)
    out.append(format_markdown_table(headers, rows, aligns) + "\n")

    # Verdicts.
    out.append("\n## Verdicts\n")
    out.extend(_verdicts(agg))
    return "\n".join(out) + "\n"


def _verdicts(agg):
    lines = []
    base = VARIANTS[0][0]
    # H1 verdict per analyzer.
    for analyzer in ANALYZERS:
        b = agg.get((analyzer, base), {}).get("instructions_per_byte", (None, None))[0]
        parts = []
        for (variant, _) in VARIANTS[1:]:
            o = agg.get((analyzer, variant), {}).get(
                "instructions_per_byte", (None, None))[0]
            parts.append("{}={}".format(variant, fmt_delta_pct(b, o)))
        lines.append("- **H1 [{}]**: instructions/byte vs baseline -> {}".format(
            analyzer, ", ".join(parts) if parts else "n/a"))
    # Read-stalls verdict: compare read vs fixed/pipe on dcache-miss% and IPC.
    def g(analyzer, metric):
        return agg.get((analyzer, base), {}).get(metric, (None, None))[0]
    lines.append(
        "- **READ-STALLS**: on baseline, dcache-miss% "
        "fixed={} pipe={} read={}; IPC fixed={} pipe={} read={}. "
        "Higher read dcache-miss% with lower read IPC would localize the "
        "stalls to L1-dcache pressure per byte.".format(
            _fmt1(g("fixed", "dcache_miss_pct")),
            _fmt1(g("pipe", "dcache_miss_pct")),
            _fmt1(g("read", "dcache_miss_pct")),
            _fmt1(g("fixed", "ipc")),
            _fmt1(g("pipe", "ipc")),
            _fmt1(g("read", "ipc")),
        )
    )
    return lines


def _fmt1(v):
    return "n/a" if v is None else "{:.4f}".format(v)


# --------------------------------------------------------------------------- #
# Privilege drop for child processes (pure, mockable; used under sudo)        #
# --------------------------------------------------------------------------- #
#
# Only the sysfs frequency-lock (FreqController, which uses open() directly)
# needs to run as root. EVERY other child -- git, cargo, perf, the harness
# binary -- must run as the ORIGINAL invoking user when we were launched via
# sudo. Otherwise:
#   * cargo is a rustup shim that needs the user's HOME/CARGO_HOME/RUSTUP_HOME
#     to resolve the toolchain (and root's scrubbed PATH lacks ~/.cargo/bin,
#     which is the FileNotFoundError: 'cargo' symptom), and
#   * building/gitting as root would litter root-owned files into the user's
#     ~/.cargo caches and the repo's .git/worktrees.
#
# The decision + env reconstruction is kept in the PURE function
# ``compute_privilege_context`` so it can be unit tested with no root and no
# child spawn. The impure ``install_privilege_context`` wires it to the live
# process and handles the "real root, no sudo" error path.


class PrivilegeError(RuntimeError):
    """Raised when running as real root (euid 0) without sudo context."""


# Module-global holding the active privilege context (set by
# install_privilege_context). None means "not yet computed / no drop".
_PRIV_CTX = None


def user_cargo_bin(home):
    """The invoking user's rustup/cargo shim directory."""
    return os.path.join(home, ".cargo", "bin")


def build_child_env(base_environ, home, user):
    """Reconstruct a child environment for the invoking user (pure).

    Starts from a copy of ``base_environ`` (so TERM/LANG/etc. are preserved),
    then:
      * HOME/USER/LOGNAME are pointed at the invoking user, so a rustup ``cargo``
        shim resolves the toolchain and writes caches under the user's HOME.
      * ~/.cargo/bin is prepended to PATH so the shim is found even though sudo
        scrubbed it from PATH.
      * CARGO_HOME / RUSTUP_HOME are passed through untouched if present (they
        ride along in ``base_environ``); if absent they are left unset so cargo
        defaults to ~/.cargo and ~/.rustup under the now-correct HOME.
      * sudo bookkeeping vars are removed so children see a clean, self-
        consistent (non-root) environment.
    """
    env = dict(base_environ)
    env["HOME"] = home
    env["USER"] = user
    env["LOGNAME"] = user

    cargo_bin = user_cargo_bin(home)
    path = env.get("PATH", "")
    parts = path.split(os.pathsep) if path else []
    if cargo_bin not in parts:
        parts.insert(0, cargo_bin)
    env["PATH"] = os.pathsep.join(parts)

    for k in ("SUDO_USER", "SUDO_UID", "SUDO_GID", "SUDO_COMMAND"):
        env.pop(k, None)
    return env


def compute_privilege_context(euid, environ, getpwnam=pwd.getpwnam):
    """Decide whether/how to drop privileges for child processes (pure).

    Returns a dict:
      * ``{"drop": False}`` when euid != 0 -- normal user, no change at all
        (this preserves the pre-existing non-root code path EXACTLY).
      * ``{"drop": True, "user", "uid", "gid", "home", "env"}`` when euid == 0
        and SUDO_USER is set (launched via sudo). uid/gid/home come from the
        passwd database (authoritative; SUDO_UID/SUDO_GID agree with these),
        and ``env`` is the reconstructed child environment.

    Raises ``PrivilegeError`` when euid == 0 but SUDO_USER is unset (someone is
    logged in as real root, not via sudo): we refuse to build as root rather
    than crash or create root-owned artifacts.

    ``getpwnam`` is injectable so tests need not touch the real passwd db.
    """
    if euid != 0:
        return {"drop": False}

    sudo_user = environ.get("SUDO_USER")
    if not sudo_user:
        raise PrivilegeError(
            "running as real root without sudo (euid=0, SUDO_USER unset): "
            "refusing to build/run the toolchain as root. Doing so would fail "
            "to resolve the rustup toolchain and would create root-owned files "
            "in ~/.cargo and the repo's .git/worktrees. Re-run via "
            "'sudo ./perf_orchestrate.py' from your normal user so the invoking "
            "user (SUDO_USER) can be recovered for git/cargo/perf/harness.")

    try:
        pw = getpwnam(sudo_user)
    except KeyError as e:
        raise PrivilegeError(
            "SUDO_USER={!r} is not a known user in the passwd database "
            "({}).".format(sudo_user, e))

    home = pw.pw_dir
    return {
        "drop": True,
        "user": sudo_user,
        "uid": pw.pw_uid,
        "gid": pw.pw_gid,
        "home": home,
        "env": build_child_env(environ, home, sudo_user),
    }


def privilege_kwargs(ctx=None):
    """Return subprocess.run/Popen kwargs implementing the privilege drop.

    ``{}`` when no drop is required (non-root path -> children inherit the
    current env and identity, exactly as before). Otherwise ``user=``,
    ``group=`` and the reconstructed ``env=`` so the child runs as the invoking
    user with a toolchain-resolving environment. Pure w.r.t. its ``ctx`` arg;
    falls back to the module-global installed context when ``ctx`` is None.
    """
    if ctx is None:
        ctx = _PRIV_CTX
    if not ctx or not ctx.get("drop"):
        return {}
    return {"user": ctx["uid"], "group": ctx["gid"], "env": ctx["env"]}


def install_privilege_context():
    """Compute and install the global privilege context (impure).

    On the "real root without sudo" edge case, prints a clear, actionable error
    and exits non-zero rather than proceeding to build as root. Returns the
    context dict on success.
    """
    global _PRIV_CTX
    try:
        ctx = compute_privilege_context(os.geteuid(), os.environ)
    except PrivilegeError as e:
        print("ERROR: {}".format(e), file=sys.stderr)
        sys.exit(2)
    _PRIV_CTX = ctx
    if ctx.get("drop"):
        print("Running as root via sudo: keeping only the CPU frequency lock "
              "privileged; dropping to user '{}' (uid={}, gid={}) for "
              "git/cargo/perf/harness.".format(
                  ctx["user"], ctx["uid"], ctx["gid"]))
    return ctx


# --------------------------------------------------------------------------- #
# Subprocess helpers (impure; thin wrappers around git/cargo/perf)            #
# --------------------------------------------------------------------------- #

def _spawn(cmd, **kwargs):
    """subprocess.run wrapper that drops privileges to the invoking user when
    running as root via sudo. Applies user/group/env from the installed
    privilege context without clobbering any kwargs the caller set explicitly.
    """
    for k, v in privilege_kwargs().items():
        kwargs.setdefault(k, v)
    return subprocess.run(cmd, **kwargs)


def _run(cmd, cwd=None, check=True):
    proc = _spawn(cmd, cwd=cwd, stdout=subprocess.PIPE,
                  stderr=subprocess.PIPE, text=True)
    if check and proc.returncode != 0:
        raise RuntimeError(
            "command failed ({}): {}\nstdout:\n{}\nstderr:\n{}".format(
                proc.returncode, " ".join(cmd), proc.stdout, proc.stderr))
    return proc


def repo_root():
    proc = _run(["git", "rev-parse", "--show-toplevel"])
    return proc.stdout.strip()


def probe_perf_events(events, cpu=DEFAULT_CPU):
    """Probe each event by running perf on `true`; return (supported, unsupp)."""
    outputs = {}
    for ev in events:
        proc = _spawn(
            ["perf", "stat", "-x,", "-e", ev, "--", "true"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        outputs[ev] = proc.stderr
    return filter_supported(events, outputs)


def create_worktree(root, base_dir, sha):
    wt = os.path.join(base_dir, "wt_" + sha)
    _run(["git", "worktree", "add", "--detach", wt, sha], cwd=root)
    # Inject the harness (examples/ is auto-discovered by Cargo).
    ex_dir = os.path.join(wt, "examples")
    os.makedirs(ex_dir, exist_ok=True)
    with open(os.path.join(ex_dir, "perf_harness.rs"), "w") as f:
        f.write(HARNESS_SRC)
    return wt


def build_harness(wt):
    # Per-worktree default target dir (do NOT set CARGO_TARGET_DIR).
    _run(["cargo", "build", "--release", "--example", "perf_harness"], cwd=wt)
    return os.path.join(wt, "target", "release", "examples", "perf_harness")


def remove_worktree(root, wt):
    _spawn(["git", "worktree", "remove", "--force", wt], cwd=root,
           stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)


# --------------------------------------------------------------------------- #
# Orchestration driver                                                        #
# --------------------------------------------------------------------------- #

def run_full(args):
    ctx = install_privilege_context()
    root = repo_root()
    freq = FreqController(os.geteuid())

    base_dir = tempfile.mkdtemp(prefix="bufjson_perf_")
    # When dropping privileges, hand the scratch dir (and thus every worktree
    # and cargo target dir created inside it) to the invoking user so the
    # dropped git/cargo children can write and NO root-owned files remain.
    if ctx.get("drop"):
        os.chown(base_dir, ctx["uid"], ctx["gid"])
    worktrees = {}

    def cleanup():
        for wt in list(worktrees.values()):
            remove_worktree(root, wt)
        worktrees.clear()
        _spawn(["git", "worktree", "prune"], cwd=root,
               stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        shutil.rmtree(base_dir, ignore_errors=True)
        freq.restore()

    atexit.register(cleanup)

    try:
        freq_locked = freq.apply()

        # Probe counters once; degrade unsupported to n/a.
        all_events = sorted(set(GROUP_EVENTS["A"]) | set(GROUP_EVENTS["B"]))
        supported, unsupported = probe_perf_events(all_events, args.cpu)
        if unsupported:
            print("NOTICE: unsupported counters degraded to n/a: {}".format(
                ", ".join(unsupported)))
        group_events = {
            g: [e for e in GROUP_EVENTS[g] if e in supported] for g in GROUPS
        }

        # Build all worktrees.
        binaries = {}
        for (variant, sha) in VARIANTS:
            print("Preparing worktree for {} ({}) ...".format(variant, sha))
            wt = create_worktree(root, base_dir, sha)
            worktrees[variant] = wt
            binaries[variant] = build_harness(wt)

        # Interleaved measurement.
        schedule = build_schedule(args.rounds)
        # counters[(group, analyzer, variant)] -> list of per-round dicts
        counters = {}
        total = len(schedule)
        for i, cell in enumerate(schedule, 1):
            g, a, v = cell["group"], cell["analyzer"], cell["variant"]
            evs = group_events[g]
            binary = binaries[v]
            if not evs:
                continue
            # Throwaway warm-up run (discarded) before each measured perf stat.
            _spawn([binary] + harness_args(a, args.n, args.fetch),
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            cmd = build_perf_cmd(evs, binary, a, args.n, args.fetch,
                                 reps=args.reps, cpu=args.cpu)
            proc = _spawn(cmd, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, text=True)
            parsed = parse_perf_stat(proc.stderr)
            counters.setdefault((g, a, v), []).append(parsed)
            print("  [{}/{}] round {} group {} {:<5} {:<8} done".format(
                i, total, cell["round"], g, a, v))

        agg = _aggregate_all(counters, args.n)
        report = build_report(agg, args, freq_locked)
        print("\n" + report)
        if args.out:
            with open(args.out, "w") as f:
                f.write(report)
            print("Report written to {}".format(args.out))
    finally:
        cleanup()
        atexit.unregister(cleanup)


def _aggregate_all(counters, n):
    """counters[(group,analyzer,variant)] -> agg[(analyzer,variant)]{metric:(m,sd)}."""
    tb = total_bytes(n)
    # For each (analyzer,variant), gather per-round metric dicts from both groups.
    by_av = {}
    for (g, a, v), round_dicts in counters.items():
        per_round_metrics = [compute_metrics(d, tb) for d in round_dicts]
        by_av.setdefault((a, v), []).extend(per_round_metrics)
    agg = {}
    for (a, v), metric_dicts in by_av.items():
        agg[(a, v)] = aggregate_metric_series(metric_dicts)
    return agg


def run_dry(args):
    schedule = build_schedule(args.rounds)
    print("Interleave schedule ({} cells; order round->group->analyzer->"
          "variant, variant innermost):".format(len(schedule)))
    for i, c in enumerate(schedule):
        print("  {:4d}  round={} group={} analyzer={:<5} variant={:<8} sha={}"
              .format(i, c["round"], c["group"], c["analyzer"], c["variant"],
                      c["sha"]))


def run_smoke(args):
    """Tiny end-to-end proof: one worktree (baseline), one cell, tiny N."""
    ctx = install_privilege_context()
    root = repo_root()
    base_dir = tempfile.mkdtemp(prefix="bufjson_smoke_")
    if ctx.get("drop"):
        os.chown(base_dir, ctx["uid"], ctx["gid"])
    wt = None

    def cleanup():
        if wt is not None:
            remove_worktree(root, wt)
        _spawn(["git", "worktree", "prune"], cwd=root,
               stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        shutil.rmtree(base_dir, ignore_errors=True)

    atexit.register(cleanup)
    try:
        variant, sha = VARIANTS[0]
        print("[smoke] worktree {} ({}) in {}".format(variant, sha, base_dir))
        wt = create_worktree(root, base_dir, sha)
        binary = build_harness(wt)
        print("[smoke] built: {}".format(binary))

        # Prove the harness itself runs and exits 0 (no perf, no root).
        n = 3
        rc = _spawn([binary] + harness_args("fixed", n, args.fetch)).returncode
        assert rc == 0, "harness exit {}".format(rc)
        print("[smoke] harness fixed N={} exit 0 OK".format(n))

        # Now attempt one real perf-measured cell end-to-end.
        supported, unsupported = probe_perf_events(GROUP_EVENTS["A"], args.cpu)
        if not supported or "instructions" not in supported:
            print("[smoke] perf counters unavailable ({} unsupported) -- "
                  "skipping perf leg gracefully.".format(unsupported))
            return
        cmd = build_perf_cmd(supported, binary, "fixed", n, args.fetch,
                             reps=1, cpu=args.cpu)
        print("[smoke] running: {}".format(" ".join(cmd)))
        proc = _spawn(cmd, stdout=subprocess.PIPE,
                      stderr=subprocess.PIPE, text=True)
        if proc.returncode != 0:
            print("[smoke] perf returned {} -- perf may be restricted here; "
                  "skipping gracefully.\nstderr:\n{}".format(
                      proc.returncode, proc.stderr))
            return
        parsed = parse_perf_stat(proc.stderr)
        metrics = compute_metrics(parsed, total_bytes(n))
        agg = {("fixed", variant): aggregate_metric_series([metrics])}
        table = _matrix_table(agg, "instructions_per_byte",
                              "SMOKE instructions/byte", 4)
        print("[smoke] parsed counters: {}".format(parsed))
        print("[smoke] table:\n" + table)
        print("[smoke] END-TO-END OK (build+perf+parse+table).")
    finally:
        cleanup()
        atexit.unregister(cleanup)


def main(argv=None):
    args = parse_cli(sys.argv[1:] if argv is None else argv)
    if args.dry_run:
        run_dry(args)
        return 0
    if args.smoke:
        run_smoke(args)
        return 0
    run_full(args)
    return 0


if __name__ == "__main__":
    sys.exit(main())
