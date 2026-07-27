#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Unit tests for perf_orchestrate.py.

All tests are pure: NO root, NO /sys access, NO cargo/perf/git invocation, NO
benchmark run. Run with:  python3 -m pytest test_perf_orchestrate.py -v
(or plain `python3 test_perf_orchestrate.py` via the unittest fallback at the
bottom if pytest is unavailable).
"""

import unittest

import perf_orchestrate as po


# --------------------------------------------------------------------------- #
# Realistic perf stat -x, fixtures                                            #
# --------------------------------------------------------------------------- #

# GroupA style output (task-clock in msec, cycles/instructions/branches/misses).
PERF_GROUP_A = """\
1234.567890,msec,task-clock,1234567890,100.00,0.999,CPUs utilized
4500000000,,cycles,1234567890,100.00,3.646,GHz
9000000000,,instructions,1234567890,100.00,2.00,insn per cycle
1000000000,,branches,1234567890,100.00,810.234,M/sec
10000000,,branch-misses,1234567890,100.00,1.00,of all branches
"""

# GroupB style output with one UNSUPPORTED counter to exercise degradation.
PERF_GROUP_B = """\
9000000000,,instructions,1234567890,100.00,0.0,
50000000,,L1-icache-load-misses,1234567890,100.00,0.0,
<not supported>,,iTLB-load-misses,,,,
2000000000,,L1-dcache-loads,1234567890,100.00,0.0,
40000000,,L1-dcache-load-misses,1234567890,100.00,2.00,of all L1-dcache accesses
"""

# A probe of a single supported / unsupported event against `true`.
PROBE_OK = "0,,instructions,1000,100.00,,\n"
PROBE_UNSUPPORTED = "<not supported>,,stalled-cycles-frontend,,,,\n"


class TestPerfParsing(unittest.TestCase):
    def test_parse_group_a(self):
        c = po.parse_perf_stat(PERF_GROUP_A)
        self.assertAlmostEqual(c["task-clock"], 1234.567890)
        self.assertEqual(c["cycles"], 4500000000.0)
        self.assertEqual(c["instructions"], 9000000000.0)
        self.assertEqual(c["branches"], 1000000000.0)
        self.assertEqual(c["branch-misses"], 10000000.0)

    def test_parse_unsupported_becomes_none(self):
        c = po.parse_perf_stat(PERF_GROUP_B)
        self.assertIsNone(c["iTLB-load-misses"])
        self.assertEqual(c["L1-dcache-loads"], 2000000000.0)
        self.assertEqual(c["L1-dcache-load-misses"], 40000000.0)

    def test_parse_ignores_blank_and_comment_lines(self):
        text = "# a comment\n\n" + PERF_GROUP_A + "\n# trailing\n"
        c = po.parse_perf_stat(text)
        self.assertIn("cycles", c)
        self.assertEqual(len(c), 5)

    def test_event_status(self):
        self.assertEqual(po.event_status(PROBE_OK, "instructions"), "ok")
        self.assertEqual(
            po.event_status(PROBE_UNSUPPORTED, "stalled-cycles-frontend"),
            "not-supported")
        self.assertEqual(po.event_status(PROBE_OK, "cycles"), "missing")

    def test_filter_supported(self):
        probes = {
            "instructions": PROBE_OK,
            "stalled-cycles-frontend": PROBE_UNSUPPORTED,
        }
        sup, unsup = po.filter_supported(
            ["instructions", "stalled-cycles-frontend"], probes)
        self.assertEqual(sup, ["instructions"])
        self.assertEqual(unsup, ["stalled-cycles-frontend"])


class TestMetricMath(unittest.TestCase):
    def test_total_bytes(self):
        self.assertEqual(po.total_bytes(1), 204800)
        self.assertEqual(po.total_bytes(20000), 20000 * 204800)

    def test_known_per_byte_math(self):
        # Choose counters so ratios are exact and hand-checkable.
        b = 1000  # bytes
        counters = {
            "instructions": 8000.0,   # 8 ins/byte
            "cycles": 4000.0,         # 4 cyc/byte, IPC = 2.0
            "branches": 2000.0,
            "branch-misses": 40.0,    # 2% branch miss
            "L1-dcache-loads": 1000.0,
            "L1-dcache-load-misses": 50.0,  # 5% dcache miss, 0.05/byte
            "L1-icache-load-misses": 10.0,  # 0.01/byte
            "iTLB-load-misses": 5.0,        # 0.005/byte
            "task-clock": 2.0,        # msec => 0.002 s
        }
        m = po.compute_metrics(counters, b)
        self.assertAlmostEqual(m["instructions_per_byte"], 8.0)
        self.assertAlmostEqual(m["cycles_per_byte"], 4.0)
        self.assertAlmostEqual(m["ipc"], 2.0)
        self.assertAlmostEqual(m["branch_miss_pct"], 2.0)
        self.assertAlmostEqual(m["dcache_miss_pct"], 5.0)
        self.assertAlmostEqual(m["dcache_misses_per_byte"], 0.05)
        self.assertAlmostEqual(m["icache_misses_per_byte"], 0.01)
        self.assertAlmostEqual(m["itlb_misses_per_byte"], 0.005)
        # GHz = cycles / (task_clock_ms * 1e6) = 4000 / 2e6 = 0.002
        self.assertAlmostEqual(m["ghz"], 0.002)

    def test_missing_counters_omit_metrics(self):
        m = po.compute_metrics({"instructions": 100.0}, 100)
        self.assertIn("instructions_per_byte", m)
        self.assertNotIn("ipc", m)          # no cycles
        self.assertNotIn("dcache_miss_pct", m)

    def test_zero_denominator_guarded(self):
        # cycles == 0 must not raise and must not emit IPC.
        m = po.compute_metrics({"instructions": 5.0, "cycles": 0.0}, 100)
        self.assertNotIn("ipc", m)

    def test_none_counter_skipped(self):
        m = po.compute_metrics(
            {"instructions": 100.0, "cycles": None}, 100)
        self.assertNotIn("cycles_per_byte", m)
        self.assertNotIn("ipc", m)

    def test_mean_stddev(self):
        mean, sd = po.mean_stddev([2.0, 4.0, 4.0, 4.0, 5.0, 5.0, 7.0, 9.0])
        self.assertAlmostEqual(mean, 5.0)
        self.assertAlmostEqual(sd, 2.138089935299395)  # sample stddev

    def test_mean_stddev_single_and_empty(self):
        self.assertEqual(po.mean_stddev([3.0]), (3.0, 0.0))
        self.assertEqual(po.mean_stddev([]), (None, None))
        self.assertEqual(po.mean_stddev([None, None]), (None, None))

    def test_aggregate_metric_series(self):
        series = [
            {"instructions_per_byte": 8.0, "ipc": 2.0},
            {"instructions_per_byte": 10.0, "ipc": 2.0},
        ]
        agg = po.aggregate_metric_series(series)
        self.assertAlmostEqual(agg["instructions_per_byte"][0], 9.0)
        self.assertAlmostEqual(agg["ipc"][0], 2.0)
        self.assertAlmostEqual(agg["ipc"][1], 0.0)


class TestTableFormatting(unittest.TestCase):
    def _assert_equal_width_columns(self, table):
        per_col = po.column_segment_widths(table)
        self.assertTrue(per_col)
        for col, widths in per_col.items():
            self.assertEqual(
                len(widths), 1,
                "column {} has unequal cell widths: {}".format(col, widths))

    def test_equal_width_simple(self):
        headers = ["analyzer", "baseline", "branchy", "simple"]
        rows = [
            ["fixed", "8.1234\u00b10.0100", "8.20\u00b10.02", "8.0\u00b10.0"],
            ["read", "9.9999\u00b10.5000", "10.00\u00b10.10", "9.5\u00b10.3"],
        ]
        aligns = ["left", "right", "right", "right"]
        table = po.format_markdown_table(headers, rows, aligns)
        self._assert_equal_width_columns(table)

    def test_equal_width_with_report_tables(self):
        # Build a real matrix table via the report helper and verify widths.
        agg = {}
        for a in po.ANALYZERS:
            for (v, _) in po.VARIANTS:
                agg[(a, v)] = {"instructions_per_byte": (8.123456, 0.01)}
        table = po._matrix_table(
            agg, "instructions_per_byte", "ins/byte", 4)
        self._assert_equal_width_columns(table)

    def test_delta_table_equal_width(self):
        agg = {}
        for a in po.ANALYZERS:
            agg[(a, "baseline")] = {"instructions_per_byte": (8.0, 0.0)}
            agg[(a, "branchy")] = {"instructions_per_byte": (8.4, 0.0)}
            agg[(a, "simple")] = {"instructions_per_byte": (7.6, 0.0)}
        table = po._delta_table(agg, "instructions_per_byte", "delta")
        self._assert_equal_width_columns(table)

    def test_column_width_is_max_cell(self):
        headers = ["h", "value"]
        rows = [["x", "1234567"], ["y", "9"]]
        table = po.format_markdown_table(headers, rows, ["left", "right"])
        per_col = po.column_segment_widths(table)
        # col 1 width = max(len('value')=5, len('1234567')=7) = 7; segment
        # includes one leading + one trailing space => 9.
        self.assertEqual(per_col[1], {9})

    def test_na_rendering(self):
        self.assertEqual(po.fmt_mean_sd((None, None)), "n/a")
        self.assertEqual(po.fmt_mean_sd((1.5, 0.25), prec=2), "1.50\u00b10.25")


class TestSchedule(unittest.TestCase):
    def test_single_round_order_variant_innermost(self):
        sched = po.build_schedule(1)
        seq = [(c["group"], c["analyzer"], c["variant"]) for c in sched]
        expected = []
        for g in po.GROUPS:
            for a in po.ANALYZERS:
                for (v, _) in po.VARIANTS:
                    expected.append((g, a, v))
        self.assertEqual(seq, expected)

    def test_variant_is_innermost(self):
        # Consecutive cells within a (group,analyzer) block differ only by
        # variant, and cycle through all variants in order.
        sched = po.build_schedule(1)
        variants = [v for (v, _) in po.VARIANTS]
        for i in range(0, len(sched), len(variants)):
            block = sched[i:i + len(variants)]
            self.assertEqual([c["variant"] for c in block], variants)
            # group + analyzer constant within the block.
            self.assertEqual(len({c["group"] for c in block}), 1)
            self.assertEqual(len({c["analyzer"] for c in block}), 1)

    def test_round_count_and_size(self):
        rounds = 6
        sched = po.build_schedule(rounds)
        cells_per_round = len(po.GROUPS) * len(po.ANALYZERS) * len(po.VARIANTS)
        self.assertEqual(len(sched), rounds * cells_per_round)
        self.assertEqual(sorted({c["round"] for c in sched}),
                         list(range(rounds)))

    def test_sha_mapping(self):
        sched = po.build_schedule(1)
        mapping = {c["variant"]: c["sha"] for c in sched}
        self.assertEqual(mapping,
                         {"baseline": "eeab453", "branchy": "4e6af3a",
                          "simple": "26fa6b9"})


class TestPerfCommandAndArgs(unittest.TestCase):
    def test_harness_args(self):
        self.assertEqual(po.harness_args("fixed", 20000, False),
                         ["fixed", "20000", "nofetch"])
        self.assertEqual(po.harness_args("read", 5, True),
                         ["read", "5", "fetch"])

    def test_build_perf_cmd_structure(self):
        cmd = po.build_perf_cmd(
            ["cycles", "instructions"], "/tmp/bin", "pipe", 100, True,
            reps=6, cpu=3)
        self.assertEqual(
            cmd,
            ["perf", "stat", "-x,", "-r", "6", "-e", "cycles,instructions",
             "--", "taskset", "-c", "3", "/tmp/bin", "pipe", "100", "fetch"])

    def test_build_perf_cmd_nofetch_default_cpu(self):
        cmd = po.build_perf_cmd(["cycles"], "b", "fixed", 1, False)
        self.assertIn("nofetch", cmd)
        self.assertEqual(cmd[cmd.index("-c") + 1], "3")  # default cpu


class TestCliParsing(unittest.TestCase):
    def test_defaults(self):
        a = po.parse_cli([])
        self.assertFalse(a.fetch)
        self.assertEqual(a.n, po.DEFAULT_N)
        self.assertEqual(a.rounds, po.DEFAULT_ROUNDS)
        self.assertEqual(a.reps, po.DEFAULT_REPS)
        self.assertEqual(a.cpu, po.DEFAULT_CPU)
        self.assertFalse(a.dry_run)
        self.assertFalse(a.smoke)

    def test_fetch_flag_and_overrides(self):
        a = po.parse_cli(["--fetch", "--n", "5000", "--rounds", "3",
                          "--reps", "2", "--cpu", "1"])
        self.assertTrue(a.fetch)
        self.assertEqual(a.n, 5000)
        self.assertEqual(a.rounds, 3)
        self.assertEqual(a.reps, 2)
        self.assertEqual(a.cpu, 1)

    def test_dry_run_and_smoke_flags(self):
        self.assertTrue(po.parse_cli(["--dry-run"]).dry_run)
        self.assertTrue(po.parse_cli(["--smoke"]).smoke)


# --------------------------------------------------------------------------- #
# Root detection + frequency control -- mocked, never real root, never /sys   #
# --------------------------------------------------------------------------- #

class FakeSysfs:
    """In-memory sysfs stand-in; records writes, never touches disk."""

    def __init__(self, files, governors):
        self._files = dict(files)          # path -> current value
        self._governors = list(governors)  # governor paths
        self.writes = []                   # (path, value) in order

    def read(self, path):
        return self._files.get(path)

    def write(self, path, value):
        self._files[path] = str(value)
        self.writes.append((path, str(value)))
        return True

    def list_governors(self):
        return list(self._governors)


class TestFreqController(unittest.TestCase):
    def _fake(self):
        govs = [
            "/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor",
            "/sys/devices/system/cpu/cpu1/cpufreq/scaling_governor",
        ]
        files = {
            po.NO_TURBO_PATH: "0",
            govs[0]: "powersave",
            govs[1]: "schedutil",
        }
        return FakeSysfs(files, govs), govs

    def test_non_root_does_nothing_and_notifies(self):
        sysfs, _ = self._fake()
        msgs = []
        fc = po.FreqController(euid=1000, sysfs=sysfs, log=msgs.append)
        applied = fc.apply()
        self.assertFalse(applied)
        self.assertFalse(fc.applied)
        self.assertEqual(sysfs.writes, [])       # NOTHING written to /sys
        self.assertTrue(any("not running as root" in m for m in msgs))
        # restore is a no-op when nothing saved.
        fc.restore()
        self.assertEqual(sysfs.writes, [])

    def test_root_locks_and_restores(self):
        sysfs, govs = self._fake()
        fc = po.FreqController(euid=0, sysfs=sysfs, log=lambda *_: None)
        applied = fc.apply()
        self.assertTrue(applied)
        self.assertTrue(fc.applied)
        # Turbo disabled + performance governor set on every core.
        self.assertEqual(sysfs.read(po.NO_TURBO_PATH), "1")
        for g in govs:
            self.assertEqual(sysfs.read(g), "performance")
        # Now restore original values.
        fc.restore()
        self.assertEqual(sysfs.read(po.NO_TURBO_PATH), "0")
        self.assertEqual(sysfs.read(govs[0]), "powersave")
        self.assertEqual(sysfs.read(govs[1]), "schedutil")
        self.assertFalse(fc.applied)

    def test_root_missing_no_turbo_still_handles_governors(self):
        govs = ["/sys/devices/system/cpu/cpu0/cpufreq/scaling_governor"]
        sysfs = FakeSysfs({govs[0]: "ondemand"}, govs)  # no no_turbo file
        fc = po.FreqController(euid=0, sysfs=sysfs, log=lambda *_: None)
        fc.apply()
        self.assertEqual(sysfs.read(govs[0]), "performance")
        # no_turbo absent => not written.
        self.assertNotIn(po.NO_TURBO_PATH, dict(sysfs.writes))
        fc.restore()
        self.assertEqual(sysfs.read(govs[0]), "ondemand")

    def test_is_root_via_injected_euid(self):
        self.assertTrue(po.FreqController(euid=0, sysfs=FakeSysfs({}, [])).is_root())
        self.assertFalse(
            po.FreqController(euid=1000, sysfs=FakeSysfs({}, [])).is_root())


class TestReportAssembly(unittest.TestCase):
    def _fake_agg(self):
        agg = {}
        vals = {"baseline": 8.0, "branchy": 8.5, "simple": 7.5}
        for a in po.ANALYZERS:
            for (v, _) in po.VARIANTS:
                agg[(a, v)] = {
                    "instructions_per_byte": (vals[v], 0.01),
                    "cycles_per_byte": (vals[v] * 0.5, 0.01),
                    "ipc": (2.0, 0.0),
                    "dcache_miss_pct": (3.0, 0.1),
                    "dcache_misses_per_byte": (0.0005, 0.00001),
                    "branch_miss_pct": (1.0, 0.0),
                    "icache_misses_per_byte": (0.0001, 0.0),
                    "itlb_misses_per_byte": (0.00001, 0.0),
                }
        return agg

    def test_build_report_contains_all_sections_and_valid_tables(self):
        class A:
            fetch = False
            n = 20000
            rounds = 6
            reps = 1
            cpu = 3
        report = po.build_report(self._fake_agg(), A(), freq_locked=False)
        for needle in ["Q-H1", "Q-READ-STALLS", "instructions / byte",
                       "IPC", "Supporting per-byte counters", "Verdicts",
                       "\u0394 vs baseline"]:
            self.assertIn(needle, report)
        # Every markdown table in the report has equal-width columns.
        blocks = report.split("\n\n")
        checked = 0
        for line in report.splitlines():
            pass
        # Validate each contiguous table region.
        per_col = po.column_segment_widths(report)
        # column_segment_widths across the WHOLE report mixes tables of
        # different shapes, so instead validate each table block individually.
        for block in report.split("\n\n"):
            if block.lstrip().startswith("|"):
                widths = po.column_segment_widths(block)
                for col, w in widths.items():
                    self.assertEqual(len(w), 1,
                                     "unequal col {} in block:\n{}".format(col, block))
                checked += 1
        self.assertGreater(checked, 0)

    def test_aggregate_all_end_to_end(self):
        # Simulate two rounds of GroupA + GroupB counters for one cell.
        counters = {
            ("A", "fixed", "baseline"): [
                {"instructions": 1638400.0, "cycles": 819200.0,
                 "branches": 200000.0, "branch-misses": 2000.0,
                 "task-clock": 1.0},
                {"instructions": 1638400.0, "cycles": 819200.0,
                 "branches": 200000.0, "branch-misses": 2000.0,
                 "task-clock": 1.0},
            ],
            ("B", "fixed", "baseline"): [
                {"instructions": 1638400.0, "L1-dcache-loads": 400000.0,
                 "L1-dcache-load-misses": 4000.0,
                 "L1-icache-load-misses": 800.0, "iTLB-load-misses": 40.0},
            ],
        }
        agg = po._aggregate_all(counters, n=8)  # total_bytes = 8*204800
        tb = po.total_bytes(8)
        self.assertAlmostEqual(
            agg[("fixed", "baseline")]["instructions_per_byte"][0],
            1638400.0 / tb)
        self.assertAlmostEqual(
            agg[("fixed", "baseline")]["ipc"][0], 2.0)
        self.assertAlmostEqual(
            agg[("fixed", "baseline")]["dcache_miss_pct"][0], 1.0)


# --------------------------------------------------------------------------- #
# Privilege drop under sudo -- pure/mocked, never real root, never spawns      #
# --------------------------------------------------------------------------- #

class FakePwEntry:
    """Minimal stand-in for a pwd.struct_passwd."""

    def __init__(self, name, uid, gid, home):
        self.pw_name = name
        self.pw_uid = uid
        self.pw_gid = gid
        self.pw_dir = home


def _fake_getpwnam(name):
    if name == "schapper":
        return FakePwEntry("schapper", 1000, 2000,
                           "/home/ANT.AMAZON.COM/schapper")
    raise KeyError(name)


class TestPrivilegeContext(unittest.TestCase):
    def test_non_root_never_drops(self):
        # euid != 0 -> the existing non-root code path is preserved EXACTLY.
        ctx = po.compute_privilege_context(1000, {}, getpwnam=_fake_getpwnam)
        self.assertEqual(ctx, {"drop": False})
        self.assertEqual(po.privilege_kwargs(ctx), {})

    def test_root_via_sudo_resolves_user_group_and_env(self):
        environ = {
            "SUDO_USER": "schapper",
            "SUDO_UID": "1000",
            "SUDO_GID": "2000",
            "SUDO_COMMAND": "/usr/bin/whatever",
            "HOME": "/root",
            "PATH": "/usr/sbin:/usr/bin:/sbin:/bin",
            "TERM": "xterm",
        }
        ctx = po.compute_privilege_context(0, environ, getpwnam=_fake_getpwnam)
        self.assertTrue(ctx["drop"])
        self.assertEqual(ctx["user"], "schapper")
        self.assertEqual(ctx["uid"], 1000)
        self.assertEqual(ctx["gid"], 2000)
        self.assertEqual(ctx["home"], "/home/ANT.AMAZON.COM/schapper")

        env = ctx["env"]
        # HOME points at the invoking user (NOT /root) so rustup resolves.
        self.assertEqual(env["HOME"], "/home/ANT.AMAZON.COM/schapper")
        self.assertEqual(env["USER"], "schapper")
        self.assertEqual(env["LOGNAME"], "schapper")
        # ~/.cargo/bin is prepended to PATH (the cargo shim location).
        cargo_bin = "/home/ANT.AMAZON.COM/schapper/.cargo/bin"
        self.assertEqual(env["PATH"].split(":")[0], cargo_bin)
        self.assertIn("/usr/bin", env["PATH"].split(":"))
        # Unrelated vars preserved.
        self.assertEqual(env["TERM"], "xterm")
        # sudo bookkeeping scrubbed from the child env.
        for k in ("SUDO_USER", "SUDO_UID", "SUDO_GID", "SUDO_COMMAND"):
            self.assertNotIn(k, env)

    def test_privilege_kwargs_for_drop(self):
        ctx = po.compute_privilege_context(
            0, {"SUDO_USER": "schapper"}, getpwnam=_fake_getpwnam)
        kw = po.privilege_kwargs(ctx)
        self.assertEqual(kw["user"], 1000)
        self.assertEqual(kw["group"], 2000)
        self.assertIs(kw["env"], ctx["env"])
        self.assertEqual(set(kw), {"user", "group", "env"})

    def test_cargo_home_passthrough_when_present(self):
        environ = {
            "SUDO_USER": "schapper",
            "CARGO_HOME": "/home/ANT.AMAZON.COM/schapper/.cargo",
            "RUSTUP_HOME": "/home/ANT.AMAZON.COM/schapper/.rustup",
        }
        ctx = po.compute_privilege_context(0, environ, getpwnam=_fake_getpwnam)
        self.assertEqual(ctx["env"]["CARGO_HOME"],
                         "/home/ANT.AMAZON.COM/schapper/.cargo")
        self.assertEqual(ctx["env"]["RUSTUP_HOME"],
                         "/home/ANT.AMAZON.COM/schapper/.rustup")

    def test_cargo_home_absent_lets_cargo_default(self):
        # When unset, they are NOT injected -> cargo defaults to ~/.cargo,
        # ~/.rustup under the (now correct) HOME.
        ctx = po.compute_privilege_context(
            0, {"SUDO_USER": "schapper"}, getpwnam=_fake_getpwnam)
        self.assertNotIn("CARGO_HOME", ctx["env"])
        self.assertNotIn("RUSTUP_HOME", ctx["env"])

    def test_real_root_without_sudo_raises_graceful_error(self):
        with self.assertRaises(po.PrivilegeError) as cm:
            po.compute_privilege_context(0, {}, getpwnam=_fake_getpwnam)
        msg = str(cm.exception)
        self.assertIn("sudo", msg)
        # Actionable guidance is present.
        self.assertIn("SUDO_USER", msg)

    def test_unknown_sudo_user_raises(self):
        with self.assertRaises(po.PrivilegeError):
            po.compute_privilege_context(
                0, {"SUDO_USER": "ghost"}, getpwnam=_fake_getpwnam)

    def test_build_child_env_does_not_duplicate_cargo_bin(self):
        home = "/home/u"
        env = po.build_child_env(
            {"PATH": "/home/u/.cargo/bin:/usr/bin"}, home, "u")
        parts = env["PATH"].split(":")
        self.assertEqual(parts.count("/home/u/.cargo/bin"), 1)

    def test_build_child_env_empty_path(self):
        env = po.build_child_env({}, "/home/u", "u")
        self.assertEqual(env["PATH"], "/home/u/.cargo/bin")


if __name__ == "__main__":
    unittest.main(verbosity=2)
