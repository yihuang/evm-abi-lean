#!/usr/bin/env python3
"""A/B two checkouts of this repo on the keyed regression bench.

Both binaries are built up front and then run alternately, so drift lands on
both columns equally.  What decides whether a row moved is a rank test, not a
comparison of ranges: a range grows with the sample count, so a range test
gets *weaker* the more runs you give it, which is the opposite of what
`--runs` should buy.  Measured against 120 real runs of this bench, the range
test needed about +20% on most rows before it fired at all, and could not
confirm a real 12% win whose ranges still touched at the edge.

A row is reported as moved when both hold:

  * the two samples are separable -- Mann-Whitney U, two-sided, p < 0.01; and
  * the median shift clears `GUARD`, so a reliably separable 0.4% change,
    which is real but not worth anyone's afternoon, stays quiet.

Dependencies come from each checkout's committed `lake-manifest.json`, which
`lake build` honours and does not re-resolve, so both sides link the same
lean-binary.  (Pinning the harness's lakefile at a branch and running
`lake update` per side, as the cross-language harness did, leaves the two
builds free to pick up different dependency revisions minutes apart.)

Usage:
    ./bench_ab.py --build DIR OUT          # build bench-regress from a checkout
    ./bench_ab.py BASE_BIN HEAD_BIN [--runs N] [--key K ...]
"""

import argparse
import collections
import math
import re
import shutil
import statistics
import subprocess
import sys
from pathlib import Path

BENCH_RE = re.compile(r"^BENCH (\S+) (\d+) (\d+)$")

# Below this a real, repeatable shift is not worth reporting as a regression.
GUARD = 0.02
# Two-sided significance for the rank test.
ALPHA = 0.01


def sh(cmd: list, cwd: Path) -> None:
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if p.returncode != 0:
        sys.stderr.write(p.stdout + p.stderr)
        sys.exit(f"{' '.join(cmd)} failed in {cwd} ({p.returncode})")


TARGET = '\n[[lean_exe]]\nname = "bench-regress"\nroot = "BenchRegress"\n'


def build(src: str, out: Path, bench_from: str | None = None) -> None:
    """Build `bench-regress` in a checkout and copy the binary out.

    `bench_from` overlays that checkout's bench source onto this one, adding
    the Lake target if it is missing.  The instrument has to be the same on
    both sides: a checkout old enough to be the merge base of the commit that
    *adds* a row does not have the row, and a pull request free to edit the
    bench and the encoder together could otherwise report a change in the
    measurement as a change in the code.
    """
    d = Path(src).resolve()
    if not (d / "lakefile.toml").is_file():
        sys.exit(f"{d} is not a checkout of this repo (no lakefile.toml)")
    if bench_from:
        shutil.copy(Path(bench_from).resolve() / "BenchRegress.lean",
                    d / "BenchRegress.lean")
        lakefile = d / "lakefile.toml"
        text = lakefile.read_text()
        if 'name = "bench-regress"' not in text:
            lakefile.write_text(text.rstrip() + "\n" + TARGET)
    sh(["lake", "build", "bench-regress"], d)
    shutil.copy(d / ".lake/build/bin/bench-regress", out)


def run_bench(binary: Path, args: list) -> dict:
    """Run the bench binary, as {row: ns/op}."""
    p = subprocess.run([str(binary)] + args, capture_output=True, text=True)
    if p.returncode != 0:
        sys.stderr.write(p.stdout + p.stderr)
        sys.exit(f"{binary} failed ({p.returncode})")
    rows = {m[1]: int(m[2]) for m in map(BENCH_RE.match, p.stdout.splitlines()) if m}
    if not rows:
        sys.exit(f"no BENCH lines from {binary}: is this bench-regress?")
    return rows


def keys_of(binary: Path) -> list:
    """Every row the binary knows.  `--once` skips the probe and the budget,
    so this enumerates the full set in a few milliseconds."""
    return list(run_bench(binary, ["--once"]))


def collect(base: Path, head: Path, runs: int, keys: list) -> dict:
    """{row: (base samples, head samples)}.

    One row per process.  Sharing a process across rows is what the bench
    used to do, and it makes the allocation-heavy rows -- `int256[]` and
    `address[]` both build a bignum per element -- perturb whatever runs
    after them through the heap they leave behind: two runs of the *same*
    binary disagreed by 50% on `int256[]` that way, against 6% when the row
    has the process to itself.  Base and head alternate within each row, so
    drift stays local to the pair being compared.
    """
    rows = collections.defaultdict(lambda: ([], []))
    for i in range(runs):
        for key in keys:
            for column, exe in ((0, base), (1, head)):
                rows[key][column].append(run_bench(exe, [key])[key])
        print(f"run {i + 1}/{runs}", file=sys.stderr, flush=True)
    return rows


def mannwhitney_p(a: list, b: list) -> float:
    """Two-sided Mann-Whitney U by normal approximation, tie-corrected.

    Ties are the common case: neighbouring runs of a cheap row repeat values,
    and without the correction the variance is overstated and everything
    reads as "no difference".
    """
    n1, n2 = len(a), len(b)
    pool = sorted(a + b)
    rank, i = {}, 0
    while i < len(pool):
        j = i
        while j + 1 < len(pool) and pool[j + 1] == pool[i]:
            j += 1
        rank[pool[i]] = (i + j) / 2 + 1
        i = j + 1
    u = sum(rank[x] for x in a) - n1 * (n1 + 1) / 2
    n = n1 + n2
    ties = collections.Counter(pool)
    var = n1 * n2 / 12 * ((n + 1) - sum(t**3 - t for t in ties.values()) / (n * (n - 1)))
    if var <= 0:
        return 1.0
    return math.erfc(abs(u - n1 * n2 / 2) / math.sqrt(var) / math.sqrt(2))


def report(rows: dict, runs: int) -> int:
    both = sorted(row for row, (b, h) in rows.items() if b and h)
    if skipped := sorted(set(rows) - set(both)):
        print(f"missing from one build, skipped: {', '.join(skipped)}", file=sys.stderr)
    if not both:
        sys.exit("no row appeared in both builds")

    print(f"\n{runs} alternating runs per build, ns/op\n")
    print(f"{'row':<30} {'base':>9} {'head':>9} {'delta':>8} {'p':>9}  verdict")
    moved = 0
    for row in both:
        b, h = rows[row]
        mb, mh = statistics.median(b), statistics.median(h)
        delta = (mh - mb) / mb if mb else 0.0
        p = mannwhitney_p(b, h)
        if p < ALPHA and abs(delta) >= GUARD:
            verdict = "SLOWER" if delta > 0 else "faster"
            moved += delta > 0
        elif p < ALPHA:
            verdict = f"separable, under {GUARD:.0%}"
        else:
            verdict = "no difference"
        print(f"{row:<30} {mb:>9g} {mh:>9g} {delta:>+7.1%} {p:>9.1e}  {verdict}")
    print(f"\n{moved} row(s) got slower by more than {GUARD:.0%}.")
    return moved


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--build", nargs=2, metavar=("DIR", "OUT"),
                    help="build bench-regress from a checkout, binary to OUT")
    ap.add_argument("--bench-from", metavar="DIR",
                    help="with --build: take BenchRegress.lean from DIR, so "
                         "both sides are measured by the same instrument")
    ap.add_argument("--runs", type=int, default=30,
                    help="alternating runs per build (default: %(default)s)")
    ap.add_argument("--key", action="append", default=[],
                    help="restrict to this row (repeatable)")
    ap.add_argument("bins", nargs="*", metavar="BIN", help="BASE_BIN HEAD_BIN")
    args = ap.parse_args()

    if args.build:
        build(args.build[0], Path(args.build[1]).resolve(), args.bench_from)
    elif len(args.bins) == 2:
        base, head = (Path(b).resolve() for b in args.bins)
        keys = args.key or keys_of(head)
        if missing := sorted(set(keys) - set(keys_of(base))):
            print(f"absent from the base build, skipped: {', '.join(missing)}",
                  file=sys.stderr)
            keys = [k for k in keys if k not in missing]
        sys.exit(1 if report(collect(base, head, args.runs, keys), args.runs) else 0)
    else:
        ap.error("give BASE_BIN and HEAD_BIN, or --build DIR OUT")


if __name__ == "__main__":
    main()
