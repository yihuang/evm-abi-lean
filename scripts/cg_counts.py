#!/usr/bin/env python3
"""Instructions executed per benchmark row, under callgrind.

Timing on a shared runner cannot carry a threshold: row medians drift 5-30%
between runs, so any threshold small enough to catch a real regression
invents several a week.  Counting instructions removes the drift rather than
averaging it away -- three runs of one binary spanned 0.0006%, so re-running
buys nothing.

The count is not a pure function of the code under test, though: a commit
that changes codegen shifts layout, and untouched rows move by a fraction of
a percent.  Nor is it time -- a change trading instructions for locality
moves the two in opposite directions, so a row over the threshold is a
question for the wall-clock job, not by itself a verdict.

Each row runs in its own process with `--once`, and process start is measured
separately and subtracted: without that a 2 us row sits under a constant so
much larger that a 50% regression in it reads as rounding.

Usage:
    ./cg_counts.py --snapshot ./bench-regress out.json
    ./cg_counts.py --diff before.json after.json [--threshold 0.02]
"""

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

BENCH_RE = re.compile(r"^BENCH (\S+) (\d+) (\d+)$")
REFS_RE = re.compile(r"I\s+refs:\s+([\d,]+)")

# A key no row uses, so the run measures process start and module
# initialisation and nothing else.
BASELINE = "__baseline__"


def callgrind(binary: Path, args: list) -> int:
    """Instructions executed by one run of `binary`."""
    p = subprocess.run(
        ["valgrind", "--tool=callgrind", "--callgrind-out-file=/dev/null",
         str(binary)] + args,
        capture_output=True, text=True)
    if p.returncode != 0:
        sys.stderr.write(p.stdout + p.stderr)
        sys.exit(f"callgrind failed on {binary} {' '.join(args)} ({p.returncode})")
    m = REFS_RE.search(p.stderr)
    if not m:
        sys.stderr.write(p.stderr)
        sys.exit("callgrind printed no instruction count")
    return int(m.group(1).replace(",", ""))


def keys_of(binary: Path) -> list:
    p = subprocess.run([str(binary), "--once"], capture_output=True, text=True)
    if p.returncode != 0:
        sys.stderr.write(p.stdout + p.stderr)
        sys.exit(f"{binary} failed ({p.returncode})")
    keys = [m[1] for m in map(BENCH_RE.match, p.stdout.splitlines()) if m]
    if not keys:
        sys.exit(f"no BENCH lines from {binary}: is this bench-regress?")
    return keys


def snapshot(binary: Path) -> dict:
    base = callgrind(binary, ["--once", BASELINE])
    out = {"__startup__": base}
    for key in keys_of(binary):
        total = callgrind(binary, ["--once", key])
        # A row cheaper than the noise in process start would come out
        # negative; clamp so the diff below never divides by a negative.
        out[key] = max(total - base, 1)
        print(f"{key:<30} {out[key]:>12,}", file=sys.stderr, flush=True)
    return out


def diff(before: dict, after: dict, threshold: float) -> int:
    rows, gone, new = [], [], []
    for key, now in after.items():
        if key == "__startup__":
            continue
        was = before.get(key)
        if was is None:
            new.append(key)
            continue
        rows.append(((now - was) / was, key, was, now))
    gone = [k for k in before if k not in after and k != "__startup__"]

    rows.sort(reverse=True)
    worse = [r for r in rows if r[0] > threshold]

    print(f"{'delta':>8}  {'before':>13}  {'after':>13}  row")
    for d, key, was, now in rows:
        mark = "  <-- over threshold" if d > threshold else ""
        print(f"{d:>+7.2%}  {was:>13,}  {now:>13,}  {key}{mark}")
    if new:
        print(f"\nnew rows, nothing to compare against: {', '.join(sorted(new))}")
    if gone:
        print(f"\nrows that disappeared: {', '.join(sorted(gone))}")

    startup = after.get("__startup__", 0) - before.get("__startup__", 0)
    if startup:
        print(f"\nprocess start and module init moved {startup:+,} instructions "
              f"(subtracted from every row above)")

    if worse:
        print(f"\n{len(worse)} row(s) execute more than {threshold:.0%} more "
              f"instructions than the base.")
        return 1
    print(f"\nNo row gained more than {threshold:.0%}.")
    return 0


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--snapshot", nargs=2, metavar=("BIN", "OUT"))
    ap.add_argument("--diff", nargs=2, metavar=("BEFORE", "AFTER"))
    ap.add_argument("--threshold", type=float, default=0.01,
                    help="fractional increase that counts (default: %(default)s)")
    args = ap.parse_args()

    if args.snapshot:
        binary, out = Path(args.snapshot[0]).resolve(), Path(args.snapshot[1])
        out.write_text(json.dumps(snapshot(binary), indent=1, sort_keys=True))
    elif args.diff:
        before, after = (json.loads(Path(p).read_text()) for p in args.diff)
        sys.exit(diff(before, after, args.threshold))
    else:
        ap.error("give --snapshot BIN OUT or --diff BEFORE AFTER")


if __name__ == "__main__":
    main()
