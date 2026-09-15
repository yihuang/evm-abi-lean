#!/usr/bin/env python3
"""Proof-body lines per module, as CONTRIBUTING.md's metric defines them.

A proof body is a tactic block: the line carrying a `by` token, plus every
following line indented past it, blanks and comments excluded.

The anchor is `by`, not `:= by`.  A `structure` instance written with `where`
has no `:= by`, so anchoring there scores its fields as zero and a refactor
can post a reduction by moving proofs into them -- which is what #53 did.

Term-mode theorems are reported alongside, since a proof rewritten as a term
scores zero here and would otherwise read as a saving of its whole body.

Usage:
    ./proof-body-lines.py FILE...            # count the files
    ./proof-body-lines.py --base main FILE   # compare against a git ref
    ./proof-body-lines.py --base main        # every .lean the branch changed
"""

import argparse
import re
import subprocess
from pathlib import Path

DECL = re.compile(r"^(private |protected |noncomputable |partial |@\[[^\]]*\]\s*)*"
                  r"(theorem|lemma|example)\b")
# A `by` that opens a tactic block: `:= by`, `=> by`, `by` at end of line.
BY = re.compile(r"(?:^|[\s(\[=>])by(?:\s|$)")


def skippable(lines: list) -> list:
    """True for each line that is blank or wholly comment."""
    flags, depth = [], 0
    for line in lines:
        s = line.strip()
        flags.append(depth > 0 or not s or s.startswith(("--", "/-")))
        depth += line.count("/-") - line.count("-/")
    return flags


def measure(text: str) -> tuple:
    """(tactic-block lines, term-mode theorem count)."""
    lines = text.splitlines()
    skip = skippable(lines)
    opens = [not skip[i] and bool(BY.search(l)) for i, l in enumerate(lines)]
    indent = [len(l) - len(l.lstrip()) for l in lines]

    counted = [False] * len(lines)
    for i in range(len(lines)):
        if not opens[i]:
            continue
        counted[i] = True
        # `stop` is the shallowest indent still inside the block.  A `by` at
        # end of line opens its block on the next line, which may be indented
        # *less* than the `by` itself -- a multi-line signature puts `:= by`
        # under a four-space continuation and the tactics under two -- so the
        # body's own indent is the bound.  A `by` with tactics after it on the
        # same line continues only under that line.
        if lines[i].rstrip().endswith("by"):
            body = next((j for j in range(i + 1, len(lines)) if not skip[j]), None)
            if body is None:
                continue
            stop = indent[body]
        else:
            stop = indent[i] + 1
        for j in range(i + 1, len(lines)):
            if skip[j]:
                continue
            if indent[j] < stop:
                break
            counted[j] = True

    starts = [i for i, l in enumerate(lines) if not skip[i] and DECL.match(l)]
    ends = starts[1:] + [len(lines)]
    term = sum(1 for i, e in zip(starts, ends) if not any(opens[i:e]))

    return sum(counted), term


def git(*args: str) -> str:
    p = subprocess.run(["git", *args], capture_output=True, text=True)
    return (p.stdout or "") if p.returncode == 0 else ""


def read(path: str) -> str:
    return Path(path).read_text() if Path(path).exists() else ""


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--base", help="git ref to compare against")
    ap.add_argument("files", nargs="*")
    args = ap.parse_args()

    files = args.files
    if not files and args.base:
        files = git("diff", "--name-only", f"{args.base}...HEAD", "--", "*.lean").splitlines()
        if not files:
            # Not an argument error -- `--base` was given.  The usual cause is
            # work that is still uncommitted, which a commit-to-commit diff
            # cannot see.
            raise SystemExit(f"no .lean file differs from {args.base}; "
                             f"uncommitted work is not counted, so commit it "
                             f"first or name the files explicitly")
    if not files:
        ap.error("give files, or --base REF to take everything the branch changed")

    if not args.base:
        print(f"{'module':<34}{'lines':>7}{'term-mode':>11}")
        total = 0
        for f in files:
            n, t = measure(read(f))
            total += n
            print(f"{f:<34}{n:>7}{t:>11}")
        print(f"{'TOTAL':<34}{total:>7}")
        return

    print(f"{'module':<34}{'base':>7}{'head':>7}{'delta':>8}{'term-mode':>12}")
    was = now = 0
    for f in files:
        b, bt = measure(git("show", f"{args.base}:{f}"))
        h, ht = measure(read(f))
        was, now = was + b, now + h
        print(f"{f:<34}{b:>7}{h:>7}{h - b:>+8}{bt:>6} ->{ht:>4}")
    pct = f"{100 * (now - was) / was:+.1f}%" if was else "n/a"
    print(f"{'TOTAL':<34}{was:>7}{now:>7}{now - was:>+8}   {pct}")


if __name__ == "__main__":
    main()
