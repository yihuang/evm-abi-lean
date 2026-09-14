#!/usr/bin/env python3
"""Proof-body lines per module, as CONTRIBUTING.md's metric defines them.

A proof body is a **tactic block**: the line carrying a `by` token, plus every
following line indented past it.  Blank lines and comments do not count.

Anchoring on the `by` token rather than on `:= by` is the whole point.  A
`structure` instance written with `where` has no `:= by` on its declaration
line, so a metric that looks for one scores every tactic in its fields as
zero -- and a refactor can then post a large reduction purely by moving
proofs from `theorem foo := by` into the fields of a `def foo … where`,
without deleting a line of tactic text.  That is not hypothetical: it is
what #53 did, and it is why this script exists rather than a prose
definition alone.

The count of **term-mode theorems** is reported alongside for the same
reason.  A proof rewritten from a tactic block into a term (`:= lemma a b`)
is genuinely shorter, but it drops to zero under any tactic-line metric, so
a bare line count would read that as a much larger win than it is.  Show
both and the reader can tell the two apart.

Usage:
    ./proof-body-lines.py FILE...            # count the files
    ./proof-body-lines.py --base main FILE   # compare against a git ref
    ./proof-body-lines.py --base main        # every .lean the branch changed
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path

DECL = re.compile(r"^(private |protected |noncomputable |partial |@\[[^\]]*\]\s*)*"
                  r"(theorem|lemma|example)\b")
# A `by` that opens a tactic block: `:= by`, `=> by`, `by` alone at end of line.
BY = re.compile(r"(?:^|[\s(\[=>])by(?:\s|$)")


def strip_comments(lines: list) -> list:
    """True for every line that is blank or wholly comment."""
    out, depth = [], 0
    for line in lines:
        s = line.strip()
        inside = depth > 0
        depth += line.count("/-") - line.count("-/")
        out.append(inside or s == "" or s.startswith("--") or s.startswith("/-"))
    return out


def indent(line: str) -> int:
    return len(line) - len(line.lstrip())


def measure(text: str) -> tuple:
    """(tactic lines, term-mode theorem count)."""
    lines = text.splitlines()
    skip = strip_comments(lines)
    counted = [False] * len(lines)

    for i, line in enumerate(lines):
        if skip[i] or not BY.search(line):
            continue
        base = indent(line)
        counted[i] = True
        for j in range(i + 1, len(lines)):
            if skip[j]:
                continue
            if indent(lines[j]) <= base:
                break
            counted[j] = True

    # A theorem is term-mode when no line of it opens a tactic block.
    term = 0
    starts = [i for i, l in enumerate(lines) if not skip[i] and DECL.match(l)]
    for k, i in enumerate(starts):
        end = starts[k + 1] if k + 1 < len(starts) else len(lines)
        body = range(i, end)
        if not any(not skip[j] and BY.search(lines[j]) for j in body):
            term += 1

    return sum(counted), term


def at_ref(ref: str, path: str) -> str:
    p = subprocess.run(["git", "show", f"{ref}:{path}"], capture_output=True, text=True)
    return p.stdout if p.returncode == 0 else ""


def changed(base: str) -> list:
    p = subprocess.run(["git", "diff", "--name-only", f"{base}...HEAD", "--", "*.lean"],
                       capture_output=True, text=True)
    if p.returncode != 0:
        sys.exit(p.stderr.strip() or f"cannot diff against {base}")
    return [f for f in p.stdout.split() if f]


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--base", help="git ref to compare against")
    ap.add_argument("files", nargs="*")
    args = ap.parse_args()

    files = args.files or (changed(args.base) if args.base else [])
    if not files:
        ap.error("give files, or --base REF to take everything the branch changed")

    if not args.base:
        total = 0
        for f in files:
            n, t = measure(Path(f).read_text())
            total += n
            print(f"{f:<34}{n:>6}{('  (' + str(t) + ' term-mode)') if t else ''}")
        print(f"{'TOTAL':<34}{total:>6}")
        return

    print(f"{'module':<34}{'base':>7}{'head':>7}{'delta':>8}{'term-mode':>12}")
    tb = th = 0
    for f in files:
        b, bt = measure(at_ref(args.base, f))
        h, ht = measure(Path(f).read_text() if Path(f).exists() else "")
        tb += b
        th += h
        print(f"{f:<34}{b:>7}{h:>7}{h - b:>+8}{bt:>6} ->{ht:>4}")
    pct = f"{100 * (th - tb) / tb:+.1f}%" if tb else "n/a"
    print(f"{'TOTAL':<34}{tb:>7}{th:>7}{th - tb:>+8}   {pct}")


if __name__ == "__main__":
    main()
