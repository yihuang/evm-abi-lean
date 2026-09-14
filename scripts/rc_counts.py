#!/usr/bin/env python3
"""Reference-count traffic in the generated C, per function.

Lean's ownership inference decides where to emit `lean_inc`/`lean_dec`, and it
is sensitive to the *shape* of the types a function scrutinises, not only to
its own source.  A change to `Ty` once took `emitVal` from 4 `lean_dec` to 20
with the function body untouched, and every static-element array paid that per
element.  Timing found the symptom late and noisily; this count is exact and
machine-independent, so it runs usefully on a shared runner where a benchmark
cannot.

It counts occurrences, not calls, so it reports rather than decides: an
increase inside a per-element walker (`emitVal`, `emitVals`, `emitAny`) is paid
per element and matters, where the same increase in something run once per
encode is usually the price of a win elsewhere.

Usage:
    ./rc_counts.py .lake/build/ir > counts.json   # snapshot one build
    ./rc_counts.py --diff before.json after.json  # report the increases
"""

import json
import re
import sys
from pathlib import Path

NAME = re.compile(r"([A-Za-z_]\w*)\s*$")


def opens_definition(line: str) -> str | None:
    """The function name, if this line opens a top-level definition.

    Lean emits definitions at column 0 with the body's `{` on the signature
    line; forward declarations are the same shape but end in `);`.  The name is
    the identifier immediately before the parameter list.
    """
    if not line or line[0].isspace() or ";" in line or "(" not in line:
        return None
    if not line.rstrip().endswith("{"):
        return None
    m = NAME.search(line.split("(", 1)[0])
    return m.group(1) if m else None


def counts_for(path: Path) -> dict:
    """{function: {inc, dec}} for one generated .c file."""
    out, name, depth, inc, dec = {}, None, 0, 0, 0
    for line in path.read_text(errors="replace").splitlines():
        if name is None:
            name = opens_definition(line)
            if name is None:
                continue
            depth, inc, dec = 0, 0, 0
        inc += line.count("lean_inc")
        dec += line.count("lean_dec")
        depth += line.count("{") - line.count("}")
        if depth == 0:
            if inc or dec:
                out[name] = {"inc": inc, "dec": dec}
            name = None
    return out


def snapshot(ir_dir: Path) -> dict:
    """Walk a build's IR directory, keyed by module then function."""
    out = {}
    for c in sorted(ir_dir.rglob("*.c")):
        mod = str(c.relative_to(ir_dir).with_suffix(""))
        fns = counts_for(c)
        if fns:
            out[mod] = fns
    return out


def diff(before: dict, after: dict) -> list:
    """Functions whose refcount traffic grew, worst first."""
    rows = []
    for mod, fns in after.items():
        for fn, now in fns.items():
            was = before.get(mod, {}).get(fn)
            if was is None:
                continue  # new function: nothing to compare against
            d = (now["inc"] + now["dec"]) - (was["inc"] + was["dec"])
            if d > 0:
                rows.append((d, mod, fn, was, now))
    return sorted(rows, reverse=True)


def main() -> None:
    if sys.argv[1:2] == ["--diff"]:
        before = json.loads(Path(sys.argv[2]).read_text())
        after = json.loads(Path(sys.argv[3]).read_text())
        rows = diff(before, after)
        if not rows:
            print("No function gained reference-count traffic.")
            return
        print(f"{len(rows)} function(s) gained reference-count traffic:\n")
        print(f"{'delta':>6}  {'inc/dec before':>16}  {'after':>10}  function")
        for d, mod, fn, was, now in rows:
            print(f"{d:>+6}  {was['inc']:>7}/{was['dec']:<8}  "
                  f"{now['inc']:>4}/{now['dec']:<5}  {mod}::{fn}")
        sys.exit(1)
    print(json.dumps(snapshot(Path(sys.argv[1])), indent=1, sort_keys=True))


if __name__ == "__main__":
    main()
