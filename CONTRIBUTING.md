# Contributing

Working notes live in [AGENTS.md](AGENTS.md); this file records the few rules
that a reviewer should be able to check mechanically, or that were learned from
a concrete accident.

## Proofs

### Do not add a global `grind` annotation

`attribute [grind =]` (and `[grind →]`, `[grind ←]`, `grind_pattern`) are
*global*: they enter the environment of every module that transitively imports
the file they are written in.  A proof verified with `lake env lean` can
therefore pass against the stale `.olean` in `.lake/build` and then be rejected
by `lake build`, after the annotation is actually in the environment.

That happened on the `grind` migration: an `attribute [grind =]` block added in
`EvmAbi/Parts.lean` turned an already-passing `EvmAbi/Spec/Roundtrip.lean` into
a redundant-parameter error plus two `isDefEq` heartbeat timeouts, while
`lake env lean EvmAbi/Spec/Roundtrip.lean` on the same file still reported no
errors.

Use a **local hint list** instead (`grind [lemma₁, …, lemmaₙ]`), at most about
six lemmas, and prefer a fresh `lake build` when you need to be sure.  `grind`
also rejects local hypotheses and mutual-block siblings as arguments
("redundant parameter"); pass an *instantiated* application
(`decodeElemsBA_eq t k ba off`, `ih (off + 1) (by omega)`) rather than a bare
name.

### Bare `grind` is a default-set dependency

A bare `grind` (no hint list) depends on whichever lemmas carry `@[grind]` in
core and in this library at the time.  It is fine to use, but on a toolchain
upgrade the bare `grind` proofs are the first place to look -- they can start
needing a hint or a heartbeat bump without any local edit.

### Proof-only refactors

A pull request that only replaces proof bodies should not touch a declaration:
no theorem or lemma statement, name, argument order, doc comment or `termination_by`
line.  Check it with

```bash
scripts/check-proof-only-diff.sh origin/main
```

which fails if any added or removed line begins with a declaration keyword.
Pull requests carrying the `proof-only` label run the same script in CI
(`.github/workflows/lean_action_ci.yml`); the label is what opts a pull request
in, so ordinary pull requests that add lemmas are unaffected.

When a proof refactor does need a new helper lemma, drop the label and say so in
the description, as a reviewer cannot tell the two apart from the diff alone.

### Measure, do not estimate

Proof length is measured in proof-body lines: the line carrying a `by` token
plus the tactic block it opens, blanks and comments excluded.  Run

```bash
scripts/proof-body-lines.py --base origin/main
```

so a reviewer can reproduce the number.

The anchor is `by`, not `:= by`: a `where` instance has no `:= by`, so
anchoring there scores its fields as zero and a refactor can post a reduction
by moving proofs into them.  The script also counts term-mode theorems, which
score zero under any tactic-line count — quote both.
