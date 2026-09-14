#!/usr/bin/env bash
# Fail when a change that claims to be proof-only touches a declaration.
#
#   scripts/check-proof-only-diff.sh [base]
#
# `base` defaults to `origin/main`.  A declaration line is one that begins,
# after optional modifiers and attributes, with `theorem`, `lemma`, `def`,
# `abbrev`, `instance`, `structure`, `inductive` or `class`.  A proof-only
# refactor must leave every such line byte-identical: only proof bodies,
# comments, blank lines and attribute *lines* may differ.
#
# The check is deliberately not a required CI job for every pull request --
# ordinary work adds declarations.  It is meant for proof refactors, which is
# what the `proof-only` label marks (see CONTRIBUTING.md).
set -euo pipefail

base=${1:-origin/main}

if ! git rev-parse --verify --quiet "${base}^{commit}" >/dev/null; then
  echo "check-proof-only-diff: unknown base '$base'" >&2
  exit 2
fi

hits=$(
  git diff --unified=0 "$base"...HEAD -- '*.lean' \
    | grep -E '^[+-]' \
    | grep -vE '^(\+\+\+|---)' \
    | grep -E '^[+-][[:space:]]*(private[[:space:]]+|protected[[:space:]]+|noncomputable[[:space:]]+|partial[[:space:]]+|@\[[^]]*\][[:space:]]*)*(theorem|lemma|def|abbrev|instance|structure|inductive|class)\b' \
    || true
)

if [ -n "$hits" ]; then
  echo "check-proof-only-diff: this change is not proof-only; the following" >&2
  echo "declaration lines differ from '$base':" >&2
  printf '%s\n' "$hits" >&2
  exit 1
fi

echo "check-proof-only-diff: ok, no declaration line differs from '$base'"
