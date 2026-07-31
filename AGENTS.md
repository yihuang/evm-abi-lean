# AGENTS.md

Working notes for AI agents editing this repository: Lean 4 ABI codec
(see `docs/design.md` for the roadmap, `EvmAbi/*.lean` for the layers).

## Architecture in one paragraph

The library is a proof-first ABI codec: `encode` (Builder-based)
materializes a `Ty.Val` to bytes; `decode` (the linear canonical decoder)
reads canonical layouts back with two monotonic cursors threaded through
the **`Get2` monad** (`EvmAbi.Builder`); `decodeStrict` is `decode` plus an
exact-consumption check.  The `Get2` walkers (`decodeElem`, `decodeElems`,
`decodeTuple`) are the heart; the roundtrip family
(`decode_roundtrip`: encode ⇒ decode), soundness family (`decode_sound`:
decode ⇒ encode) and bound-free static delegation (`decode_static_append`)
are their theorems; `IsCanonical` / `decodeStrict` and the capstones
(`isCanonical_iff`, `decodeStrict_eq_some_iff`) form the strict API.
`EvmAbi.Packed` (`decodePacked`) mirrors the codec shape — a `Builder`
encoder (`putPacked`) and `Get2` walkers (`decodePackedElem` /
`decodePackedTuple`) — and reads array elements via the bound-free static
delegation (`decodeElems` / `decode_static_append`).
`EvmAbi.Codec` holds the codec proper (defs, helper packages, static
delegation); the theorem families live in `EvmAbi.Codec.Roundtrip` /
`EvmAbi.Codec.Sound` / `EvmAbi.Codec.Strict` (each family is one self-
contained `mutual` block).

## Style rules

* **Small lemmas, short proofs.**  If a proof grows past ~30 lines or
  fights the goal, split it: per-constructor lemmas, per-step lemmas,
  shared helpers.  Do not force-debug one big proof.
* State theorems in **`Get2` `.run` form**:
  `(decodeElems t k).run head tails E = some (⟨vs, hk⟩, head', tails', E')`.
  The frontier `E'` is always threaded and stated
  (`E' = E + tailSizes …`) — the old walkers dropped it; keep it.
* The per-component step (`decodeElem`) stays a **bare run**
  (`⟨fun head tails E => …⟩`): the frontier check `o = E` needs the
  state, which `do`-notation cannot read.  The walkers use `do`-notation.
* **Never measure a cursor.**  `decode` returns the bytes it consumed
  (`Option (t.Val × Nat × List UInt8)`) and `decodeElem` advances the
  frontier by that count.  `List.length` on a cursor is `O(remaining)`,
  so anything of the shape `tails.length - rest.length` turns the walk
  quadratic — this is exactly the bug the linear decoder replaced.  The
  count is structural: `32`, the count `decodeBytesPrefix` reports, or
  the walker's own final frontier.
* Mutual blocks use `termination_by` measures `8 * sizeOf t + N` (or
  `(sizeOf t, N)`); a call from sibling `A` to sibling `B` must satisfy
  `measure_B(args) < measure_A(args)`.  Two siblings at the same offset
  are fine as long as neither calls the other.

## Pitfalls (learned the hard way)

* **`++` is LEFT-associative in Lean 4 core.**  `A ++ B ++ C` parses as
  `(A ++ B) ++ C`.  When assembling equalities of appends
  (`encode t v ++ X = (put t v).toList ++ X`), you usually need
  `rw [List.append_assoc]` (and a second one for nested left-assoc
  groups), and often an explicit `rfl` after the `rw` chain — `rw`'s
  internal `rfl` check does not see through `encode`/`toList`
  definitional unfolding, a standalone `rfl` does.
* **`rw [defName]` fails for structure-valued defs** (e.g. a
  `Get2`-typed def).  Use `simp only [defName]` or `unfold defName`
  instead.
* **`rw` does not refold** `(putParts ps).toList` back to
  `encodeParts ps` by defeq matching — write `rw [← encodeParts]`
  explicitly before unfolding it.
* **`cases h : e` substitutes `e` into the goal**, so a later
  `simp [h]` is often useless (`h` is an unused simp arg — the linter
  will say so; remove it).  The substitution also leaves the goal's
  match on `some p` with shadowed binder names — run a plain `simp`
  to reduce it before rewriting inside.
* **`cases h : e` also rewrites the goal's occurrences of `e`**, e.g.
  after `cases hdw : decodeUint buf`, the goal `∃ w, decodeUint buf =
  some w ∧ …` becomes `∃ w, some w = some w ∧ …` — the conjunct is
  `rfl` (write `exact ⟨w, rfl, …⟩`), not a rewrite of `hdw`.
* **A match that binds its scrutinee (`match hp : e with`) blocks
  `cases hp : e` + `simp only [hp]`** ("simp made no progress").  Use
  `split at h` instead; its branches come in *source order* (the
  `some` branch first, then `none`).
* **Flat `obtain ⟨a, b, c, d⟩ := q` mis-binds on `A × B × C`** —
  `rcases` matches the surplus patterns against the last component
  (cons-destructing a list!).  Write the nesting explicitly:
  `obtain ⟨⟨a, b⟩, c⟩ := q`.
* **`constructor` splits a right-nested conjunction only one level**:
  `A ∧ B ∧ C` → goals `A` and `B ∧ C`.  For three conjuncts use
  `refine ⟨?_, ?_, ?_⟩`.
* **`rw` direction matters**; "Did not find an occurrence of the
  pattern" usually means (a) you wrote `← h` when you need `h` (or
  vice versa), or (b) the term needs unfolding first — e.g. add
  `encodeAddress` to the `simp` before `rw [← buf_take_32_eq_…]` can
  match `encodeUint x` inside it.
* **`subst h` with `h : a = b` replaces the RHS variable `b` by `a`**
  (cases on `Eq.refl a`).  Name the variable that survives.
* **`simpa only [thm]` does not strip `some`** — for
  `some a = some b → a = b` use `simpa [thm]` (full simp set) or
  `Option.some.inj`.
* **Sibling termination offsets**: keep them ordered so every mutual
  call decreases (`decodeElem` +1 calls `decode` +0 on the same `t`;
  `decodeElems` +2 calls `decodeElem` +1; `decode` calls `decodeElems`/
  `decodeTuple` on strictly smaller types).

## Quirks to respect

* `IsCanonical` is `(decodeStrict t buf).isSome = true` with an explicit
  `Decidable` instance — instance search does not unfold plain defs.
* `decodeStrict` needs the `2^256` bound only for the completeness
  direction (`encode ⇒ decode`), so offset words cannot wrap; static
  types never need it (`decode_static_append`).
* `Packed` reads array elements via the standard `decodeElems`
  (bound-free static delegation); its own walkers stay structurally
  recursive so `by decide` still evaluates packed decodes.
