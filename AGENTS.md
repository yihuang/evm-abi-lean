# AGENTS.md

Working notes for AI agents editing this repository: Lean 4 ABI codec
(see `docs/design.md` for the roadmap, `EvmAbi/*.lean` for the layers).

## Architecture in one paragraph

The library is a proof-first ABI codec with two layers.  The **spec layer**
(`EvmAbi.Spec`, implemented by `EvmAbi.Codec` and its `Roundtrip`/`Sound`/
`Strict` families) is the proof surface: `Spec.put` builds a `Ty.Val` into
a `Builder` (`EvmAbi.Builder`: a chunk tree with `O(1)` `++` and a cached
size), materialized two ways — `Spec.encode = (put t v).toList` is the
`List UInt8` specification every theorem is stated over, and
`Spec.encodeByteArray = (put t v).run` fills the same builder into a
pre-sized `ByteArray`, bridged by `Spec.data_toList_encodeByteArray`.
`Spec.decode` is the linear canonical decoder reading with two monotonic
cursors threaded through the **`Get2` monad** (`EvmAbi.Builder`);
`Spec.decodeStrict` is `Spec.decode` plus an exact-consumption check.  The
`Get2` walkers (`Spec.decodeElem`, `Spec.decodeElems`, `Spec.decodeTuple`)
are the heart; the roundtrip family (`Spec.decode_roundtrip`: encode ⇒
decode), soundness family (`Spec.decode_sound`: decode ⇒ encode) and
bound-free static delegation (`Spec.decode_static_append`) are their
theorems; `Spec.IsCanonical` / `Spec.decodeStrict` and the capstones
(`Spec.isCanonical_iff`, `Spec.decodeStrict_eq_some_iff`) form the strict
API.

The **runtime layer** (`EvmAbi.Codec.Runtime`) is what users run: `encode`
over `ValBA` values into a `ByteArray`, `decode` / `decodeStrict` over a
`ByteArray` into `ValBA` values, and `IsCanonical`.  It is tied to the spec
by `toList_putBA` (runtime encoder denotes the spec encoder of the
denotation), `ValBA.toList`, and the decoder agreement family in
`EvmAbi.Codec.ByteArray`; a private `decodeBA` walker there is a proof
bridge and is not public API.
`EvmAbi.Packed` (`decodePacked`) mirrors the codec shape — a `Builder`
encoder (`putPacked`) and `Get2` walkers (`decodePackedElem` /
`decodePackedTuple`) — and reads array elements via the bound-free static
delegation (`Spec.decodeElems` / `Spec.decode_static_append`).
`EvmAbi.Codec.ByteArray` mirrors the decoder over offsets — `GetBA` is
`Get2` with the two cursors as naturals into one buffer — and pairs every
definition with an agreement lemma under `off ↦ ba.data.toList.drop off`,
so the list families transport rather than being restated.  Reads there go
through `natAtBA` / `windowList`, never through a slice.  `EvmAbi.Codec`
holds the spec codec proper (defs, helper packages, static delegation); the
theorem families live in `EvmAbi.Codec.Roundtrip` / `EvmAbi.Codec.Sound` /
`EvmAbi.Codec.Strict` (each family is one self-contained `mutual` block).

## Style rules

* **Naming:** the runtime API is primary and unsuffixed (`encode`,
  `decode`, `decodeStrict`, `IsCanonical`); the list/spec API lives in the
  `Spec` namespace (`Spec.encode`, `Spec.decodeStrict`, …).  New
  `ByteArray`/`ValBA` work goes in `EvmAbi.Codec.Runtime` or
  `EvmAbi.Codec.ByteArray` and must ship with its agreement lemma against
  the `Spec` counterpart.
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
* **Never walk the chunk tree for a size.**  `Part.headSize`/`tailSize`
  and `putHeads` read `Builder.size`, the cached count, because the
  head/tail layout asks for every tail's size while writing the offset
  words; computing it from `toList` would restore the `O(n · depth)` cost
  the builder exists to remove.  `Builder.size_eq_length_toList` rewrites
  the cache back to `toList.length`, so *statements* stay on the
  specification side and only the definitions see `size`.
* **`Builder.++` is a constructor, so it is associative only up to
  `toList`.**  `(a ++ b) ++ c` and `a ++ (b ++ c)` are different trees.
  Never state a `Builder`-valued equation that needs associativity or
  `∅`-neutrality — state it of `toList` instead (see
  `encodeHeads_append` / `encodeTails_append`, which are proved by
  induction at the list level for exactly this reason).
* **Windows are clamped.**  `windowList` and anything like it must clamp
  their end to `ba.size`: the length is a word off the wire, and
  `ByteArray.extract` sizes its copy from the range it is handed, so an
  unclamped window asks the allocator for up to `2 ^ 256` bytes.  `take`
  clamps on the list side, so clamping costs nothing in the spec.
* **The `array` clause matches dependently.**  Both decoders read the
  length word with `match hk : … with` because the `some k` branch needs
  `hk` for the `Ty.Val` bound, so neither scrutinee can be rewritten in
  place (`motive is not type correct`).  Resolve the match once against a
  known word with the `decode_array_pos` / `_none` pair — the device
  `decode_bytes_pos` already uses — and work with the plain match that
  leaves.
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

## Compiler rules

* **See what the emitter produces with the `trace` flag.**
  `abi_codec foo "…" trace` prints each specialised definition and its
  correctness theorem as it is emitted, as raw unelaborated syntax (macro
  scopes stripped, display only).
  When changing `Compile.Meta`, run a traced codec before and after to see
  the diff in the generated code; `Tests.lean` pins the transcript for
  `abi_codec tiny "(bool)" trace`.

* **The emitter never invents a proof.**  Every generated theorem is a lemma
  from `EvmAbi.Compile` applied to sub-results.  If a new `Ty` clause needs
  reasoning the emitter cannot express as one application, add the lemma to
  `EvmAbi.Compile` — do not generate a tactic script that searches.
* **Generated statements are binder-free** (`Denotes ty node3`), so nothing
  has to be spliced into a binder position.  The one exception is the tuple
  body, which needs `v.1`, `v.2.1`, …: build its `v` with
  `mkIdent (← MonadQuotation.addMacroScope \`v)` and splice the *same* ident
  into the `fun` binder and every projection.
* **`simp only` will not fire on `partsOfTupleBA`'s generated equations** —
  the value argument is dependent, and unification gives up.  That is why
  `Compile.partsOfTupleBA_cons` is stated with projections (`v.1`, `v.2`)
  rather than a pair pattern: in that form `simp only` matches, and emitted
  proofs need no `obtain`.
* **Compile-time constants must be justified, not assumed.**  The head-size
  numeral the emitter folds into `Acc.start` is `headSizeSum ts`; the machine
  is only allowed to close (`Inv.finish_toList`) against the real
  `headSizes ps`, and `headSizes_partsOfTupleBA` (needs `AllValid ts`,
  emitted as `by decide`) is what connects them.  The decoder's clauses take
  their head size as a *parameter* for the same reason, with `rfl` against
  `Ty.headSize`/`headSizeSum` as the emitted justification.
* **The decoder's equalities are between `GetBA` programs**, so they go
  through `funext` and a local `getBA_ext`, and the branches close by `rfl`
  only after both matches have been reduced — `cases hq : e <;> simp only [hq]`
  where a bare `rfl` fails, because the two sides use *different* auxiliary
  matchers with the same body.
* **Emitted code is checked by the kernel as it is emitted**, so a compiler
  bug is a compile-time error, never a wrong codec.  Keep it that way: no
  `sorry`, no `native_decide`, no `Decidable` shortcuts in emitted proofs.
* **The machine's instructions are `@[inline]` and its loops
  `@[specialize]`.**  An instruction is a three-field structure the compiler
  should fold into its caller; without the attributes the array rows of the
  benchmark lose ~1.2×, because every element allocates a state instead of
  updating one.  For the same reason `cons`/`elems` take the reader *maker*
  (`elemStatic`/`elemDyn`) plus the component's decoder, not a built `GetBA`:
  a structure argument is opaque to the specialiser, and passing one costs
  ~10 ns per component.
* **Do not replace the builder with a chain of `ByteArray` appends.**  It looks
  like the tighter target for an all-static type, whose size is a compile-time
  constant, and it is measurably worse: ~6% better on two words, 10× worse on
  eight (176 ns → 1717 ns).  `Builder.run` owns its accumulator uniquely and
  extends it in place; `e ++ w₁ ++ w₂ ++ …` does not, and copies per step.
* **A word is one `chunk` leaf, in both `putUint` branches.**  `word32Small`
  skips computing the 24 leading zero bytes of a small word, and the obvious
  spelling — `Builder.zeros 24 ++ Builder.chunk …`, reusing the `zeros` run —
  is 1.53× on `bytes[]` but **1.37× slower** on `bool[]`: the extra `append`
  node and second `emit` step cost more than the pushes they save.  Keep the
  two shapes identical.
* **Benchmark rows must thread the iteration index into the work.**  Lean
  floats closed subterms to cached top-level constants, so
  `timed n (fun _ => f topLevelData)` evaluates `f` once and then times a
  field read — an early draft of `Bench`'s word-codec section reported 32000
  `ByteArray.push`es in "3 ns".  Closing over a function parameter is safe;
  writing against top-level definitions is not, and the index must reach the
  loop, not just the returned sum.  The mirror hazard, when writing a probe:
  a shared accumulator threaded through `Id.run` can lose unique ownership
  and copy per push (830 ns/word against a real 86).  Mirror the structure of
  the code under test rather than inventing a tighter loop.
* **The static/dynamic choice lives in exactly one place per direction** —
  `Acc.static`/`Acc.dyn` when writing, `elemStatic`/`elemDyn` when reading.
  Everything above them (the loop, the tuple chain, the clause lemmas) is
  written once and takes the instruction as a parameter, with `Acc.Step` as
  the contract on the writing side.  Resist re-splitting them: that is how the
  four `denotes_*` and four loop lemmas this file used to carry appeared.

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
