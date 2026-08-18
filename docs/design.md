# abi-lean Design Report

## Abstract

`abi-lean` is a formally verified implementation of the Ethereum Contract ABI
encoding and decoding specification in Lean 4.  The central result is a
**roundtrip theorem** covering the full ABI type grammar — static primitives,
dynamic bytes/string, fixed- and dynamic-size arrays, and nested tuples —
with no unproven cases (`sorry`).  This report describes the design
decisions, architecture, technical challenges, and proofs that make the
result possible.

## 1. Context

### 1.1 EVM ABI

The Solidity ABI defines a deterministic encoding for function call data
sent to Ethereum contracts.  Every value is encoded as a sequence of 32-byte
words.  The encoding distinguishes *static* types (whose in-place encoding
size is known from the type alone) from *dynamic* types (whose size varies
at runtime).  Dynamic types employ a **head/tail layout**: the head contains
a 32-byte offset word pointing to the tail, which holds the actual data.

### 1.2 The Verification Problem

A correct ABI implementation must satisfy

```
Spec.decode (Spec.encode v) = v
```

for every value `v` of every valid type.  This statement is **tight**: it
is genuinely false for encodings whose offset words would overflow `2^256`
(such encodings are rejected at the Ethereum protocol layer, so the bound is
not an artifact of the proof).  The theorem must therefore carry an explicit
size hypothesis.

### 1.3 Prior Art

Existing ABI libraries (in Rust, Go, TypeScript, Python) are tested against
spec vectors but carry no machine-checked proof of correctness.  This
project provides the first full formal verification of ABI roundtrip for the
complete type grammar.

## 2. Contributions

1. **Full type universe.**  `Ty` covers `uintM`, `intM`, `bool`, `address`,
   `bytesM`, `bytes`, `string`, `T[]`, `T[k]`, and `(T₁,…,Tₙ)`.  Nesting
   is unrestricted (e.g., `string[][]`, `(uint256, (bool, bytes))[]`).

2. **Type-indexed value family.**  `Val : Ty → Type` is an indexed family of
   refined types: `Val (.uint 256) = {n : Nat // n < 2^256}`,
   `Val (.bytes) = List UInt8`, and compound types are structurally
   composed from their components.  The roundtrip statement
   `Spec.decode t (Spec.encode t v) = some v` needs no separate well-formedness
   predicate on values — the refinement is built into the type.

3. **Unified roundtrip theorem.**  A single theorem `roundtrip` covers every
   valid type, proved by structural induction on `Ty`.  The proof reduces
   each compound case (array, fixed array, tuple) to a sequence of component
   reads, each of which roundtrips by the induction hypothesis.

4. **Head/tail combinator library.**  `Parts` provides a generic framework
   for head/tail layouts: `Part` structures, `encodeParts`,
   offset-computation lemmas (`wordAt_offset`, `drop_tailOffset`), and
   well-formedness (`WF`).  The ABI codec is built on top of this library,
   keeping layout arithmetic isolated from type-specific encoding logic.

5. **Appended-buffer read lemmas.**  Every primitive decoder is proved to
   read its value from the front of a buffer and ignore a trailing suffix
   (`decodeUint_append` and friends).  This property is essential for
   decoding compound types: a component's encoding is embedded inside a
   larger buffer, and the decoder must not be confused by data that follows.

6. **The linear canonical decoder.**  The decoder `Spec.decode` walks a buffer
   with two monotonic cursors (the head section and the tails), threading
   an *expected tail frontier*: a dynamic component's offset word must
   point to tails laid out contiguously, in order, immediately after the
   head — so every byte is touched at most once, and the frontier check
   doubles as the strictness check.  The walkers (`decodeElem`,
   `decodeElems`, `decodeTuple`) are `Get2` programs (`EvmAbi.Builder`).
   The predicate `Spec.IsCanonical` (exact consumption, no trailing garbage)
   and the strict decoder `Spec.decodeStrict` are built on top; the theorem
   families are the roundtrips (`Spec.decode_roundtrip`: every `Spec.encode`
   decodes back), the soundness (`Spec.decode_sound`: the decoder only
   produces encodings), and the capstones `Spec.isCanonical_iff` /
   `Spec.decodeStrict_eq_some_iff` (canonical buffers are precisely the image
   of `Spec.encode`).

7. **Packed ABI encoding.**  `EvmAbi.Packed` implements Solidity's
   non-standard packed mode: scalars are concatenated at their tight
   widths, dynamic types (`bytes`, `string`, `T[]`) are encoded in place
   without length words, and array *elements* keep their standard padded
   32-byte-word layout.  Structs and nested arrays are not supported by
   Solidity; `PackedSupported` marks the conformant fragment.  Packed
   encoding is ambiguous without lengths, so only the static fragment is
   decodable — `roundtrip_packed_static` proves its roundtrip.

8. **One encoder, two materializations.**  The encoder is written against
   a `Builder` abstraction (`O(1)` concatenation, cached size, one-pass fill
   into a pre-sized `ByteArray`).  `Spec.encode = (put t v).toList` is the
   specification the proofs are stated over; `Spec.encodeByteArray = (put t v).run`
   is the same builder run for real, and
   `data_toList_encodeByteArray : (Spec.encodeByteArray t v).data.toList = Spec.encode t v`
   ties them.  Proofs stay on `List UInt8`; execution never builds one.
   2.9× faster on flat values and asymptotically faster on nested ones (§3.7).

9. **An ABI compiler.**  `abi_codec foo "…"` (`EvmAbi.Compile.Meta`) reads a
   type at elaboration time and emits Lean code specialised to it in both
   directions — straight-line for tuples, one loop for arrays, offsets folded
   to numerals — together with machine-checked theorems that the emitted
   encoder agrees with `encode` and the emitted decoder with `decodeStrict`.
   The emitted code targets small abstract machines (`EvmAbi.Compile`,
   `EvmAbi.Compile.Decode`) whose instructions are proved correct once, so the
   emitter only ever applies existing lemmas; nothing it prints is trusted
   (§3.8).

The **runtime layer** (`EvmAbi.Codec`) is the user-facing side:
`encode` (`ValBA` values → `ByteArray`), `decode` / `decodeStrict`
(`ByteArray` → `ValBA` values) and `IsCanonical`.  Its encoder is the same
layout over packed payloads, and `toList_putBA` proves it denotes the spec
encoder of the denotation, so the `Spec` theorems transport by rewrite.

## 3. Core Design

### 3.1 Type Universe (`Ty.lean`)

The type grammar is an inductive `Ty` with ten constructors.  Four
auxiliary predicates/functions are defined alongside it:

- **`Valid`** — size-parameter constraints (e.g., `uintM` requires `8∣M`,
  `8≤M≤256`).  Defined as a `Prop` with a `Decidable` instance.  A dynamic
  array additionally requires `0 < t.headSize` of its element type: an
  element occupying no head (`()`, `T[0]`) would let a 32-byte length word
  name arbitrarily many elements, leaving the decoder's element walk
  bounded by nothing.  The specification has no such types, and `Spec.decode`
  and the human-readable parser both reject them.

- **`isStatic`** — whether the encoding size is fixed by the type (a `Bool`
  predicate, lowercase per Lean convention).  Used by the head/tail layout:
  static elements sit inline in the head; dynamic elements contribute an
  offset word.

- **`headSize`** — bytes occupied in the head section.  Static types take
  their full encoding size; dynamic types take 32 (the offset word).

- **`packedSize`** — bytes occupied in packed encoding.  Scalars take
  their tight width (`uint8` → 1, `address` → 20); fixed arrays take `n`
  *padded* element slots (`uint8[3]` → 96), since Solidity pads packed
  array elements; for dynamic types it is 0 (packed size is not
  statically known, and `decodePacked` rejects them).

All are defined via **mutual recursion** with their `List`-indexed
siblings (`AllValid`, `allStatic`, `headSizeSum`, `packedSizeSum`).  This
avoids well-founded recursion (`Acc.rec`), which would make the predicates
opaque to the elaborator and break `@[reducible]` on `Val`.

### 3.2 Value Family

`Val` is a `@[reducible] def` that computes the type of values for each ABI
type:

```
Val (.uint m)     = {n : Nat // n < 2^m}
Val (.bytes)      = List UInt8
Val (.tuple ts)   = TupleVal ts          -- right-nested product
Val (.array t)    = List (Val t)
Val (.fixedArray t n) = {vs : List (Val t) // vs.length = n}
```

`TupleVal` is also `@[reducible]` and defined mutually with `Val`:

```
TupleVal []        = Unit
TupleVal (t :: ts) = Val t × TupleVal ts
```

This design gives definitional reduction — `Val (.uint 8)` *is*
`Subtype (fun n => n < 2^8)` — so dependent pattern matching in
`Spec.encode`/`Spec.decode` sees through the index.

Dynamic payloads (`bytes`, `string`, `T[]`) carry a `< 2^64` length bound
in their subtype, and the decoders enforce it — see `Ty.Val` for why that
is tighter than soundness needs.

### 3.3 Spec Codec Architecture (`Spec.lean`)

Encoding and decoding are defined by structural recursion on `Ty`:

- **`Spec.encode t v`** dispatches on the type.  Base types call the standalone
  codecs from `Static`/`Dynamic`.  Compound types construct a `Part` list
  (via `partOf` / `partsOfTuple`) and delegate to `encodeParts`.

- **`Spec.decode t buf`** is the linear canonical decoder, in prefix form: it
  returns the value together with the bytes it consumed and the untouched
  remainder (`Option (t.Val × Nat × List UInt8)`), so nested components
  are prefixes of their parent's buffer.  Its walkers (`decodeElem` /
  `decodeElems` / `decodeTuple`) are `Get2` programs: a head cursor and a
  tail cursor advance monotonically while an expected tail frontier is
  threaded — a dynamic component's offset word must equal the frontier
  exactly, and static components decode inline from the head.

  The consumed count is what keeps the walk linear.  It is computed
  *structurally* — 32 for the word types, the count `decodeBytesPrefix`
  already reports for the payload types, and the walker's own final
  frontier for the compound types — so `decodeElem` advances the frontier
  by an addition rather than by measuring the cursors.  Deriving it as
  `tails.length - rest.length` instead would cost `O(remaining)` per
  dynamic component, i.e. `O(n²)` for the whole buffer.

The codec is **mutually recursive** with its component-level helpers
(`partOf`, `decodeElems`, etc.), each assigned an explicit `termination_by`
measure.  `Spec.decodeStrict` is `Spec.decode` plus an exact-consumption check (no
trailing garbage).

### 3.4 Head/Tail Combinator (`Parts.lean`)

`Parts` is a standalone library providing:

- **`Part`** — a triple `(head : List UInt8, tail : List UInt8, isDyn : Bool)`.
- **`encodeParts`** — given a list of parts, lays out the head section
  (concatenating static heads and writing offset words for dynamic ones) and
  the tail section (concatenating dynamic tails).
- **Offset theorems:** `drop_headOffset_static`,
  `drop_tailOffset_append`, `wordAt_offset_append`.

The ABI codec uses `Parts` only for compound types; base types have their
own standalone encoding for efficiency and simplicity.

### 3.5 Packed ABI (`Packed.lean`)

Solidity's non-standard packed mode obeys four rules: scalars shorter
than 32 bytes are concatenated without padding; dynamic types are encoded
in place and without the length; array *elements* are padded (standard
32-byte-word layout), but still encoded in place; structs as well as
nested arrays are not supported.  The module provides:

- **Primitive packed codecs** — `encodeUintPacked` / `decodeUintPacked`,
  etc., operating at the element's natural byte width (`m/8` for `uintM`,
  1 for `bool`, 20 for `address`, `n` for `bytesN`).  Non-byte-aligned
  widths are rejected at decode (the encoder would truncate them).

- **Type-indexed packed codec** — `encodePacked : (t : Ty) → t.Val →
  List UInt8` (total) and `decodePacked : (t : Ty) → List UInt8 →
  Option t.Val`.  The codec mirrors the standard one: the encoder is a
  `Builder` chunk tree (`putPacked`, materialized once by `toList`)
  and the decoder is a single linear pass with `Get2` walkers
  (`decodePackedElem` / `decodePackedTuple`; the tail cursor and frontier
  are inert in packed layouts).  Scalars pack tight; `bytes`/`string`
  pack as their raw payload; array elements are standard-encoded
  (`Spec.encode`, padded words) and read back by the standard `decodeElems`
  (bound-free for static element types); tuples concatenate — the
  `.tuple` arm models the flat argument list of a multi-argument
  `abi.encodePacked(a, b, …)` call, and on nested tuples is a documented
  non-Solidity extension.  `PackedSupported` marks the conformant
  fragment.

- **Static roundtrip** — `roundtrip_packed_static`: every static value
  decodes from its own packed encoding.  The lemmas are stated in `Get2`
  `.run` form (`decodePackedElem_append` / `decodePackedTuple_append`),
  and array elements ride on the standard codec's bound-free static
  roundtrip (`decodeElems_static_append`).

Dynamic types encode but do not decode: packed encoding provides no
mechanism to delimit variable-length elements, so `decodePacked` returns
`none` for them rather than guessing.

### 3.6 Decoder Proof Structure

The decoder's theorems live in `Spec.lean` alongside the encoder; each
theorem family is a self-contained `mutual` block, so the later families
were moved to sibling modules: `Spec.Roundtrip`, `Spec.Sound`,
`Spec.Strict`.

| Section | Module | Content |
|---|---|---|
| Encoder packages A/B | `Spec` | Head sizes, static encoding lengths, alignment (`encode_length_static`, `wf_map_partOf`) |
| Package C | `Spec` | Appended-buffer read lemmas (`decodeUint_append`, …) and the layout lemmas `drop_headPartOf_static` |
| Package D | `Spec` | Locating dynamic tails (`drop_tail_partOf_dynamic`, `natAt_offset_partOf_dynamic`) |
| Decoder helpers | `Spec` | Head-size and word-recovery lemmas the decoder proofs need |
| **Static delegation** | `Spec` | `decode_static_append` family — static types carry no offset words, so the roundtrips are bound-free |
| **Roundtrip** | `Spec.Roundtrip` | `decode_roundtrip` family — every encoding decodes back, leaving the suffix untouched |
| **Soundness** | `Spec.Sound` | `decode_sound` family — the decoder only produces encodings |
| **Strict API** | `Spec.Strict` | `Spec.decodeStrict`, `Spec.IsCanonical`, and the capstones |
| **Runtime codec** | `Codec` + `Codec.ByteArray` | `encode`/`decode`/`decodeStrict`/`IsCanonical` over `ByteArray` and `ValBA`; the offset primitives (`natAtBA`, `windowList`), the `ValBA` walkers, the private `decodeBA` proof bridge, and the agreement family (`decodeBAVal_eq`, `decodeStrictBAVal_eq`, `decodeStrictBA_eq`) that carries the rows above onto the `ByteArray` side |

**Static delegation** is the first milestone: for static types the frontier
never moves and the tail cursor is never read, so the roundtrips hold
without the `2^256` bound.  The array and tuple cases use
`decodeElems_static_append` / `decodeTuple_static_append`.

**Roundtrip** extends this to dynamic types: a dynamic component's offset
word equals the frontier for free on encodings (the `putParts` offset
correctness theorems), so the frontier check costs nothing.  The proof
threads the frontier invariant `E = tailOffset …` and advances it by each
component's tail size (`tailOffset_snoc`), needing the `hb` bound only so
offset words cannot wrap.

**Soundness** is the mirror: whenever the decoder succeeds, the consumed
front of the buffer is exactly the encoding of the decoded value —
`Spec.decode t buf = some (v, rest)` implies `Spec.encode t v ++ rest = buf`.

Both families factor their per-component work into a *step* lemma
(`decodeElem_roundtrip`, `decodeElem_sound_static`/`_dynamic`) that the
element and tuple walkers share.  The step owns the static/dynamic case
split; the walkers only enumerate parts and advance the head offset via
`headSizes_snoc_partOf`, which holds for static and dynamic components
alike.

**Package E** instantiates the prefix roundtrip with an empty suffix,
yielding the user-facing `roundtrip` theorem.

### 3.7 Builder and Executable Encoder (`Builder.lean`)

`List UInt8` is the right specification type and the wrong runtime type: a
cons cell and a boxed `UInt8` per byte, and — worse — `Spec.encode` is built from
`++`, so a value nested `d` levels deep has its bytes re-copied once per
level, `O(n · d)`.  Rewriting `Spec.encode` over `ByteArray` would fix the
representation but not the concatenation: persistent `a ++ b` still builds a
third array.  (Appending onto a uniquely-owned accumulator — what
`Chunks.emit` does — is linear; see `Builder.lean`.)

The fix is the builder pattern (Haskell's `Data.Binary.Builder`): make
concatenation free by not concatenating.

**`Builder.lean`** is ABI-agnostic.  `Chunks` is a tree with three kinds of
leaf — a literal byte list, a `ByteArray` chunk (so `String.toUTF8` payloads
are never unpacked), and a run of `n` zero bytes (so padding is never
materialised) — plus an `append` *constructor*, which is what makes
concatenation `O(1)`.  `Builder` wraps that tree with its **cached** byte
count:

```lean
structure Builder where
  chunks  : Chunks
  size    : Nat
  size_eq : size = chunks.toList.length
```

The cache is not an optimisation detail.  The head/tail scheme needs the size
of every tail in order to write the offset words, so a `size` that walked the
tree would put the `O(n · depth)` cost straight back — an earlier draft did
exactly that and was *slower* than the specification encoder.  `size_eq` is a
`Prop`: erased at run time, and no `Builder` can lie about its size.
`Builder.run` then allocates `size` bytes up front and emits into them with
`ByteArray.push`, both `@[extern]` primitives — one linear pass, no
intermediate lists.

There is no second encoder to keep in step: `put` — the `Builder`-valued
encoder `Spec.lean` already defines — *is* the executable one.  The two
entry points are its two materializations,

```lean
-- in `namespace EvmAbi.Spec`
def encode          (t : Ty) (v : t.Val) : List UInt8 := (put t v).toList
def encodeByteArray (t : Ty) (v : t.Val) : ByteArray  := (put t v).run
```

and `Builder.data_toList_run` bridges them directly:

```lean
theorem data_toList_encodeByteArray (t : Ty) (v : t.Val) :
    (Spec.encodeByteArray t v).data.toList = Spec.encode t v
```

That is the entire bridge — no mirrored definitions, no mutual induction
relating them.  Every result about `Spec.encode` transports by rewriting, so
`decode_encodeByteArray`, `decode_encodeByteArray_static`,
`isCanonical_encodeByteArray` and `decodeStrict_encodeByteArray` are three
lines each in `Spec/Strict.lean`.  The runtime encoder over `ValBA` is the
same layout with `chunk` leaves, and `toList_putBA` gives the analogous
bridge to `Spec.encode` (`EvmAbi.Codec`).

The one place the layout touches the builder's *representation* rather than
its denotation is `Part.headSize`/`tailSize` and `putHeads`, which read the
cached `size`.  `Builder.size_eq_length_toList` rewrites that back to
`toList.length`, so every statement stays on the specification side.

Measured by `Bench.lean` (compiled; the win rests on the `@[extern]`
`ByteArray` primitives, so interpreted runs show the opposite): 2.9× on flat
`bytes[]` values, and 16×/53× at tuple nesting depth 50/200, where the
specification encoder is quadratic and the builder linear.

### 3.8 The ABI Compiler (`Compile.lean`, `Compile/Decode.lean`, `Compile/Meta.lean`)

The encoder of §3.7 is interpretive.  For a *fixed* type, everything it
decides at run time is already known:

```
putBA          matches on the Ty                      -- once per value
partOfBA       asks t.isStatic                        -- once per component,
                                                      -- and per array element
partsOfTupleBA allocates a List Part                  -- once per tuple/array
putParts       walks that list three times            -- headSizes, putHeads,
                                                      -- putTails
```

A compiler can settle all of it at elaboration time.  The design question is
what the emitted code should be written *in*, because that decides what its
correctness proof costs.  Emitting raw `Builder` expressions and closing the
goal with a large `simp` would make every compiled type a fresh proof-search
problem; the answer here is to give the compiler a **target language whose
instructions are already proved**.

`EvmAbi.Compile` is that language: a three-register machine for the head/tail
layout.

```lean
structure Acc where
  head : Builder   -- head section so far
  off  : Nat       -- offset the next dynamic tail will occupy (the frontier)
  tail : Builder   -- tail section so far

def start  (H : Nat) : Acc            -- open a layout with an H-byte head
def static (s : Acc) (b : Builder)    -- inline a static component
def dyn    (s : Acc) (b : Builder)    -- write the frontier, append to tails
def finish (s : Acc) : Builder        -- head ++ tails
```

`Acc.Inv H s ps` says the state `s` is exactly what `putHeads`/`putTails`
would have built from the parts `ps`, and each instruction has one lemma:
`Inv.static` and `Inv.dyn` extend `ps` by one part, `Inv.finish_toList` closes
the layout once `ps` is all of it.  One loop (`elems`) runs one instruction
per array element — an array is homogeneous, so *which* instruction is decided
at compile time, and the loop is the only recursion left in compiled code.

The contract is a single definition:

```lean
def Denotes (t : Ty) (f : ValBA t → Builder) : Prop :=
  ∀ v, (f v).toList = (putBA t v).toList
```

and the clause lemmas compose it: `denotes_array` turns `Denotes t f` — plus
the instruction the elements are written with, `Acc.Step t step f` — into
`Denotes (.array t) (fun v => putUint v.val.length ++ …)`, and so on for each
constructor.  `run_eq_encode` then lifts a `Denotes` to the user's
statement, `f v |>.run = encode t v` — note this is a `toList` equality
throughout, because `Builder.append` is a constructor and the machine's
appends associate to the left where the generic layout's associate to the
right.  The two denote the same bytes; they are not the same tree.

The decoder half (`Compile/Decode.lean`) is the mirror image.  `Reads t g`
says `g` answers what `decodeBAVal t` answers; `elemStatic`/`elemDyn` are the
two branches of `decodeElemBAVal` with the sub-decoder taken as a parameter,
and they are the only place that choice survives compilation — `cons` chains
one of them onto the reader for the remaining components (so a compiled tuple
is a nest of combinators with no `Ty` in it) and `elems` runs one per array
element; `readArray`/`readFixedArray`/`readTuple` are the three recursive
clauses of `decodeBAVal` with their head sizes taken as *parameters*.  That last point is the decoder's version of the head-size
constant: the emitter passes a numeral and the lemma demands `rfl` against
`Ty.headSize`, so the constant is checked, not assumed.  `runStrict_eq` then
lifts a `Reads` to the user's statement about `decodeStrict`.

`EvmAbi.Compile.Meta` is then a *printer*.  For each compound sub-type it
emits a definition and the theorem `Denotes ty node` (or `Reads ty dnode`),
whose proof is the matching clause lemma applied to the sub-nodes' theorems;
leaves are inlined.  For a tuple it emits one `static`/`dyn` per component —
one `cons` when decoding — and chains the instruction lemmas in the same
order.  It never constructs a proof step of its own, and the
kernel checks each theorem as it is emitted, so a compiled codec that
disagrees with the verified one cannot be produced; the command fails
instead.

Two things are worth stating plainly.  First, this is *not* a verified
compiler in the CompCert sense: there is no theorem quantifying over all
inputs of the emitter, because the emitter is a metaprogram and Lean has no
such theorem to state.  What is proved is every output, individually, by
construction — a certificate per compilation, which for a code generator whose
outputs are all checked is the same guarantee where it matters.  Second, the
head-size constant the compiler folds into `Acc.start` is justified, not
assumed: `headSizes_partsOfTupleBA` (which needs `AllValid ts`, discharged by
`decide` at compile time) proves the numeral is the head section's real size.

Measured (`Bench.lean`, compiled): encoding 2.2× on `(bool × 8)` and 1.8× on
`bool[100]`, decoding 1.8× and 1.4× on the same, where the words are cheap and
the layout is the work; 1.02–1.19× on `uint256`/`bytes` shapes, where
`Binary`'s word codec (~700 ns per full-width word, against tens of
nanoseconds of layout) dominates and there is little left to remove.

The instructions are `@[inline]` and the loops `@[specialize]`, and both
matter: an instruction is a three-field state, so folding it into the loop
body is the difference between building a state per element and updating one.
It is also why the readers are passed to `cons`/`elems` as the *maker*
(`elemStatic`/`elemDyn`) plus the component's decoder rather than as a built
`GetBA` — a structure argument is opaque to the specialiser, and passing one
costs ~10 ns per component.

**Reading the generated code.**  `abi_codec foo "…" trace` prints every
definition and theorem the emitter writes, as it writes it — the raw syntax,
before elaboration.  The transcript *is* the compiler's behaviour made
visible.  For `transfer(address to, uint256 amount)` the encoder is:

```lean
def callArgs.put : EvmAbi.ValBA (EvmAbi.Ty.tuple [EvmAbi.Ty.address, EvmAbi.Ty.uint 256]) → EvmAbi.Builder :=
  fun v =>
  (((EvmAbi.Compile.Acc.start 64).static (EvmAbi.putAddress (v.1).val)).static
      (EvmAbi.putUint (v.2.1).val)).finish

theorem callArgs.put_denotes :
    EvmAbi.Compile.Denotes (EvmAbi.Ty.tuple [EvmAbi.Ty.address, EvmAbi.Ty.uint 256]) callArgs.put :=
  by
  intro v
  refine EvmAbi.Compile.toList_tuple (by decide) _ ?_
  simp only [EvmAbi.Compile.partsOfTupleBA_cons, EvmAbi.Compile.partsOfTupleBA_nil]
  exact
    ((EvmAbi.Compile.Acc.start_inv 64).static (by decide) (EvmAbi.Compile.denotes_address (v).1)).static (by decide)
      (EvmAbi.Compile.denotes_uint 256 (v).2.1)
```

Every decision the type made available is already taken.  The head section
is a numeral — `Acc.start 64` — where the generic encoder would compute
`headSizeSum` at run time.  The components are straight-line `static`
instructions (both happen to be static; a `bytes` argument would read
`dyn`) whose bodies are the leaf codecs, and the value is reached by the
projections `v.1`, `v.2.1`, … rather than by matching a `Ty`.  `finish`
closes the layout.  The theorem below it is the whole correctness story: one
clause lemma of `EvmAbi.Compile` per instruction — `Acc.start_inv` for the
opening, `.static` for each component — applied to the leaf lemmas
(`denotes_address`, `denotes_uint`), with the tuple's parts list closed by
the two `partsOfTupleBA` equations.  Nothing here was found by proof search;
it is the emitter's output, and the kernel checks it as it is emitted.

The decoder is the mirror image:

```lean
def callArgs.read : ByteArray → Nat → Option (EvmAbi.ValBA … × Nat) :=
  EvmAbi.Compile.Decode.readTuple 64
    (EvmAbi.Compile.Decode.cons EvmAbi.Compile.Decode.elemStatic EvmAbi.Compile.Decode.readAddress
      (EvmAbi.Compile.Decode.cons EvmAbi.Compile.Decode.elemStatic (EvmAbi.Compile.Decode.readUint 256)
        EvmAbi.Compile.Decode.consNil))
```

`readTuple 64` is the recursive clause of the generic decoder with its head
size taken as a *parameter*, `elemStatic` is the static branch of the element
step, and the `cons` chain links them; `consNil` ends the list.  The `Reads`
theorem is the corresponding chain of `reads_tuple`/`cons_eq`/`elemStatic_eq`
applications, the numeral checked against `Ty.headSize` by `rfl`.

The dynamic case shows where the work went.  `sam(bytes, bool, uint256[])`
emits two definitions, the array sub-type first because the emitter works
bottom-up:

```lean
def samArgs.node0 : EvmAbi.ValBA (EvmAbi.Ty.array (EvmAbi.Ty.uint 256)) → EvmAbi.Builder :=
  fun v =>
  EvmAbi.putUint v.val.length ++
    ((EvmAbi.Compile.Acc.start (v.val.length * 32)).elems EvmAbi.Compile.Acc.static
        (fun v => EvmAbi.putUint v.val) v.val).finish

def samArgs.put : EvmAbi.ValBA (EvmAbi.Ty.tuple [EvmAbi.Ty.bytes, EvmAbi.Ty.bool, …]) → EvmAbi.Builder :=
  fun v =>
  ((((EvmAbi.Compile.Acc.start 96).dyn (EvmAbi.Codec.putBytesBA (v.1).val)).static (EvmAbi.putBool (v.2.1))).dyn
      (samArgs.node0 (v.2.2.1))).finish
```

`node0` is the compiled encoder of the array sub-type; its single loop
(`Acc.elems Acc.static`) runs one instruction per element, and its proof is
one application of `denotes_array`.  The tuple then *calls* it —
`samArgs.node0 …` — instead of rebuilding it, which is why compound types
never duplicate code.  The `dyn` on the `bytes` and array components is the
static/dynamic decision made once at compile time: a dynamic component
writes its offset word and appends its payload to the tails, a static one
(`bool`) goes inline.  The head size `96` is three offset words, all static
components, in head order.  The `trace` transcript of a compiled codec is
thus a complete, machine-checked account of what the type decided.

## 4. Technical Challenges

### 4.1 Dependent Pattern Matching over `Val`

**Problem.**  `Val` is a dependent function `Ty → Type`.  In `Spec.encode` and
`Spec.decode`, the pattern match on `t` must reveal the structure of `t.Val` to
the elaborator.  Without reduction, `Val (.bytesN m)` is opaque, so a
pattern like `⟨bs, h⟩` cannot match it.

**Solution.**  `Val` is marked `@[reducible]` and defined in a `mutual`
block with `TupleVal`.  The mutual block ensures the recursion is
structurally visible, while `@[reducible]` forces definitional reduction
during elaboration.  This gives `Val (.bytesN m) = Subtype (λ bs => bs.length = m)`
and `Val (.tuple [t₁, t₂]) = Val t₁ × Val t₂ × Unit`, both definitionally.

### 4.2 Prefix-Tolerant Decoding

**Problem.**  In a compound type layout, individual element encodings are
concatenated.  A strict decoder that validates trailing padding (e.g.,
`decodeBytesN` checking that `buf.drop n` is all zeros) would fail when
the next element's data follows immediately.

**Solution.**  Every base-type decoder is proved **prefix-tolerant**: for
any `rest : List UInt8`, `Spec.decode t (Spec.encode t v ++ rest)` returns `v`, the
bytes it consumed, and `rest` untouched.  For
`bytes` and `string`, a separate prefix decoder `decodeBytesPrefix` returns
the decoded data *and* the number of bytes consumed, making composition
explicit.

### 4.3 Offset Arithmetic

**Problem.**  The head/tail layout involves computing byte offsets for the
tail of each dynamic part.  The proof that `Spec.decode` follows the correct
offset requires arithmetic on head sizes, tail sizes, and alignment (all
multiples of 32).  The plan anticipated "pure omega" for this; in practice,
many goals are closed by `omega`, but some require explicit lemmas about
`headSizes`, `tailSizes`, and their alignment properties (`dvd_headSizes`,
`dvd_headSizeSum`).

**Solution.**  Package B (`wf_map_partOf`, `wf_partsOfTuple`,
`encode_length_aligned`) proves that every part list produced by the codec
is well-formed (`WF`): each head and tail length is a multiple of 32.  These
facts feed directly into the offset-word correctness lemmas from `Parts`
(`wordAt_offset_append`, `drop_tailOffset_append`).

### 4.4 Mutual Recursion and Termination

**Problem.**  The codec involves multiple mutually-recursive functions
(`Spec.encode`/`partOf`/`partsOfTuple`, and the decoder `Spec.decode` with its `Get2`
walkers `decodeElem`/`decodeElems`/`decodeTuple`), each defined by pattern
matching on `Ty` or `List Ty`.
The default `decreasing_tactic` cannot always see through the list
destructuring.

**Solution.**  Every mutual block carries an explicit `termination_by`
measure (typically `sizeOf` with a constant offset to distinguish sibling
levels — the decoder's walkers sit at offsets `+1`/`+2`/`+3` above the
prefix `Spec.decode`, so a component step can call it on the same type).  The
measures are chosen so that recursive calls occur at strictly smaller
values, and the `decreasing_tactic` discharges every goal.

## 5. Architecture Diagram

```
┌──────────────────────────────────────────────┐
│                 Packed.lean                   │
│  encodePacked / decodePacked (mutual)         │
│  packed static roundtrip; array elements      │
│  reuse the linear decoder                     │
└──────────────────────┬───────────────────────┘
                       │
┌──────────────────────▼───────────────────────┐
│                  Spec.lean                    │
│  Spec.encode (mutual with partOf / partsOfTuple)   │
│  Spec.decode (Get2 walkers decodeElem/Elems/Tuple) │
│  roundtrip / soundness / static delegation    │
│  strict API (Spec.decodeStrict, Spec.IsCanonical)       │
└──────────┬──────────────┬────────────────────┘
           │              │
    ┌──────▼──────┐  ┌───▼──────────┐
    │ Static.lean  │  │ Parts.lean    │
    │ Dynamic.lean │  │ (head/tail)   │
    │ (primitives) │  │               │
    └──────┬───────┘  └───┬───────────┘
           │              │
    ┌──────▼──────┐  ┌───▼──────────┐
    │   Ty.lean    │  │  Word.lean    │
    │  (universe)  │  │  Align.lean   │
    │              │  │  Bytes.lean   │
    └─────────────┘  └───────────────┘

┌──────────────────────────────────────────────┐
│      Compile.lean + Compile/Meta.lean         │
│  the layout machine (Acc / Acc.Inv) and        │
│  Denotes; abi_encoder emits code against it,   │
│  one lemma application per instruction         │
└──────────────────────┬───────────────────────┘
                       │  proved against putBA

              ┌──────────────────────────┐
              │      Builder.lean         │
              │  Chunks / Builder:        │
              │  O(1) ++, cached size,    │
              │  toList denotation,       │
              │  run -> ByteArray;        │
              │  Get2 dual-cursor reader  │
              │  (ABI-agnostic)           │
              └──────────────────────────┘
   used by Static/Dynamic/Parts to build, and by Codec to read
```

## 6. Future Work

### Runtime Value Family (`ValBA`) — done

The decoder still reads payloads through `windowList`, which copies a
field's bytes into a `List UInt8` because that is what `Ty.Val .bytes`
is.  `EvmAbi.ValBA` is the value family with packed payloads
(`ValBA .bytes = {bs : ByteArray // …}`), and `EvmAbi.Codec.ByteArray`
and `EvmAbi.Codec` write their runtime walkers against it:
`decodeStrict` (the runtime strict decoder) decodes with one `extract`
(a memcpy) per payload instead of ~two allocations per byte, and `encode` emits a
`chunk` memcpy instead of a per-byte push and never walks a length.

`ValBA.toList` maps every packed value to its `Ty.Val` denotation, and
the decoder agreement family (`decodeBAVal_eq`, `decodeElemBAVal_eq`, …,
`decodeStrictBAVal_eq`) says every `ValBA` decode is the corresponding
`Spec` decode under that map, so the `List` capstones transport by one
rewrite.  The encoder side is closed too: `toList_putBA` proves `putBA`
denotes `Spec.put` of the denotation, so the runtime `encode` is byte-for-byte
the spec encoding of the same value.

Measured on flat `bytes[]` (500/2000 elements, same machine): `Spec.decodeStrict`
1118/4436 µs → **82/338 µs** (≈13×, at parity with go-ethereum's
reflection decoder); `Spec.encode` 618/2507 µs → **283/1173 µs**.  The two
value families are one value family materialized two ways, like `Spec.encode`
and `Spec.encodeByteArray`.

### Faster Word Encoding — done, upstream

`encodeUint` goes through `Binary.encodeBEU`, which used to peel one byte at a
time with `n / 256` and `n % 256`.  Above `2 ^ 63` a `Nat` is a GMP bignum and
each of those allocates, so one EVM word cost 32 GMP calls — about 4.8 µs,
against ~30 ns for the list plumbing around it.  Every ABI word paid it.

The fix landed in `lean-binary` as `Binary.Fast`: peel eight bytes at a time
through a `UInt64`, proved equal to the definition and registered with
`@[csimp]`, so no definition, no theorem and no caller changed.  Measured on
`uint256[]` with 1000 full-width words, `Spec.encodeByteArray` went 4961 µs → 997 µs
(5.0×) and the specification encoder 5323 µs → 1307 µs, since the fix sits
below both.

### Compiling Further

The compiler emits Lean.  Two directions follow.

*A tighter target — measured, and rejected.*  For an all-static type the total
size is a compile-time constant, so the encoding looks like it could be written
straight into a pre-sized `ByteArray` with no builder and no machine state at
all.  Measured against the compiled builder path on the same values, that is
~6% faster on `(address, uint256)` and **10× slower** on `(bool × 8)`
(176 ns → 1717 ns).  `Builder.run` allocates once and appends into an
accumulator it uniquely owns, so each append extends it in place; an expression
chain `e ++ w₁ ++ w₂ ++ …` does not preserve that ownership and the accumulator
is copied per step.  The builder already *is* the tight target; what is left in
those rows is the word codec, not the layout.  (Not isolated to the refcount
level: a fold that threads the accumulator through a function, as `Chunks.emit`
does, may well behave differently from an expression chain.)

*EVM bytecode.*  The machine is deliberately first-order: `start`/`static`/
`dyn`/`finish` over a head cursor, a frontier and a tail cursor is a
description of what contract code does with memory.  Emitting EVM instead of
Lean means giving those four instructions a second backend — and, to prove
*that* backend, a semantics to relate them to, which is what
[EVMYulLean](https://github.com/NethermindEth/EVMYulLean) provides.

## 7. References

- [Solidity ABI Specification](https://docs.soliditylang.org/en/latest/abi-spec.html)
- [Ethereum Yellow Paper, Appendix H](https://ethereum.github.io/yellowpaper/paper.pdf)
- [Lean 4 Theorem Prover](https://lean-lang.org/)
