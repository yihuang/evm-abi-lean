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
decode (encode v) = v
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
   `decode t (encode t v) = some v` needs no separate well-formedness
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

6. **The linear canonical decoder.**  The decoder `decode` walks a buffer
   with two monotonic cursors (the head section and the tails), threading
   an *expected tail frontier*: a dynamic component's offset word must
   point to tails laid out contiguously, in order, immediately after the
   head — so every byte is touched at most once, and the frontier check
   doubles as the strictness check.  The walkers (`decodeElem`,
   `decodeElems`, `decodeTuple`) are `Get2` programs (`EvmAbi.Builder`).
   The predicate `IsCanonical` (exact consumption, no trailing garbage)
   and the strict decoder `decodeStrict` are built on top; the theorem
   families are the roundtrips (`decode_roundtrip`: every `encode`
   decodes back), the soundness (`decode_sound`: the decoder only
   produces encodings), and the capstones `isCanonical_iff` /
   `decodeStrict_eq_some_iff` (canonical buffers are precisely the image
   of `encode`).

7. **Packed ABI encoding.**  `EvmAbi.Packed` implements Solidity's
   non-standard packed mode: scalars are concatenated at their tight
   widths, dynamic types (`bytes`, `string`, `T[]`) are encoded in place
   without length words, and array *elements* keep their standard padded
   32-byte-word layout.  Structs and nested arrays are not supported by
   Solidity; `PackedSupported` marks the conformant fragment.  Packed
   encoding is ambiguous without lengths, so only the static fragment is
   decodable — `roundtrip_packed_static` proves its roundtrip.

## 3. Core Design

### 3.1 Type Universe (`Ty.lean`)

The type grammar is an inductive `Ty` with ten constructors.  Four
auxiliary predicates/functions are defined alongside it:

- **`Valid`** — size-parameter constraints (e.g., `uintM` requires `8∣M`,
  `8≤M≤256`).  Defined as a `Prop` with a `Decidable` instance.  A dynamic
  array additionally requires `0 < t.headSize` of its element type: an
  element occupying no head (`()`, `T[0]`) would let a 32-byte length word
  name arbitrarily many elements, leaving the decoder's element walk
  bounded by nothing.  The specification has no such types, and `decode`
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
`encode`/`decode` sees through the index.

### 3.3 Codec Architecture (`Codec.lean`)

Encoding and decoding are defined by structural recursion on `Ty`:

- **`encode t v`** dispatches on the type.  Base types call the standalone
  codecs from `Static`/`Dynamic`.  Compound types construct a `Part` list
  (via `partOf` / `partsOfTuple`) and delegate to `encodeParts`.

- **`decode t buf`** is the linear canonical decoder, in prefix form: it
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
measure.  `decodeStrict` is `decode` plus an exact-consumption check (no
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
  Option t.Val`.  Scalars pack tight; `bytes`/`string` pack as their raw
  payload; array elements are standard-encoded (`encode`, padded words)
  and read back with the standard `decode`; tuples concatenate — the
  `.tuple` arm models the flat argument list of a multi-argument
  `abi.encodePacked(a, b, …)` call, and on nested tuples is a documented
  non-Solidity extension.  `PackedSupported` marks the conformant
  fragment.

- **Static roundtrip** — `roundtrip_packed_static`: every static value
  decodes from its own packed encoding.  Array elements ride on the
  standard codec's bound-free static roundtrip `decode_static_append`;
  only the scalar and tuple walks need packed-specific lemmas.

Dynamic types encode but do not decode: packed encoding provides no
mechanism to delimit variable-length elements, so `decodePacked` returns
`none` for them rather than guessing.

### 3.6 Decoder Proof Structure

The decoder's theorems live in `Codec.lean` alongside the encoder; each
theorem family is a self-contained `mutual` block, so the later families
were moved to sibling modules: `Codec.Roundtrip`, `Codec.Sound`,
`Codec.Strict`.

| Section | Module | Content |
|---|---|---|
| Encoder packages A/B | `Codec` | Head sizes, static encoding lengths, alignment (`encode_length_static`, `wf_map_partOf`) |
| Package C | `Codec` | Appended-buffer read lemmas (`decodeUint_append`, …) and the layout lemmas `drop_headPartOf_static` |
| Package D | `Codec` | Locating dynamic tails (`drop_tail_partOf_dynamic`, `natAt_offset_partOf_dynamic`) |
| Decoder helpers | `Codec` | Head-size and word-recovery lemmas the decoder proofs need |
| **Static delegation** | `Codec` | `decode_static_append` family — static types carry no offset words, so the roundtrips are bound-free |
| **Roundtrip** | `Codec.Roundtrip` | `decode_roundtrip` family — every encoding decodes back, leaving the suffix untouched |
| **Soundness** | `Codec.Sound` | `decode_sound` family — the decoder only produces encodings |
| **Strict API** | `Codec.Strict` | `decodeStrict`, `IsCanonical`, and the capstones |

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
`decode t buf = some (v, rest)` implies `encode t v ++ rest = buf`.

Both families factor their per-component work into a *step* lemma
(`decodeElem_roundtrip`, `decodeElem_sound_static`/`_dynamic`) that the
element and tuple walkers share.  The step owns the static/dynamic case
split; the walkers only enumerate parts and advance the head offset via
`headSizes_snoc_partOf`, which holds for static and dynamic components
alike.

**Package E** instantiates the prefix roundtrip with an empty suffix,
yielding the user-facing `roundtrip` theorem.

## 4. Technical Challenges

### 4.1 Dependent Pattern Matching over `Val`

**Problem.**  `Val` is a dependent function `Ty → Type`.  In `encode` and
`decode`, the pattern match on `t` must reveal the structure of `t.Val` to
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
any `rest : List UInt8`, `decode t (encode t v ++ rest)` returns `v`, the
bytes it consumed, and `rest` untouched.  For
`bytes` and `string`, a separate prefix decoder `decodeBytesPrefix` returns
the decoded data *and* the number of bytes consumed, making composition
explicit.

### 4.3 Offset Arithmetic

**Problem.**  The head/tail layout involves computing byte offsets for the
tail of each dynamic part.  The proof that `decode` follows the correct
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
(`encode`/`partOf`/`partsOfTuple`, and the decoder `decode` with its `Get2`
walkers `decodeElem`/`decodeElems`/`decodeTuple`), each defined by pattern
matching on `Ty` or `List Ty`.
The default `decreasing_tactic` cannot always see through the list
destructuring.

**Solution.**  Every mutual block carries an explicit `termination_by`
measure (typically `sizeOf` with a constant offset to distinguish sibling
levels — the decoder's walkers sit at offsets `+1`/`+2`/`+3` above the
prefix `decode`, so a component step can call it on the same type).  The
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
│                  Codec.lean                   │
│  encode (mutual with partOf / partsOfTuple)   │
│  decode (Get2 walkers decodeElem/Elems/Tuple) │
│  roundtrip / soundness / static delegation    │
│  strict API (decodeStrict, IsCanonical)       │
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
```

## 6. Future Work

### ByteArray Interface

The library works entirely with `List UInt8` for proofs and `ByteArray`
only at the I/O boundary.  A future layer could lift the roundtrip theorem
to `ByteArray` without reproving, using a list/bytearray isomorphism lemma.

## 7. References

- [Solidity ABI Specification](https://docs.soliditylang.org/en/latest/abi-spec.html)
- [Ethereum Yellow Paper, Appendix H](https://ethereum.github.io/yellowpaper/paper.pdf)
- [Lean 4 Theorem Prover](https://lean-lang.org/)
