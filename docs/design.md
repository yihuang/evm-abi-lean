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

5. **Prefix-tolerant primitive decoders.**  Every base-type decoder is
   proved to read its value from the front of a buffer and ignore a trailing
   suffix (`decode_encode_append_static`).  This property is essential for
   decoding compound types: a component's encoding is embedded inside a
   larger buffer, and the decoder must not be confused by data that follows.

6. **Canonical-layout validation.**  Beyond the lenient decoder, an
   executable checker `validate` verifies that a buffer uses the strict ABI
   layout (offsets contiguous, in order, immediately after the head) and
   returns the number of bytes consumed.  The predicate `IsCanonical`
   additionally rejects trailing garbage; `decodeCanonical` combines both
   checks.  The C1–C3 theorem packages (`EvmAbi.Canonical`) prove
   completeness (every `encode` validates), soundness (validating buffers
   are precisely the image of `encode`), and a unified roundtrip for the
   strict decoder.

7. **Packed ABI encoding.**  `EvmAbi.Packed` implements Solidity's
   non-standard packed mode: scalars are concatenated at their tight
   widths, dynamic types (`bytes`, `string`, `T[]`) are encoded in place
   without length words, and array *elements* keep their standard padded
   32-byte-word layout.  Structs and nested arrays are not supported by
   Solidity; `PackedSupported` marks the conformant fragment.  Packed
   encoding is ambiguous without lengths, so only the static fragment is
   decodable — `roundtrip_packed_static` proves its roundtrip.

8. **Executable encoder with a proved bridge.**  A `Builder` abstraction
   (`O(1)` concatenation, cached size, one-pass fill into a pre-sized
   `ByteArray`) carries a second encoder whose only tie to the verified one
   is `toList_encodeB : (encodeB t v).toList = encode t v`.  Proofs stay on
   `List UInt8`; execution never builds one.  2.9× faster on flat values and
   asymptotically faster on nested ones (§3.7).

## 3. Core Design

### 3.1 Type Universe (`Ty.lean`)

The type grammar is an inductive `Ty` with ten constructors.  Four
auxiliary predicates/functions are defined alongside it:

- **`Valid`** — size-parameter constraints (e.g., `uintM` requires `8∣M`,
  `8≤M≤256`).  Defined as a `Prop` with a `Decidable` instance.

- **`IsStatic`** — whether the encoding size is fixed by the type.  Used by
  the head/tail layout: static elements sit inline in the head; dynamic
  elements contribute an offset word.

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

- **`decode t buf`** dispatches on the type.  Base types call their
  standalone decoders.  Compound types invoke `readElem` / `decodeElems` /
  `decodeTuple`, which walk the buffer element-by-element.

- **`readElem t buf off`** reads one element at head offset `off`.  For
  static types it decodes in place.  For dynamic types it reads the offset
  word at `off`, follows it, and decodes the tail.

The codec is **mutually recursive** with its component-level helpers
(`partOf`, `decodeElems`, etc.), each assigned an explicit `termination_by`
measure.

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
  standard codec's `decode_encode_append_static`; only the scalar and
  tuple walks need packed-specific lemmas.

Dynamic types encode but do not decode: packed encoding provides no
mechanism to delimit variable-length elements, so `decodePacked` returns
`none` for them rather than guessing.

### 3.6 Roundtrip Proof Structure

The proof is organized into five packages (A–E) in `Codec.lean`:

| Package | Content |
|---|---|
| A | Head sizes, static encoding lengths (`encode_length_static`) |
| B | Alignment and well-formedness (`encode_length_aligned`, `wf_map_partOf`) |
| C | **Static prefix roundtrip** — `decode_encode_append_static` for every static type, plus the step `readElem_partOf_append_static` and the walkers `decodeElems_static_append` / `decodeTuple_static_append` |
| D | **Full prefix roundtrip** — `decode_encode_append`, the step `readElem_partOf_append`, and the walkers `decodeElems_append` / `decodeTuple_append` for all types, dynamic elements included |
| E | **Top-level roundtrip** — `roundtrip` derived from Package D by supplying `rest := []` |

**Package C (static prefix)** is the first major milestone.  It proves that
a static value decodes from the front of its encoding even when arbitrary
data follows.  The proof is by induction on `Ty`; the array and tuple cases
use `decodeElems_static_append` and `decodeTuple_static_append`, which in
turn call `decode_encode_append_static` for each component.

**Package D (full prefix)** extends Package C to dynamic types.  For dynamic
components, `readElem` resolves the offset word and decodes from the tail,
using the Parts theorems `wordAt_offset_append` and
`drop_tailOffset_append` to locate the data.  The proof is again by
structural induction, now with the additional hypotheses `LenBound` (dynamic
payload sizes) and `hb` (total buffer size < `2^256`).

Both packages factor their per-component work into a *step* lemma
(`readElem_partOf_append`, `readElem_partOf_append_static`) that the element
and tuple walkers share.  The step owns the static/dynamic case split; the
walkers only enumerate parts and advance the head offset via
`headSizes_snoc_partOf`, which holds for static and dynamic components alike.
`Canonical.lean` follows the same shape in packages C1 and C3
(`validateElem_encode_append`, `segments_of_validateElem`).

**Package E** instantiates the prefix roundtrip with an empty suffix,
yielding the user-facing `roundtrip` theorem.

### 3.7 Builder and Executable Encoder (`Builder.lean`, `Encode.lean`)

`List UInt8` is the right specification type and the wrong runtime type: a
cons cell and a boxed `UInt8` per byte, and — worse — `encode` is built from
`++`, so a value nested `d` levels deep has its bytes re-copied once per
level, `O(n · d)`.  Rewriting `encode` over `ByteArray` would fix the
representation but not the concatenation, since `ByteArray` append copies too.

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

**`Encode.lean`** mirrors the encoder clause for clause: `PartB`/
`encodePartsB` mirror `Part`/`encodeParts` (with `PartB.toPart` as the
denotation), and `encodeB`/`partOfB`/`partsOfTupleB` mirror
`encode`/`partOf`/`partsOfTuple` with the same termination measures.  The
mirror is a *separate* definition rather than a refactor of `encode`, so no
existing proof changes; one mutual induction ties them together:

```lean
theorem toList_encodeB (t : Ty) (v : t.Val) : (encodeB t v).toList = encode t v
```

That is the entire bridge.  `encodeByteArray t v = (encodeB t v).run` then
satisfies `(encodeByteArray t v).data.toList = encode t v`, so every result
about `encode` transports by rewriting — `decode_encodeByteArray`,
`decode_encodeByteArray_static`, `isCanonical_encodeByteArray` and
`decodeCanonical_encodeByteArray` are three lines each.

Measured by `Bench.lean` (compiled; the win rests on the `@[extern]`
`ByteArray` primitives, so interpreted runs show the opposite): 2.9× on flat
`bytes[]` values, and 16×/53× at tuple nesting depth 50/200, where the
specification encoder is quadratic and the builder linear.

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
any `rest : List UInt8`, `decode t (encode t v ++ rest) = some v`.  For
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
(`encode`/`partOf`/`partsOfTuple`, `decode`/`readElem`/`decodeElems`/
`decodeTuple`), each defined by pattern matching on `Ty` or `List Ty`.
The default `decreasing_tactic` cannot always see through the list
destructuring.

**Solution.**  Every mutual block carries an explicit `termination_by`
measure (typically `sizeOf` with a constant offset to distinguish sibling
levels).  The measures are chosen so that recursive calls occur at strictly
smaller values, and the `decreasing_tactic` discharges every goal.

## 5. Architecture Diagram

```
┌──────────────────────────┐    ┌──────────────────────┐
│       Encode.lean         │───▶│    Builder.lean       │
│ encodeB / encodeByteArray │    │  Chunks / Builder     │
│ toList_encodeB — the      │    │  cached size, run     │
│ bridge to the spec;       │    │  (ABI-agnostic)       │
│ roundtrip etc. transported│    └──────────────────────┘
└─────────────┬────────────┘
              │                 ┌──────────────────────┐
              │                 │     Packed.lean       │
              │                 │  encodePacked /       │
              │                 │  decodePacked (mutual)│
              │                 └──────────┬───────────┘
              │                            │
┌─────────────▼────────────────────────────▼───┐
│                  Codec.lean                   │
│  encode / decode (mutual)                     │
│  readElem / decodeElems / decodeTuple (mutual)│
│  Packages A–E (roundtrip proofs)              │
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

### ByteArray Decoder

The encoder now has a verified `ByteArray` path (§3.7); the decoder does
not.  `decode` consumes a `List UInt8` and `readElem` reaches its component
with `buf.drop off`, which is `O(off)` — so decoding an `n`-component tuple
is quadratic, the same shape of problem the builder solved on the encoding
side.  The natural counterpart is a cursor — a `(ByteArray, offset)` pair
with `O(1)` positioning — and a bridging theorem in the same style as
`toList_encodeB`, relating `decodeCursor t ⟨ba, off⟩` to
`decode t (ba.data.toList.drop off)`, so the roundtrip transports rather
than being reproved.

### Faster Word Encoding — done, upstream

`encodeUint` goes through `Binary.encodeBEU`, which used to peel one byte at a
time with `n / 256` and `n % 256`.  Above `2 ^ 63` a `Nat` is a GMP bignum and
each of those allocates, so one EVM word cost 32 GMP calls — about 4.8 µs,
against ~30 ns for the list plumbing around it.  Every ABI word paid it.

The fix landed in `lean-binary` as `Binary.Fast`: peel eight bytes at a time
through a `UInt64`, proved equal to the definition and registered with
`@[csimp]`, so no definition, no theorem and no caller changed.  Measured on
`uint256[]` with 1000 full-width words, `encodeByteArray` went 4961 µs → 997 µs
(5.0×) and the specification encoder 5323 µs → 1307 µs, since the fix sits
below both.

## 7. References

- [Solidity ABI Specification](https://docs.soliditylang.org/en/latest/abi-spec.html)
- [Ethereum Yellow Paper, Appendix H](https://ethereum.github.io/yellowpaper/paper.pdf)
- [Lean 4 Theorem Prover](https://lean-lang.org/)
