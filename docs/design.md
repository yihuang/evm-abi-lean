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

## 3. Core Design

### 3.1 Type Universe (`Ty.lean`)

The type grammar is an inductive `Ty` with ten constructors.  Three
auxiliary predicates are defined alongside it:

- **`Valid`** — size-parameter constraints (e.g., `uintM` requires `8∣M`,
  `8≤M≤256`).  Defined as a `Prop` with a `Decidable` instance.

- **`IsStatic`** — whether the encoding size is fixed by the type.  Used by
  the head/tail layout: static elements sit inline in the head; dynamic
  elements contribute an offset word.

- **`headSize`** — bytes occupied in the head section.  Static types take
  their full encoding size; dynamic types take 32 (the offset word).

All three are defined via **mutual recursion** with their `List`-indexed
siblings (`AllValid`, `allStatic`, `headSizeSum`).  This avoids well-founded
recursion (`Acc.rec`), which would make the predicates opaque to the
elaborator and break `@[reducible]` on `Val`.

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

### 3.5 Roundtrip Proof Structure

The proof is organized into five packages (A–E) in `Codec.lean`:

| Package | Content |
|---|---|
| A | Head sizes, static encoding lengths (`encode_length_static`) |
| B | Alignment and well-formedness (`encode_length_aligned`, `wf_map_partOf`) |
| C | **Static prefix roundtrip** — `decode_encode_append_static` for every static type, plus `decodeElems_static_append` and `decodeTuple_static_append` |
| D | **Full prefix roundtrip** — `decode_encode_append`, `decodeElems_append`, `decodeTuple_append` for all types, dynamic elements included |
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
┌──────────────────────────────────────────────┐
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

### 6.1 Calldata / Function Selector

The ABI specification defines function call data as a 4-byte Keccak-256
selector followed by the ABI encoding of the argument tuple.  Adding a
calldata roundtrip theorem — given a selector and argument values, decoding
recovers both — would complete the contract-interface verification.

### 6.2 Keccak-256

The Keccak-256 hash is kept opaque: selector values are concrete bytes
verified against test vectors (`native_decide`), but no property of the
hash function itself is proved.  A future extension could model Keccak
as an abstract sponge construction or verify it against a reference
implementation.

### 6.3 Canonical Encoding

The current decoder is *lenient*: it accepts encodings that may contain
non-canonical padding or redundant zero bytes in the tail.  An
`IsCanonical` predicate could be added to validate that every produced
encoding is canonical, and that the lenient decoder on canonical input
is complete (no false rejections).

### 6.4 ByteArray Interface

The library works entirely with `List UInt8` for proofs and `ByteArray`
only at the I/O boundary.  A future layer could lift the roundtrip theorem
to `ByteArray` without reproving, using a list/bytearray isomorphism lemma.

## 7. References

- [Solidity ABI Specification](https://docs.soliditylang.org/en/latest/abi-spec.html)
- [Ethereum Yellow Paper, Appendix H](https://ethereum.github.io/yellowpaper/paper.pdf)
- [Lean 4 Theorem Prover](https://lean-lang.org/)
