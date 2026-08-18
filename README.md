# abi-lean

EVM ABI encoding and decoding, formally verified in Lean 4.

Conforms to the [Solidity ABI Specification](https://docs.soliditylang.org/en/latest/abi-spec.html).

## Core Theorems

All theorems in this section are stated in `namespace EvmAbi.Spec`.

### Roundtrip (bijection)

The central result is that `Spec.encode` and `Spec.decode` form a **bijection** between
the value space of a valid ABI type and the image of `Spec.encode` within the
`2^256`-byte universe.  The strict roundtrip — decoding after encoding is the
identity on a complete buffer — is:

```lean4
-- in `namespace EvmAbi.Spec`
theorem decodeStrict_encode (t : Ty) (hv : t.Valid) (v : t.Val)
    (hb : (Spec.encode t v).length < 2 ^ 256) : Spec.decodeStrict t (Spec.encode t v) = some v
```

`Spec.decode` is the linear canonical decoder in *prefix form*: it returns the
value together with the number of bytes it consumed and the untouched
remainder, so nested components are prefixes of their parent's buffer
(`Spec.decode t (Spec.encode t v ++ rest) = some (v, (Spec.encode t v).length, rest)`).
The count is computed structurally, never by measuring the buffers, which
is what lets the walk advance its tail frontier in `O(1)` per component.

Injectivity of `Spec.encode` is an immediate corollary (`Spec.encode_of_decodeStrict`):
if two values encode to the same buffer, decoding that buffer recovers
both, so they coincide.

For **static types** (no dynamic offsets) the total-length bound is
dispensed with entirely:

```lean4
theorem decode_static_append (t : Ty) (hs : t.isStatic = true) (hv : t.Valid)
    (v : t.Val) (rest : List UInt8) :
    Spec.decode t (Spec.encode t v ++ rest) = some (v, t.headSize, rest)
```

No `sorry`.  All types (`uintM`, `intM`, `bool`, `address`, `bytesM`, `bytes`, `string`,
`T[]`, `T[k]`, `(T₁,…,Tₙ)`) and arbitrarily nested combinations thereof are covered.

### Strictness

Strictness is intrinsic to the decoder, not a separate layer: `Spec.decode` walks
a buffer with two monotonic cursors (head section, tails) threading an
*expected tail frontier*, and a dynamic component's offset word must equal
the frontier exactly — so tails are forced to be laid out *contiguously, in
order, immediately after the head section*.  `Spec.decodeStrict` is `Spec.decode`
plus an exact-consumption check (no trailing garbage), and `Spec.IsCanonical`
the corresponding predicate.

The capstone theorems characterise the bijection in purely extensional terms:

```lean4
-- Under the buffer bound, canonical buffers are exactly the encodings.
theorem isCanonical_iff (t : Ty) (hv : t.Valid) (buf : List UInt8)
    (hb : buf.length < 2 ^ 256) :
    Spec.IsCanonical t buf ↔ ∃ v, Spec.encode t v = buf

-- The strict decoder succeeds exactly on encodings — no side condition on the
-- value, since every t.Val carries its own bounds.
theorem decodeStrict_eq_some_iff (t : Ty) (hv : t.Valid) (buf : List UInt8)
    (v : t.Val) (hb : buf.length < 2 ^ 256) :
    Spec.decodeStrict t buf = some v ↔ Spec.encode t v = buf
```

The negative test suite in `Tests.lean` shows that non-canonical inputs
(swapped tails, gaps, duplicate offsets, misaligned offsets, trailing
garbage) are all rejected by `Spec.decodeStrict`.

### Packed ABI

Packed encoding (Solidity's *non-standard packed mode*,
`abi.encodePacked`) follows four rules: types shorter than 32 bytes are
concatenated **without padding**; dynamic types (`bytes`, `string`,
`T[]`) are encoded **in place and without the length**; array *elements*
are **padded** to their standard 32-byte-word width, but still encoded in
place; and **structs as well as nested arrays are not supported** by
Solidity.  `EvmAbi.Packed` implements all four; `PackedSupported` marks
the Solidity-conformant fragment (scalars, `bytes`/`string`, arrays of
scalar elements).

Packed encoding carries no lengths or offsets, so it is ambiguous in
general; only the static fragment is decodable, and its roundtrip is
proved:

```lean4
theorem roundtrip_packed_static (t : Ty) (hs : t.isStatic = true) (hv : t.Valid)
    (v : t.Val) : decodePacked t (encodePacked t v) = some v
```

The packed codec mirrors the standard one: encoding is assembled with the
`Builder` chunk tree (`putPacked`, materialized once by `toList`),
and decoding is a single linear pass with `Get2` walkers
(`decodePackedElem` / `decodePackedTuple`), reading array elements at
their padded widths via the standard `decodeElems`.

Packed sizes are computed by `packedSize : Ty → Nat` (`uint8` → 1 byte,
`address` → 20 bytes, `uint8[3]` → 96 bytes — array elements are padded).
The `.tuple` arm is the flat argument list of a multi-argument
`abi.encodePacked(a, b, …)` call (`(uint8, bool)` → 2 bytes); applied to
*nested* tuples or arrays it is a total-function extension with no
Solidity counterpart, documented and tested as such.

### Runtime codec

The names users run are unsuffixed: `encode` takes a `ValBA` value (packed
`ByteArray` payloads) and returns a `ByteArray`; `decode` / `decodeStrict`
take a `ByteArray` and return `ValBA` values; `IsCanonical` is the
corresponding predicate.  The list-based specification lives in the `Spec`
namespace (`Spec.encode`, `Spec.decodeStrict`, …) and is the surface every
theorem is stated over.

`EvmAbi.Builder` is what the encoder is written against, so there is only
one encoder.  A `Builder` is a tree of byte runs paired with its cached byte
count: concatenation is an `O(1)` constructor, `String.toUTF8` payloads stay
`ByteArray` chunks, padding is a `zeros` node, and `run` allocates the exact
size once and fills it with `ByteArray.push`.  The cache is not a detail —
the head/tail layout asks for every tail's size while writing the offset
words, so a `size` that walked the tree would put the `O(n · d)` cost
straight back.

`Spec.encode` returns a `List UInt8`.  That is the right type for the proofs — `++`
is associative on the nose and `take`/`drop` have a rich algebra — and the
wrong one for execution: a cons cell and a boxed byte per byte, and a nest of
`++`s that re-copies a value's bytes once per level of nesting, so a `d`-deep
value costs `O(n · d)`.  `Spec.encode` and `Spec.encodeByteArray` are the same
`Spec.put`, materialized two ways:

```lean4
def Spec.encode (t : Ty) (v : t.Val) : List UInt8 := (Spec.put t v).toList   -- specification
def Spec.encodeByteArray (t : Ty) (v : t.Val) : ByteArray := (Spec.put t v).run

-- so the bytes it produces are exactly the specified ones
-- in `namespace EvmAbi.Spec`
theorem data_toList_encodeByteArray (t : Ty) (v : t.Val) :
    (Spec.encodeByteArray t v).data.toList = Spec.encode t v
```

The runtime encoder is the same layout over `ValBA` values, and
`toList_putBA` proves it denotes the spec encoder of the denotation:

```lean4
def encode (t : Ty) (v : ValBA t) : ByteArray := (putBA t v).run

theorem toList_putBA (t : Ty) (v : ValBA t) :
    (putBA t v).toList = Spec.encode t (ValBA.toList t v)
```

so the roundtrip, the static roundtrip, canonicity and the strict roundtrip
transport to the runtime encoder without reproving anything.

Compiled, that is worth 6× on a flat `bytes[]` and 92× at nesting depth 200 —
`Spec.encode` re-copies a `d`-deep value's bytes `d` times where the builder
stays linear.  Numbers and method are in [docs/performance.md](docs/performance.md).

The decoder has the same two forms.  `Spec.decode` walks two `List UInt8`
cursors; `decodeStrict` (runtime) walks the same layout as two *offsets*
into one shared `ByteArray`, reading words with an indexed read and
materialising only the payloads that a `bytes`/`string`/`bytesN` value
actually is:

```lean4
theorem decodeStrictBAVal_eq (t : Ty) (hv : t.Valid) (ba : ByteArray) :
    (decodeStrict t ba).map (ValBA.toList t) = decodeStrictBA t ba

theorem decodeStrictBA_eq (t : Ty) (hv : t.Valid) (ba : ByteArray) :
    decodeStrictBA t ba = Spec.decodeStrict t ba.data.toList
```

Agreement runs *downward* — it says what a runtime answer denotes — while a
capstone is about the runtime value itself, so the conclusion comes back up
through `ValBA.toList_injective`.  With it, the capstones are stated of the
runtime names:

```lean4
theorem decodeStrict_encode (t : Ty) (hv : t.Valid) (v : ValBA t)
    (hb : (encode t v).size < 2 ^ 256) : decodeStrict t (encode t v) = some v

theorem isCanonical_iff (t : Ty) (hv : t.Valid) (ba : ByteArray)
    (hb : ba.size < 2 ^ 256) : IsCanonical t ba ↔ ∃ v : ValBA t, encode t v = ba
```

— the roundtrip returning the very same `ValBA` value, not merely one with
the same denotation, plus `encode_of_decodeStrict` and
`decodeStrict_eq_some_iff`.  Compiled, the offset cursors decode a `bytes[]`
3.5× faster than the list ones ([performance](docs/performance.md)).

## Human-Readable ABI

Solidity-style human-readable ABI signatures can be parsed into `Ty` and
`AbiItem` values, both at runtime and **at compile time** via macro
expansion.

### Curried parser API

```lean4
open EvmAbi

-- Parse a type string
#eval Ty.parse "uint256"
-- some (Ty.uint 256)

#eval Ty.parse "(address, uint256)[]"
-- some (Ty.array (Ty.tuple [Ty.address, Ty.uint 256]))

-- Parse a full ABI item
#eval AbiItem.parse "function approve(address spender, uint256 amount) returns (bool)"
-- some (AbiItem.function "approve" [⟨.address, "spender", false⟩, ⟨.uint 256, "amount", false⟩] ...)

#eval AbiItem.parse "event Transfer(address indexed from, address indexed to, uint256 value)"
#eval AbiItem.parse "error Unauthorized(address caller)"
#eval AbiItem.parse "constructor(address owner) payable"

-- Parse a parameter list
#eval AbiParam.parseList "address spender, uint256 amount"
```

### Compile-time macros

Three macros expand at elaboration time, converting string literals directly
into `Ty`, `AbiItem`, or `List AbiParam` expressions:

The macros live in `EvmAbi.HumanReadable.Meta`, which is not re-exported by the
`EvmAbi` root module: it needs `import Lean`, and the rest of the library stays
free of the Lean frontend.  Import it explicitly.

```lean4
import EvmAbi.HumanReadable.Meta
open EvmAbi.HumanReadable.Meta

-- Type macro: expands to the Ty constructor term
let t : Ty := ty! "uint256[]"
-- t = Ty.array (Ty.uint 256)

-- ABI item macro: expands to the AbiItem constructor term
let item := item! "function balanceOf(address) view returns (uint256)"
-- item = AbiItem.function "balanceOf" [⟨.address, none, false⟩] [⟨.uint 256, none, false⟩] .view

-- Parameter list macro: expands to List AbiParam
let p := params! "address spender, uint256 amount"
-- p = [⟨.address, "spender", false⟩, ⟨.uint 256, "amount", false⟩]
```

The macros fail at **compile time** if the string is not a valid
human-readable ABI signature, catching typos before any code runs.
They can be used anywhere a term is expected — `def`, `let`, `example`,
`theorem`, or as arguments to `Spec.encode`/`Spec.decode`.

### Supported syntax

| Human-readable | `Ty` |
|---|---|
| `uint<N>` | `.uint N` |
| `int<N>` | `.int N` |
| `uint` / `int` | `.uint 256` / `.int 256` |
| `address` | `.address` |
| `bool` | `.bool` |
| `bytes` | `.bytes` |
| `bytes<N>` | `.bytesN N` |
| `string` | `.string` |
| `T[]` | `.array T` |
| `T[N]` | `.fixedArray T N` |
| `(T₁, …, Tₙ)` | `.tuple [T₁, …, Tₙ]` |

Array suffixes apply to tuples as well, so `(address,uint256)[]` — a Solidity
`struct[]` — is a `.array (.tuple […])`.  Widths outside the range the
specification allows (`uint7`, `bytes33`, …) are rejected, so every type a
parse produces satisfies `Ty.Valid` and the codec theorems apply to it.

ABI items: `function`, `event`, `error`, `constructor`, `fallback`, `receive`.

Solidity source syntax with no ABI counterpart is accepted and dropped:
visibility (`external`, `public`, `internal`, `private`), `virtual`/`override`,
data locations (`calldata`, `memory`, `storage`) and the `payable` of
`address payable`.  `view`/`pure`/`payable`/`nonpayable` (at most one) are
recorded as the item's state mutability, and `indexed` as the parameter's flag.

## ABI Compiler

`abi_codec` compiles all four names of the runtime API — `encode`, `decode`,
`decodeStrict`, `IsCanonical` — for one fixed type, at elaboration time, and
proves each one equal to its `EvmAbi` counterpart as it goes (`abi_encoder` and
`abi_decoder` compile one direction each, under the plain name):

```lean4
import EvmAbi.Compile.Meta
open EvmAbi.Compile.Meta

abi_codec transfer "transfer(address to, uint256 amount)"

#check @transfer.encode        -- ValBA transfer.ty → ByteArray
#check @transfer.decodeStrict  -- ByteArray → Option (ValBA transfer.ty)
#check @transfer.encode_eq     -- ∀ v, transfer.encode v = EvmAbi.encode transfer.ty v
#check @transfer.decodeStrict_eq
#check @transfer.roundtrip     -- ∀ v, … → transfer.decodeStrict (transfer.encode v) = some v
```

Both generic codecs are *interpretive*.  `putBA` matches on the `Ty` while it
walks the value, `partOfBA` asks `t.isStatic` per component — and per array
*element* — `partsOfTupleBA` allocates a `List Part`, and `putParts` walks
that list three more times (`headSizes`, `putHeads`, `putTails`);
`decodeBAVal` matches on the `Ty` at every value and `decodeElemBAVal` asks
`isStatic` at every component and element.  All of it is determined by the
type alone, so for a fixed type it can be settled once, at compile time.
Print what the command emitted:

```lean4
#print transfer.put
-- fun v => (((Acc.start 64).static (putAddress v.fst.val)).static (putUint v.snd.fst.val)).finish

#print transfer.read
-- readTuple 64 (cons elemStatic readAddress (cons elemStatic (readUint 256) consNil))
```

No `Ty`, no `Part`, no list: straight-line code whose head size (`64`) and
first tail offset are numerals, and a reader chain that already knows which
component sits in the head and which behind an offset word.  Arrays keep
exactly one loop — the element count is not known until run time — but the
instruction that loop runs is chosen at compile time.

`#print` shows the root definitions; the sub-nodes and the correctness
theorems have names you would have to guess.  Appending `trace` to any of
the three commands prints each *specialised* definition and its correctness
theorem as the emitter writes it — the raw generated syntax, before
elaboration, exactly what the compiler did:

```lean4
abi_codec transfer "transfer(address to, uint256 amount)" trace
-- ┌─ emitted transfer.put
-- │def transfer.put : … := fun v => …
-- │theorem transfer.put_denotes : … := …
-- ┌─ emitted transfer.read
-- │def transfer.read : … := …
-- │theorem transfer.read_reads : … := …
```

The trace is a `logInfo` message: it prints when the file is elaborated, so
run `lake env lean file.lean` (or any command that re-elaborates, e.g.
`touch file.lean && lake build`) and read the `info:` lines; in VS Code it
appears in the Lean Messages panel.  A normal `lake build` with everything
up to date runs no elaborator and prints nothing — and the pinned trace test
in `Tests.lean` wraps its command in `#guard_msgs`, which consumes the
messages by design.

`abi_codec foo` emits:

| name | what it is |
|---|---|
| `foo.ty` | the `Ty` that was compiled (an `abbrev`) |
| `foo.node…` / `foo.dnode…` (+ `_denotes` / `_reads`) | the compiled codec of each compound sub-type, and its correctness |
| `foo.put` / `foo.read` (+ `_denotes` / `_reads`) | the compiled encoder in builder form, and the compiled reader |
| `foo.encode`, `foo.decode`, `foo.decodeStrict`, `foo.isCanonical` | the four names of the runtime API, compiled |
| `foo.encode_eq`, `foo.decode_eq`, `foo.decodeStrict_eq`, `foo.isCanonical_eq` | each one *is* its `EvmAbi` counterpart |
| `foo.encode_decodeStrict` / `foo.decodeStrict_encode` | each direction against the *generic* other one |
| `foo.decodeStrict_uniq` | a buffer `foo.decodeStrict` accepts is the encoding of what it read |
| `foo.roundtrip` | `foo.decodeStrict (foo.encode v) = some v` |

`abi_encoder foo "…"` emits the encoder half under the plain name `foo`
(`foo_eq`, `foo_decodeStrict`); `abi_decoder foo "…"` the decoder half
(`foo_eq`, `foo_encode`, `foo_uniq`).

A string that is not an ABI type is a compile-time error at the string, and
nothing is emitted — so a typo cannot reach a generated codec:

```lean4
abi_encoder oops "uint7"
-- error: abi_encoder: not an ABI type or signature: uint7
```

### Why it is trustworthy

A metaprogram cannot be verified from inside Lean — there is no theorem about
the elaborator to prove.  What *can* be arranged is that the compiler is
unable to emit code it cannot justify, and that is the design here:

* the emitted code is written against a small **abstract machine**
  (`EvmAbi.Compile` for writing — `Acc.start`, `static`, `dyn`, `finish` and
  one element loop; `EvmAbi.Compile.Decode` for reading — `elemStatic`,
  `elemDyn`, the chain and loop built on them, and the three compound
  clauses), and each
  instruction's correctness is proved *once* against the generic codec: on the
  encoder side as "this instruction preserves the layout invariant `Acc.Inv`",
  on the decoder side as "this reader answers what `decodeBAVal` answers";
* for every definition the compiler prints, it prints a theorem
  (`Denotes foo.ty foo.put`, `Reads foo.ty foo.read`) whose proof is nothing
  but those lemmas applied to the sub-codecs' theorems.  The emitter never
  invents a proof step;
* Lean's kernel checks each one as it is emitted.  A compiled encoder that
  disagrees with `EvmAbi.encode` therefore cannot be produced — the command
  fails at compile time instead.

### It reduces in the kernel

`EvmAbi.encode` is well-founded-recursive over `Ty`, so the kernel cannot
evaluate it — `decide +kernel` on a concrete encoding gets stuck at the
`Decidable` instance.  A compiled codec has no recursion in it for a fixed
type, so the kernel walks it, and `_eq` carries the result back:

```lean4
abi_codec erc20Transfer "transfer(address to, uint256 amount)"

theorem bytes : (erc20Transfer.encode v).data.toList = … := by decide +kernel
theorem generic : (encode erc20Transfer.ty v).data.toList = … := by
  rw [← erc20Transfer.encode_eq v]; exact bytes    -- the kernel never unfolds `encode`
```

Both directions reduce (`Tests.lean` pins the ERC-20 vector), on `[propext]`
alone — no `native_decide`.  That matters downstream: an audit that wants a
concrete encoding checked on the base axioms has otherwise needed a
fuel-indexed mirror of the encoder to rewrite through first.

So the compiled code inherits the whole verified stack: `foo.encode_eq` and
`foo.decode_eq` rewrite any statement about `EvmAbi.encode` /
`EvmAbi.decodeStrict` onto the compiled names, which is how `foo.roundtrip`
and `foo.decodeStrict_uniq` come out for free — the bijection of the *Core
Theorems* section, on compiled code.

### What it costs

Compilation removes the *layout* overhead and nothing else, so the win depends
on how expensive the words themselves are: 2.25× on `(bool × 8)`, where cheap
words make the layout the work, down to 1.06× on full-width `uint256[]`, where
the word codec dominates and there is little left to remove.  The tables, and
the three optimizations measured and rejected, are in
[docs/performance.md](docs/performance.md).

## Proof Structure

The proof is built in incremental layers, each reusable independently:

| Layer | Module | What it proves |
|---|---|---|
| **1. Byte plumbing** | `Bytes` | `pad32`, `take`/`drop` lemmas over appended buffers |
| **2. 32-byte alignment** | `Align` | `Aligned n := 32 ∣ n`, addition and multiplication lemmas (all `omega`) |
| **3. Word I/O** | `Word` | Reading/writing `UInt256` at aligned buffer offsets; `wordAt_append` |
| **4. Type universe** | `Ty` | ABI type grammar `Ty`, indexed value family `Val` (bounds baked into subtypes), validity/staticness/head-size predicates |
| **5. Builder / reader** | `Builder` | `Chunks`/`Builder` with `O(1)` concatenation and a cached size, `toList` denotation, `run` into a pre-sized `ByteArray`; the dual-cursor `Get2` reader monad; ABI-agnostic |
| **6. Static primitives** | `Static` | Standalone codecs for `uintM`, `intM`, `bool`, `address`, `bytesN`; strict bool/bytesN decoders |
| **7. Dynamic primitives** | `Dynamic` | Standalone codecs for `bytes`, `string`; prefix-tolerant decoder variant |
| **8. Head/tail combinator** | `Parts` | The core ABI layout abstraction (`Part`, `encodeParts`, offset-correctness theorems); type-independent |
| **9. Spec codec** | `Codec` + `Codec.Roundtrip` / `Codec.Sound` / `Codec.Strict` | `Ty`-indexed `Spec.encode` (the `List UInt8` specification) and `Spec.encodeByteArray` (the same builder run into a `ByteArray`); the linear decoder `Spec.decode` (`Get2` walkers `decodeElem`/`decodeElems`/`decodeTuple`); bound-free static delegation in `Codec`; roundtrip and soundness families in their own files; strict API `Spec.decodeStrict`/`Spec.IsCanonical` and the capstones |
| **10. Runtime codec** | `Codec` + `Codec.ByteArray` | `encode`/`decode`/`decodeStrict`/`IsCanonical` over `ByteArray` and `ValBA`; the offset primitives (`natAtBA`, `windowList`), the `ValBA` walkers, the `toList_putBA` encoder bridge, the agreement lemmas (`decodeBAVal_eq`, `decodeStrictBAVal_eq`, `decodeStrictBA_eq`) that carry the `Spec` theorems across, `ValBA.toList_injective` that carries conclusions back, and the runtime capstones (`decodeStrict_encode`, `encode_of_decodeStrict`, `decodeStrict_eq_some_iff`, `isCanonical_iff`) |
| **11. Packed ABI** | `Packed` | Packed encoding for all-static types; primitive packed codecs, type-indexed `encodePacked`/`decodePacked`, static packed roundtrip |
| **12. Human-readable ABI** | `HumanReadable` | Solidity-signature parser (`Ty.parse`, `AbiItem.parse`, `AbiParam.parseList`) |
| **13. Compile-time macros** | `HumanReadable.Meta` | `ty!`, `item!`, `params!` — parse string literals at elaboration time |
| **14. Compiler target** | `Compile` + `Compile.Decode` | The layout machine (`Acc`, its invariant `Acc.Inv` and one lemma per instruction) and the element loops; the component readers, element loops and compound clauses of the decoder; `Denotes` and `Reads` — the contracts every compiled codec is proved to satisfy |
| **15. Compiler** | `Compile.Meta` | `abi_encoder` / `abi_decoder` / `abi_codec` — emit a codec specialised to one type, with its correctness theorems, at elaboration time |
| **Tests** | `Tests` | Spec-vector encoding checks (sam, f, g), roundtrip regression, positive/negative canonical validation tests, packed encoding checks, builder and executable-encoder checks, offset-decoder checks (including degenerate and truncated buffers), human-readable ABI tests, compiled-codec checks against the same spec vectors, and its negative vectors |
| **Bench** | `Bench` | `lake build bench` — `Spec.encode` vs `Spec.encodeByteArray` vs runtime `encode`, `Spec.decodeStrict` vs `decodeStrict`, compiled vs generic `encode`/`decodeStrict`, and the word codec against an unboxed-`Nat` and a four-limb ceiling |

The separation of the **head/tail combinator (Parts)** from the **type-indexed codec (Codec)** is the key architectural decision:
the combinatorial heart of the ABI offset arithmetic is proved once on `List Part`,
then every type case in Codec reduces to it.

## Quick Example

```lean4
import EvmAbi
import EvmAbi.HumanReadable.Meta

open EvmAbi
open EvmAbi.Ty
open EvmAbi.HumanReadable.Meta

-- construct a type via human-readable ABI
let t : Ty := ty! "(uint256, bool)"
let v : t.Val := (⟨42, by decide⟩, (true, ()))
let enc := Spec.encode t v
-- enc = word(42) ++ word(1)

-- strict roundtrip
example : Spec.decodeStrict t (Spec.encode t v) = some v :=
  decodeStrict_encode t (by
    simp [Valid, AllValid])
    v
    (by native_decide)
```

## Build & Test

```bash
lake build
```

Tests (spec vectors, roundtrips, error cases) run via `native_decide` / `decide` checks in `Tests.lean`:

```bash
lake test          # build and run all test targets
lake build Tests   # compile the test module
```

The benchmark is not in `defaultTargets`, so CI does not pay for it:

```bash
lake build bench && ./.lake/build/bin/bench
```

See [docs/performance.md](docs/performance.md) for what it measures and the
current numbers, and [docs/design.md](docs/design.md) for the design notes.

## License

MIT
