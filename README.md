# abi-lean

EVM ABI encoding and decoding, formally verified in Lean 4.

Conforms to the [Solidity ABI Specification](https://docs.soliditylang.org/en/latest/abi-spec.html).

## Core Theorems

### Roundtrip (bijection)

The central result is that `encode` and `decode` form a **bijection** between
the value space of a valid ABI type and the image of `encode` within the
`2^256`-byte universe.  The strict roundtrip — decode after encode is the
identity on a complete buffer — is:

```lean4
theorem decodeStrict_encode (t : Ty) (hv : t.Valid) (v : t.Val)
    (hb : (encode t v).length < 2 ^ 256) : decodeStrict t (encode t v) = some v
```

`decode` is the linear canonical decoder in *prefix form*: it returns the
value together with the number of bytes it consumed and the untouched
remainder, so nested components are prefixes of their parent's buffer
(`decode t (encode t v ++ rest) = some (v, (encode t v).length, rest)`).
The count is computed structurally, never by measuring the buffers, which
is what lets the walk advance its tail frontier in `O(1)` per component.

Injectivity of `encode` is an immediate corollary (`encode_of_decodeStrict`):
if two values encode to the same buffer, decoding that buffer recovers
both, so they coincide.

For **static types** (no dynamic offsets) the total-length bound is
dispensed with entirely:

```lean4
theorem decode_static_append (t : Ty) (hs : t.isStatic = true) (hv : t.Valid)
    (v : t.Val) (rest : List UInt8) :
    decode t (encode t v ++ rest) = some (v, t.headSize, rest)
```

No `sorry`.  All types (`uintM`, `intM`, `bool`, `address`, `bytesM`, `bytes`, `string`,
`T[]`, `T[k]`, `(T₁,…,Tₙ)`) and arbitrarily nested combinations thereof are covered.

### Strictness

Strictness is intrinsic to the decoder, not a separate layer: `decode` walks
a buffer with two monotonic cursors (head section, tails) threading an
*expected tail frontier*, and a dynamic component's offset word must equal
the frontier exactly — so tails are forced to be laid out *contiguously, in
order, immediately after the head section*.  `decodeStrict` is `decode`
plus an exact-consumption check (no trailing garbage), and `IsCanonical`
the corresponding predicate.

The capstone theorems characterise the bijection in purely extensional terms:

```lean4
-- Under the buffer bound, canonical buffers are exactly the encodings.
theorem isCanonical_iff (t : Ty) (hv : t.Valid) (buf : List UInt8)
    (hb : buf.length < 2 ^ 256) :
    IsCanonical t buf ↔ ∃ v, encode t v = buf

-- The strict decoder succeeds exactly on encodings — no side condition on the
-- value, since every t.Val carries its own bounds.
theorem decodeStrict_eq_some_iff (t : Ty) (hv : t.Valid) (buf : List UInt8)
    (v : t.Val) (hb : buf.length < 2 ^ 256) :
    decodeStrict t buf = some v ↔ encode t v = buf
```

The negative test suite in `Tests.lean` shows that non-canonical inputs
(swapped tails, gaps, duplicate offsets, misaligned offsets, trailing
garbage) are all rejected by `decodeStrict`.

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

Packed sizes are computed by `packedSize : Ty → Nat` (`uint8` → 1 byte,
`address` → 20 bytes, `uint8[3]` → 96 bytes — array elements are padded).
The `.tuple` arm is the flat argument list of a multi-argument
`abi.encodePacked(a, b, …)` call (`(uint8, bool)` → 2 bytes); applied to
*nested* tuples or arrays it is a total-function extension with no
Solidity counterpart, documented and tested as such.

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
`theorem`, or as arguments to `encode`/`decode`.

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

## Proof Structure

The proof is built in incremental layers, each reusable independently:

| Layer | Module | What it proves |
|---|---|---|
| **1. Byte plumbing** | `Bytes` | `pad32`, `take`/`drop` lemmas over appended buffers |
| **2. 32-byte alignment** | `Align` | `Aligned n := 32 ∣ n`, addition and multiplication lemmas (all `omega`) |
| **3. Word I/O** | `Word` | Reading/writing `UInt256` at aligned buffer offsets; `wordAt_append` |
| **4. Type universe** | `Ty` | ABI type grammar `Ty`, indexed value family `Val` (bounds baked into subtypes), validity/staticness/head-size predicates |
| **5. Static primitives** | `Static` | Standalone codecs for `uintM`, `intM`, `bool`, `address`, `bytesN`; strict bool/bytesN decoders |
| **6. Dynamic primitives** | `Dynamic` | Standalone codecs for `bytes`, `string`; prefix-tolerant decoder variant |
| **7. Head/tail combinator** | `Parts` | The core ABI layout abstraction (`Part`, `encodeParts`, offset-correctness theorems); type-independent |
| **8. Full codec** | `Codec` + `Codec.Roundtrip` / `Codec.Sound` / `Codec.Strict` | `Ty`-indexed `encode` and the linear decoder `decode` (`Get2` walkers `decodeElem`/`decodeElems`/`decodeTuple`); bound-free static delegation in `Codec`; roundtrip and soundness families in their own files; strict API `decodeStrict`/`IsCanonical` and the capstones in `Codec.Strict` |
| **9. Packed ABI** | `Packed` | Packed encoding for all-static types; primitive packed codecs, type-indexed `encodePacked`/`decodePacked`, static packed roundtrip |
| **10. Human-readable ABI** | `HumanReadable` | Solidity-signature parser (`Ty.parse`, `AbiItem.parse`, `AbiParam.parseList`) |
| **11. Compile-time macros** | `HumanReadable.Meta` | `ty!`, `item!`, `params!` — parse string literals at elaboration time |
| **Tests** | `Tests` | Spec-vector encoding checks (sam, f, g), roundtrip regression, positive/negative canonical validation tests, packed encoding checks, human-readable ABI tests |

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
let enc := encode t v
-- enc = word(42) ++ word(1)

-- strict roundtrip
example : decodeStrict t (encode t v) = some v :=
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

## License

MIT
