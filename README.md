# abi-lean

EVM ABI encoding and decoding, formally verified in Lean 4.

Conforms to the [Solidity ABI Specification](https://docs.soliditylang.org/en/latest/abi-spec.html).

## Core Theorems

### Roundtrip (bijection)

The central result is that `encode`/`decode` form a **bijection** between the
value space of a valid ABI type and the image of `encode` within the
`2^256`-byte universe.

On the value side, every bound that matters is baked into the **value family**
`t.Val` itself (see [`EvmAbi.Ty`](#proof-structure)): a `bytes` value
carries a proof that its payload length is `< 2^256`, an `array` value
carries a proof that its element count is `< 2^256`, and containers inherit
their components' bounds through the recursion.  The only global assumption
is that the *total* encoding length also stays below `2^256` — an aggregate
property no single value can control.

```lean4
theorem roundtrip (t : Ty) (hv : t.Valid) (v : t.Val)
    (hb : (encode t v).length < 2 ^ 256) : decode t (encode t v) = some v
```

Injectivity of `encode` is an immediate corollary: if two values encode to
the same buffer, decoding that buffer recovers both, so they coincide.

For **static types** (no dynamic offsets) the total-length bound is
dispensed with entirely:

```lean4
theorem roundtrip_static (t : Ty) (hs : t.IsStatic = true) (hv : t.Valid) (v : t.Val) :
    decode t (encode t v) = some v
```

No `sorry`.  All types (`uintM`, `intM`, `bool`, `address`, `bytesM`, `bytes`, `string`,
`T[]`, `T[k]`, `(T₁,…,Tₙ)`) and arbitrarily nested combinations thereof are covered.

### Strictness / canonical validation

The lenient decoder accepts buffers whose offset words point anywhere decodable.
A separate **canonical validation** layer checks the stricter ABI requirement:
dynamic offset words must point to tails laid out *contiguously, in order,
immediately after the head section*, with no trailing garbage.

Three packages of theorems relate validation, lenient decoding, and encoding:

```lean4
-- C1. Completeness: every encoding validates, consuming exactly its length.
theorem isCanonical_encode (t : Ty) (hv : t.Valid) (v : t.Val)
    (hb : (encode t v).length < 2 ^ 256) : IsCanonical t (encode t v)

-- C2. Lenient completeness on canonical input: whatever validates also lenient-decodes.
theorem validate_decode (t : Ty) (buf : List UInt8) (n : Nat)
    (h : validate t buf = some n) : ∃ v, decode t buf = some v

-- C3. Canonical soundness: validation + lenient decoding pins the buffer down to the
--     encoding of the decoded value.  Canonical buffers are exactly the image of encode.
theorem encode_of_decodeCanonical (t : Ty) (hv : t.Valid) (buf : List UInt8) (v : t.Val)
    (h : decodeCanonical t buf = some v) : encode t v = buf
```

Composing C1 and C3 gives the **canonical roundtrip** and **canonical uniqueness**:

```lean4
theorem decodeCanonical_encode (t : Ty) (hv : t.Valid) (v : t.Val)
    (hb : (encode t v).length < 2 ^ 256) : decodeCanonical t (encode t v) = some v
```

The capstone theorems characterise the bijection in purely extensional terms:

```lean4
-- Under the buffer bound, canonical buffers ↔ encodings (with no bound on the value side).
theorem isCanonical_iff (t : Ty) (hv : t.Valid) (buf : List UInt8)
    (hb : buf.length < 2 ^ 256) :
    IsCanonical t buf ↔ ∃ v, decode t buf = some v ∧ encode t v = buf

-- Strict-decoder characterisation: succeeds exactly on encodings — no side condition
-- on the value, since every t.Val carries its own bounds.
theorem decodeCanonical_eq_some_iff (t : Ty) (hv : t.Valid) (buf : List UInt8)
    (v : t.Val) (hb : buf.length < 2 ^ 256) :
    decodeCanonical t buf = some v ↔ encode t v = buf
```

The negative test suite in `Tests.lean` shows that the lenient decoder accepts
non-canonical inputs (swapped tails, gaps, duplicate offsets, misaligned offsets)
while the strict decoder rejects them all.

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
theorem roundtrip_packed_static (t : Ty) (hs : t.IsStatic = true) (hv : t.Valid)
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

```lean4
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
| **8. Full codec** | `Codec` | `Ty`-indexed `encode`/`decode` over the full universe; static roundtrip, dynamic roundtrip, unified `roundtrip` |
| **9. Canonical validation** | `Canonical` | `validate`/`IsCanonical`/`decodeCanonical`; completeness (C1), lenient completeness on canonical input (C2), soundness (C3), bijection characterisation |
| **10. Packed ABI** | `Packed` | Packed encoding for all-static types; primitive packed codecs, type-indexed `encodePacked`/`decodePacked`, static packed roundtrip |
| **11. Human-readable ABI** | `HumanReadable` | Solidity-signature parser (`Ty.parse`, `AbiItem.parse`, `AbiParam.parseList`) |
| **12. Compile-time macros** | `HumanReadable.Meta` | `ty!`, `item!`, `params!` — parse string literals at elaboration time |
| **Tests** | `Tests` | Spec-vector encoding checks (sam, f, g), roundtrip regression, positive/negative canonical validation tests, packed encoding checks, human-readable ABI tests |

The separation of the **head/tail combinator (Parts)** from the **type-indexed codec (Codec)** is the key architectural decision:
the combinatorial heart of the ABI offset arithmetic is proved once on `List Part`,
then every type case in Codec reduces to it.

## Quick Example

```lean4
import EvmAbi

open EvmAbi
open EvmAbi.Ty
open EvmAbi.HumanReadable.Meta

-- construct a type via human-readable ABI
let t : Ty := ty! "(uint256, bool)"
let v : t.Val := (⟨42, by decide⟩, (true, ()))
let enc := encode t v
-- enc = word(42) ++ word(1)

-- roundtrip
example : decode t (encode t v) = some v :=
  roundtrip t (by
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
