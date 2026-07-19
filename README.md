# abi-lean

EVM ABI encoding and decoding, formally verified in Lean 4.

Conforms to the [Solidity ABI Specification](https://docs.soliditylang.org/en/latest/abi-spec.html).

## Core Theorems

### Roundtrip (lenient decoder)

The central result is a **roundtrip theorem**: for every valid ABI type `t` and every value `v`
whose encoding fits in `2^256` bytes, decoding the encoding recovers the original value.

```lean4
theorem roundtrip (t : Ty) (hv : t.Valid) (v : t.Val) (hl : LenBound t v)
    (hb : (encode t v).length < 2 ^ 256) : decode t (encode t v) = some v
```

The three preconditions are:
- `hv : t.Valid` — the type parameters comply with the ABI spec (e.g. `8 ≤ m ≤ 256`, `8 ∣ m` for `uintM`);
- `hl : LenBound t v` — every dynamic payload (bytes, string, array elements) fits in a single `uint256` length word;
- `hb : (encode t v).length < 2 ^ 256` — the total encoding itself fits in `2^256` bytes (so no offset word wraps).

Stronger statements for important subtypes are also available:

```lean4
theorem roundtrip_static (t : Ty) (hs : t.IsStatic = true) (hv : t.Valid) (v : t.Val) :
    decode t (encode t v) = some v
    -- no length bound needed: static encodings are fixed-size

theorem roundtrip_bytes (bs : List UInt8) (h : bs.length < 2 ^ 256) :
    decode .bytes (encode .bytes bs) = some bs

theorem roundtrip_string (s : String) (h : s.toUTF8.size < 2 ^ 256) :
    decode .string (encode .string s) = some s
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
theorem isCanonical_encode (t : Ty) (hv : t.Valid) (v : t.Val) (hl : LenBound t v)
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
theorem decodeCanonical_encode (t : Ty) (hv : t.Valid) (v : t.Val) (hl : LenBound t v)
    (hb : (encode t v).length < 2 ^ 256) : decodeCanonical t (encode t v) = some v
```

The negative test suite in `Tests.lean` shows that the lenient decoder accepts
non-canonical inputs (swapped tails, gaps, duplicate offsets, misaligned offsets)
while the strict decoder rejects them all.

## Proof Structure

The proof is built in incremental layers, each reusable independently:

| Layer | Module | What it proves |
|---|---|---|
| **1. Byte plumbing** | `Bytes` | `pad32`, `splitEvery`, `take`/`drop` lemmas over appended buffers |
| **2. 32-byte alignment** | `Align` | `Aligned n := 32 ∣ n`, addition and multiplication lemmas (all `omega`) |
| **3. Word I/O** | `Word` | Reading/writing `UInt256` at aligned buffer offsets; `wordAt_append` |
| **4. Type universe** | `Ty` | ABI type grammar `Ty`, indexed value family `Val`, validity/staticness/head-size/length-bound predicates |
| **5. Static primitives** | `Static` | Standalone codecs for `uintM`, `intM`, `bool`, `address`, `bytesN`; strict bool/bytesN decoders |
| **6. Dynamic primitives** | `Dynamic` | Standalone codecs for `bytes`, `string`; prefix-tolerant decoder variant |
| **7. Static arrays** | `StaticArray` | `T[k]` over word-sized elements; `splitEvery`-based decoder |
| **8. Head/tail combinator** | `Parts` | The core ABI layout abstraction (`Part`, `encodeParts`, offset-correctness theorems); type-independent |
| **9. Full codec** | `Codec` | `Ty`-indexed `encode`/`decode` over the full universe; static roundtrip (Package A-C), dynamic roundtrip (Package D), unified `roundtrip` |
| **10. Canonical validation** | `Canonical` | `validate`/`IsCanonical`/`decodeCanonical`; completeness (C1), lenient completeness on canonical input (C2), soundness (C3), corollaries |
| **Tests** | `Tests` | Spec-vector encoding checks (sam, f, g), roundtrip regression, positive/negative canonical validation tests |

The separation of the **head/tail combinator (Parts)** from the **type-indexed codec (Codec)** is the key architectural decision:
the combinatorial heart of the ABI offset arithmetic is proved once on `List Part`,
then every type case in Codec reduces to it.

## Quick Example

```lean4
import EvmAbi

open EvmAbi
open EvmAbi.Ty

-- encode a static tuple (uint256, bool)
let t : Ty := .tuple [.uint 256, .bool]
let v : t.Val := (⟨42, by decide⟩, (true, ()))
let enc := encode t v
-- enc = word(42) ++ word(1)

-- roundtrip
example : decode t (encode t v) = some v :=
  roundtrip t (by
    simp [Valid, AllValid])
    v (by simp [LenBound, TupleLenBounds])
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
