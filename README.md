# abi-lean

EVM ABI encoding and decoding, formally verified in Lean 4.

Conforms to the [Solidity ABI Specification](https://docs.soliditylang.org/en/latest/abi-spec.html).
The central result is a **roundtrip theorem**: for every valid ABI type `t` and every value `v`
whose encoding fits in `2^256` bytes, decoding the encoding recovers the original value.

```lean4
theorem roundtrip (t : Ty) (hv : t.Valid) (v : t.Val) (hl : LenBound t v)
    (hb : (encode t v).length < 2 ^ 256) : decode t (encode t v) = some v
```

No `sorry`.  All types (`uintM`, `intM`, `bool`, `address`, `bytesM`, `bytes`, `string`,
`T[]`, `T[k]`, `(T₁,…,Tₙ)`) and arbitrarily nested combinations thereof are covered.

## Architecture

| Module | Purpose |
|---|---|
| `Ty`      | Full ABI type grammar, indexed value family `Val`, validity & length-bound predicates |
| `Bytes`   | Byte-list plumbing (`pad32`, `splitEvery`, take/drop lemmas) |
| `Align`   | 32-byte alignment arithmetic (`Aligned n := 32 ∣ n`) |
| `Word`    | Reading/writing `UInt256` at aligned buffer offsets |
| `Static`  | Standalone codecs for `uintM`, `intM`, `bool`, `address`, `bytesN` |
| `Dynamic` | Standalone codecs for `bytes`, `string`, plus prefix-tolerant variant |
| `Parts`   | Head/tail combinator (`Part`, `encodeParts`, offset correctness theorems) |
| `StaticArray` | Static arrays `T[k]` over word-sized elements |
| `Codec`   | `Ty`-indexed `encode`/`decode` for the full universe, unified roundtrip proof |
| `Tests`   | Spec-vector encoding checks, roundtrip regression, error-case tests (separate target) |

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

Tests (spec vectors, roundtrips, error cases) live in a separate target and
run via `native_decide` / `decide` checks in `Tests.lean`:

```bash
lake test          # build and run all test targets
lake build Tests   # compile the test module
```

## License

MIT
