# abi-lean

EVM ABI encoding, decoding, and function selector computation, verified in Lean 4.

Based on the [Solidity ABI specification](https://docs.soliditylang.org/en/latest/abi-spec.html).

## Roundtrip Theorem

The central correctness property:

```lean4
theorem roundtrip (t : ABIType) (v : ABIValue) (data : ByteArray)
    (henc : encode t v = Except.ok data) : decode t data 0 = Except.ok (v, data.size)
```

If encoding succeeds, decoding the resulting bytes recovers the original value and correctly reports the byte length consumed.

### Proof structure

A second ABIVisitor instance, `RoundtripVisitor`, carries per-type roundtrip proofs piggybacking on the same structural fold (`foldABIType`) that encoding and decoding use, enabling compositional proofs for compound types.

### Proven cases

| Type | Status | Theorems |
|---|---|---|
| `uintN` | ✅ | `roundtrip_uint`, `roundtrip_offset_uint` |
| `intN` | ✅ | `roundtrip_int`, `roundtrip_offset_int` |
| `bool` | ✅ | `roundtrip_bool`, `roundtrip_offset_bool` |
| `address` | ✅ | `roundtrip_address`, `roundtrip_offset_address` |
| `fixedBytesN` | ✅ | `roundtrip_fixedBytes`, `roundtrip_offset_fixedBytes` |
| `bytes` | ✅ | `roundtrip_bytes` |
| `string` | ✅ | `roundtrip_string` |
| `T[]` | 🚧 | dynamic `onArray` case |
| `T[n]` | 🚧 | dynamic sub-case, static cons induction step |
| `(T1,...,Tn)` | 🚧 | `onTuple` |
| **all** | 🚧 | main `roundtrip` theorem (blocks on above) |

The offset-generalized variants (`roundtrip_offset_*`) prove the property at arbitrary offsets within a larger buffer — essential for composing array/tuple proofs where elements are decoded from non-zero positions.

## Usage

```lean4
import EvmAbi

open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode

let t : ABIType := .uint (ByteSize.ofLen 32 (by omega))
let v : ABIValue := .uint 42
let encoded := encode t v
let decoded := decode t (Except.ok? encoded) 0
-- roundtrip theorem guarantees: decoded = ok(.uint 42, 32)
```

## Tests

```bash
lake build
lake exe abi-lean-test
```

Covers spec encoding vectors, decoding, 12 standard Ethereum function selectors (transfer, balanceOf, approve, ...), 40+ roundtrip assertions across all type categories, and error cases.

## License

MIT
