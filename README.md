# abi-lean

EVM ABI encoding, decoding, and function selector computation, verified in Lean 4.

Based on the [Solidity ABI specification](https://docs.soliditylang.org/en/latest/abi-spec.html).

## Roundtrip Theorem

Decoding an ABI-encoded value recovers the original. Static types roundtrip unconditionally; dynamic-element containers (arrays, tuples) roundtrip under a well-formedness bound `enc.size < 2 ^ 256` — without it an encode can succeed while producing head pointers that overflow 32 bytes and corrupt the layout, so the *unconditional* statement is genuinely false, not merely unproven. The top-level results (no `sorry`):

```lean4
-- any well-formed type (nested structs included), decoded at offset 0
theorem roundtrip_wf (t : ABIType) (hwf : WellFormedType t)
    (v : ABIValue) (data : ByteArray) (hsz : data.size < 2 ^ 256)
    (henc : encode t v = Except.ok data) : decode t data 0 = Except.ok (v, data.size)

-- function-call level: encode an argument list then decode it back
theorem roundtrip_args_wff (types : List ABIType) (data : ByteArray) (values : List ABIValue)
    (hwf : ∀ t ∈ types, WellFormedType t) (hsz : data.size < 2 ^ 256)
    (henc : encodeArgs types values = Except.ok data) : decodeArgs types data 0 = Except.ok values
```

### Proof structure

Encoding and decoding are both structural folds over `ABIType` (`foldABIType`) via an `ABIVisitor`. Roundtrip proofs piggyback on the same fold: `WFFacts` bundles the three facts a type contributes (offset-general roundtrip, static size law, 32-byte alignment), and `wfFactsWF` builds them by structural recursion over every well-formed type — so compound types (arrays, nested tuples/structs) compose automatically, with no per-signature proof.

### Proven cases

| Type | Status | Theorems |
|---|---|---|
| `uintN` / `intN` | ✅ | `roundtrip_uint` / `roundtrip_int` (+ `roundtrip_offset_*`) |
| `bool` / `address` / `fixedBytesN` | ✅ | `roundtrip_bool` / `roundtrip_address` / `roundtrip_fixedBytes` |
| `bytes` / `string` | ✅ | `roundtrip_bytes` / `roundtrip_string` |
| `T[]` (dynamic) | ✅ WF | `roundtrip_array_wf` (both static- and dynamic-element) |
| `T[n]` (dynamic) | ✅ WF | `roundtrip_fixedArray_wf` |
| `(T1,...,Tn)` (dynamic) | ✅ WF | `roundtrip_tuple_wf` (static + dynamic dispatch) |
| any well-formed type (nested structs) | ✅ WF | `wfFactsWF`, `roundtrip_wf` |
| function args (`encodeArgs`/`decodeArgs`) | ✅ WF | `roundtrip_args_wff` |

✅ WF = proved under the well-formedness bound `enc.size < 2 ^ 256`; the one excluded case is an empty dynamic fixed-array (`fixedArray 0 e`, `e` dynamic), which encodes to 0 bytes and genuinely fails to decode. Full alignment lemmas (`szdvd_*`) and offset-generalized atom variants (`roundtrip_offset_*`, needed to decode elements from non-zero positions) are proved too. No `sorry`.

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

The proof surface also includes selector/hash size facts such as `EvmAbi.Hash.keccak256_size` and
`EvmAbi.Hash.functionSelector_size`, capturing the ABI-spec requirement that a function selector is
the first 4 bytes of the Keccak-256 hash of the canonical signature.

## License

MIT
