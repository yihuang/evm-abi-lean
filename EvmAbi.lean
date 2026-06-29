import EvmAbi.ABI
import EvmAbi.Encode
import EvmAbi.Decode
import EvmAbi.Hash


/-!
# EvmAbi — EVM ABI encoding/decoding in Lean 4

This library provides:
- `EvmAbi.ABI`: Core ABI types (`ABIType`, `ABIValue`) and byte-level helpers
- `EvmAbi.ABI.Encode`: Encode ABI values to bytes
- `EvmAbi.ABI.Decode`: Decode bytes to ABI values
- `EvmAbi.Hash`: Keccak-256 and Ethereum function selectors
- `EvmAbi.Roundtrip`: Roundtrip theorem and proofs

See the online <https://docs.soliditylang.org/en/latest/abi-spec.html>
for the Solidity ABI specification.
-/
