import EvmAbi.ABI
import EvmAbi.Encode
import EvmAbi.Decode
import EvmAbi.Hash

/-!
# ABILean — EVM ABI encoding/decoding in Lean 4

This library provides:
- `ABILean.ABI`: Core ABI types (`ABIType`, `ABIValue`) and byte-level helpers
- `ABILean.ABI.Encode`: Encode ABI values to bytes
- `ABILean.ABI.Decode`: Decode bytes to ABI values
- `ABILean.Hash`: Keccak-256 and Ethereum function selectors

See the online <https://docs.soliditylang.org/en/latest/abi-spec.html>
for the Solidity ABI specification.
-/
