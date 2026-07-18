import EvmAbi.Bytes
import EvmAbi.Align
import EvmAbi.Word
import EvmAbi.Ty
import EvmAbi.Static
import EvmAbi.Dynamic
import EvmAbi.Codec
import EvmAbi.StaticArray
import EvmAbi.Parts
import EvmAbi.Hash

/-!
# EvmAbi

Infrastructure for EVM ABI encoding/decoding, kept as a module tree separate
from the byte-order core (`Binary.*`, provided by the `lean-binary`
dependency).

Current contents (roadmap nodes 1–8):

* `EvmAbi.Bytes`   — byte-list plumbing: `pad32`, `splitEvery`, take/drop lemmas
* `EvmAbi.Align`   — 32-byte alignment arithmetic (`Aligned`)
* `EvmAbi.Word`    — reading/writing 32-byte words (`UInt256`) at aligned offsets
* `EvmAbi.Ty`      — the full ABI type universe + type-indexed value family
* `EvmAbi.Static`  — static primitives: `uintM`, `intM`, `bool`, `address`,
                  `bytesN`, with roundtrips
* `EvmAbi.Dynamic` — dynamic `bytes` / `string` with roundtrips, prefix decoder
* `EvmAbi.Codec`   — `Ty`-indexed encode/decode for all types + unified roundtrip;
                  the function-argument level (`encodeArgs`/`decodeArgs`/`roundtrip_args`)
* `EvmAbi.StaticArray` — static arrays `T[k]` over word-sized elements
* `EvmAbi.Parts`   — head/tail combinator: `Part`, `encodeParts`, offset theorems
* `EvmAbi.Hash`    — Keccak-256 (executable) + the four-byte function selector

Regression tests live in the root `Tests.lean` (the `Tests` lake target, kept out
of the core library): Solidity spec vectors, roundtrips, selector vectors, decoder
rejection. Run with `lake build Tests`.

Node 8 (complete): the full type universe (uint/int/bool/address/bytesN/
bytes/string/array/fixedArray/tuple), the `Ty`-indexed codec with the
unified roundtrip `roundtrip`, the function-argument level, and selectors.
-/
