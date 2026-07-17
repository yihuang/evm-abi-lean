import EvmAbi.Bytes
import EvmAbi.Align
import EvmAbi.Word
import EvmAbi.Ty
import EvmAbi.Static
import EvmAbi.Dynamic
import EvmAbi.Codec
import EvmAbi.StaticArray
import EvmAbi.Parts
import EvmAbi.Tests

/-!
# EvmAbi

Infrastructure for EVM ABI encoding/decoding, kept as a module tree separate
from the byte-order core (`Binary.*`, provided by the `lean-binary`
dependency).

Current contents (roadmap nodes 1–7, plus the node-8 type-universe base):

* `EvmAbi.Bytes`   — byte-list plumbing: `pad32`, `splitEvery`, take/drop lemmas
* `EvmAbi.Align`   — 32-byte alignment arithmetic (`Aligned`)
* `EvmAbi.Word`    — reading/writing 32-byte words (`UInt256`) at aligned offsets
* `EvmAbi.Ty`      — the ABI type universe + type-indexed value family
* `EvmAbi.Static`  — static primitives: `uintM`, `intM`, `bool`, `address`,
                  `bytesN`, with roundtrips
* `EvmAbi.Dynamic` — dynamic `bytes` / `string` with roundtrips, prefix decoder
* `EvmAbi.Codec`   — `Ty`-indexed encode/decode dispatch + unified roundtrip
* `EvmAbi.StaticArray` — static arrays `T[k]` over word-sized elements
* `EvmAbi.Parts`   — head/tail combinator: `Part`, `encodeParts`, offset theorems
* `EvmAbi.Tests`   — computation-checked regression instances

Next node (not yet implemented): node 8 — the full type universe (compound
constructors: fixed/dynamic arrays and tuples) and calldata, built on the
head/tail combinator of `EvmAbi.Parts`.
-/
