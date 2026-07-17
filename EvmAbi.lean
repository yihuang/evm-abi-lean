import EvmAbi.Bytes
import EvmAbi.Align
import EvmAbi.Word
import EvmAbi.Ty
import EvmAbi.Static
import EvmAbi.Dynamic
import EvmAbi.Codec
import EvmAbi.Tests

/-!
# EvmAbi

Infrastructure for EVM ABI encoding/decoding, kept as a module tree separate
from the byte-order core (`Binary.*`).

Current contents (roadmap nodes 1–5):

* `EvmAbi.Bytes`   — byte-list plumbing: `pad32`, `splitEvery`, take/drop lemmas
* `EvmAbi.Align`   — 32-byte alignment arithmetic (`Aligned`)
* `EvmAbi.Word`    — reading/writing 32-byte words (`UInt256`) at aligned offsets
* `EvmAbi.Ty`      — the ABI type universe + type-indexed value family
* `EvmAbi.Static`  — static primitives: `uintM`, `intM`, `bool`, `address`,
                  `bytesN`, with roundtrips
* `EvmAbi.Dynamic` — dynamic `bytes` / `string` with roundtrips
* `EvmAbi.Codec`   — `Ty`-indexed encode/decode dispatch + unified roundtrip
* `EvmAbi.Tests`   — computation-checked regression instances

Next nodes (not yet implemented): static arrays, head/tail combinator,
full type universe (S3/S4).
-/
