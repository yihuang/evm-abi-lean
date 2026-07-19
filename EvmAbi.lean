import EvmAbi.Bytes
import EvmAbi.Align
import EvmAbi.Word
import EvmAbi.Ty
import EvmAbi.Static
import EvmAbi.Dynamic
import EvmAbi.Codec
import EvmAbi.StaticArray
import EvmAbi.Parts

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
* `EvmAbi.Codec`   — `Ty`-indexed encode/decode for all types + unified roundtrip
* `EvmAbi.StaticArray` — static arrays `T[k]` over word-sized elements
* `EvmAbi.Parts`   — head/tail combinator: `Part`, `encodeParts`, offset theorems
* `EvmAbi.Canonical` — canonical-layout validation: `validate`, `IsCanonical`,
                  `decodeCanonical`, and the C1–C3 theorems (encodings
                  validate; canonical input lenient-decodes; canonical
                  buffers are exactly the image of `encode`)

Node 8 (complete): the full type universe (uint/int/bool/address/bytesN/
bytes/string/array/fixedArray/tuple), the `Ty`-indexed codec with the
unified roundtrip `roundtrip`, and canonical strictness on top.
-/
