import EvmAbi.Bytes
import EvmAbi.Align
import EvmAbi.Word
import EvmAbi.Ty
import EvmAbi.Builder
import EvmAbi.Static
import EvmAbi.Dynamic
import EvmAbi.Codec
import EvmAbi.Codec.Roundtrip
import EvmAbi.Codec.Sound
import EvmAbi.Codec.Strict
import EvmAbi.Codec.ByteArray
import EvmAbi.ValBA
import EvmAbi.Parts
import EvmAbi.Packed
import EvmAbi.HumanReadable

/-!
# EvmAbi

Infrastructure for EVM ABI encoding/decoding, kept as a module tree separate
from the byte-order core (`Binary.*`, provided by the `lean-binary`
dependency).

Current contents (the `roadmap node N` tags in module docstrings record
the historical build order, nodes 1–8):

* `EvmAbi.Bytes`   — byte-list plumbing: `pad32`, take/drop lemmas
* `EvmAbi.Align`   — 32-byte alignment arithmetic (`Aligned`)
* `EvmAbi.Word`    — reading/writing 32-byte words (`UInt256`) at aligned offsets
* `EvmAbi.Ty`      — the full ABI type universe + type-indexed value family
* `EvmAbi.Builder` — the builder/reader layer: a chunk-tree `Builder` with
                  `O(1)` concatenation and a cached size, whose `run` fills a
                  pre-sized `ByteArray` in one pass and whose `toList` is the
                  denotation the proofs see; and the dual-cursor `Get2`
                  prefix-reader monad.  Decouples ABI layout logic from byte
                  plumbing at both ends
* `EvmAbi.Static`  — static primitives: `uintM`, `intM`, `bool`, `address`,
                  `bytesN`, with roundtrips (list form)
* `EvmAbi.Dynamic` — dynamic `bytes` / `string` with roundtrips, prefix decoder
* `EvmAbi.Codec`   — `Ty`-indexed `encode` (the specification, `List UInt8`)
                  and `encodeByteArray` (the same builder, run into a
                  `ByteArray`), plus the linear decoder `decode`
                  (`Get2` walkers) plus the bound-free static delegation
                  `decode_static_append`; the roundtrip / soundness /
                  strict-API families live in `EvmAbi.Codec.Roundtrip` /
                  `EvmAbi.Codec.Sound` / `EvmAbi.Codec.Strict`
                  (`IsCanonical` / `decodeStrict`: canonical buffers are
                  exactly the image of `encode`)
* `EvmAbi.Codec.ByteArray` — the same decoder over **offset cursors**: two
                  naturals into one shared `ByteArray` instead of two
                  sub-lists of a converted copy, with `decodeBA_eq` /
                  `decodeStrictBA_eq` proving it is the list walk on the
                  same bytes, so every theorem transports
* `EvmAbi.Parts`   — head/tail combinator: `Part`, `encodeParts`, offset theorems
* `EvmAbi.Packed`  — packed ABI (`abi.encodePacked`, Solidity's non-standard
                  packed mode): tight scalars, in-place dynamic payloads,
                  padded array elements; static packed roundtrip
* `EvmAbi.HumanReadable` — parser for Solidity-style human-readable ABI
                  signatures into `Ty` and `AbiItem` representations

`EvmAbi.HumanReadable.Meta` — the `ty!` / `item!` / `params!` macros — is
deliberately *not* re-exported here: it needs `import Lean`, and this library is
otherwise free of the Lean frontend.  Import it explicitly to use the macros.
-/
