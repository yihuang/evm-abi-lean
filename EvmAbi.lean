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
import EvmAbi.Codec.Runtime
import EvmAbi.ValBA
import EvmAbi.Parts
import EvmAbi.Packed
import EvmAbi.Compile
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
                  `bytesN`, with roundtrips
* `EvmAbi.Dynamic` — dynamic `bytes` / `string` with roundtrips, prefix decoder
* `EvmAbi.Spec`    — the specification codec (`EvmAbi.Codec` and its
                  `Roundtrip` / `Sound` / `Strict` families): list-based
                  `Spec.encode` / `Spec.decode` / `Spec.decodeStrict` and
                  `Spec.IsCanonical`, the surface every theorem is stated
                  over
* `EvmAbi.Codec.Runtime` — the **runtime codec users run**: `encode`
                  (`ByteArray` out), `decode` / `decodeStrict` (`ValBA`
                  values out), `IsCanonical`, plus the encoder agreement
                  `toList_putBA` that ties it to `Spec`
* `EvmAbi.Codec.ByteArray` — runtime decoder internals: offset primitives,
                  the `ValBA` walkers, and the agreement lemmas that carry
                  the `Spec` theorems onto the `ByteArray` side
* `EvmAbi.Parts`   — head/tail combinator: `Part`, `encodeParts`, offset theorems
* `EvmAbi.Packed`  — packed ABI (`abi.encodePacked`, Solidity's non-standard
                  packed mode): tight scalars, in-place dynamic payloads,
                  padded array elements; static packed roundtrip
* `EvmAbi.Compile` — the ABI compiler's target language: a small abstract
                  machine for the head/tail layout (`Acc.start`/`static`/
                  `dyn`/`finish` plus one element loop) whose every step is
                  proved against `putBA`, and `Denotes`, the contract a
                  compiled encoder satisfies
* `EvmAbi.HumanReadable` — parser for Solidity-style human-readable ABI
                  signatures into `Ty` and `AbiItem` representations

`EvmAbi.HumanReadable.Meta` — the `ty!` / `item!` / `params!` macros — is
deliberately *not* re-exported here: it needs `import Lean`, and this library is
otherwise free of the Lean frontend.  Import it explicitly to use the macros.
-/
