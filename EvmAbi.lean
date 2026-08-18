import EvmAbi.Bytes
import EvmAbi.Align
import EvmAbi.Word
import EvmAbi.Ty
import EvmAbi.Builder
import EvmAbi.Static
import EvmAbi.Dynamic
import EvmAbi.Spec
import EvmAbi.Spec.Roundtrip
import EvmAbi.Spec.Sound
import EvmAbi.Spec.Strict
import EvmAbi.Codec
import EvmAbi.ValBA
import EvmAbi.Parts
import EvmAbi.Packed
import EvmAbi.Compile
import EvmAbi.Compile.Decode
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
* `EvmAbi.Spec`    — the specification codec (`EvmAbi.Spec` and its
                  `Roundtrip` / `Sound` / `Strict` families): list-based
                  `Spec.encode` / `Spec.decode` / `Spec.decodeStrict` and
                  `Spec.IsCanonical`, the surface every theorem is stated
                  over
* `EvmAbi.Codec`    — the **runtime codec users run**: `encode`
                  (`ByteArray` out), `decode` / `decodeStrict` (`ValBA`
                  values out), `IsCanonical`, plus the encoder agreement
                  `toList_putBA` that ties it to `Spec`
* `EvmAbi.Codec.ByteArray` — internal runtime decoder details:
                  offset primitives, the `ValBA` walkers, and the agreement
                  lemmas that carry the `Spec` theorems onto the `ByteArray`
                  side.  Nested under `EvmAbi.Codec` because it is an
                  implementation detail of the runtime layer
* `EvmAbi.Parts`   — head/tail combinator: `Part`, `encodeParts`, offset theorems
* `EvmAbi.Packed`  — packed ABI (`abi.encodePacked`, Solidity's non-standard
                  packed mode): tight scalars, in-place dynamic payloads,
                  padded array elements; static packed roundtrip
* `EvmAbi.Compile` — the ABI compiler's target language: a small abstract
                  machine for the head/tail layout (`Acc.start`/`static`/
                  `dyn`/`finish` plus one element loop) whose every step is
                  proved against `putBA`, and `Denotes`, the contract a
                  compiled encoder satisfies
* `EvmAbi.Compile.Decode` — the same for the decoder: the component readers
                  (`elemStatic`/`elemDyn`), the chain `cons` and loop `elems`
                  built on them, and the three compound clauses — all proved
                  against `decodeBAVal` — plus `Reads`, the contract a compiled
                  decoder satisfies
* `EvmAbi.HumanReadable` — parser for Solidity-style human-readable ABI
                  signatures into `Ty` and `AbiItem` representations

`EvmAbi.HumanReadable.Meta` — the `ty!` / `item!` / `params!` macros — and
`EvmAbi.Compile.Meta` — the `abi_encoder` / `abi_decoder` / `abi_codec`
commands — are deliberately *not* re-exported here: they need `import Lean`,
and this library is otherwise free of the Lean frontend.  Import them
explicitly to use the macros.
-/

namespace EvmAbi

-- Re-export the user-facing runtime API at the root namespace, as documented:
-- users write `EvmAbi.encode`, `EvmAbi.decode`, `EvmAbi.decodeStrict`, and
-- `EvmAbi.IsCanonical` without opening `EvmAbi.Codec`.
export EvmAbi.Codec
  (encode decode decodeStrict IsCanonical
   decodeStrict_encode encode_of_decodeStrict
   decodeStrict_eq_some_iff isCanonical_iff)

end EvmAbi
