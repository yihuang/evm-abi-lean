# Benchmarks and performance profile

Native-code benchmark results for the `EvmAbi` codec, produced by
`Bench.lean` (build with `lake build bench`, run with
`.lake/build/bin/bench`).  The workload set, the measurement
methodology, and the findings below are all reproducible.

## Methodology

* The executable is a `lean_exe` target, so every measured function is
  the **C-backend compiled** code, not the elaborator or the VM.
* Timing uses `IO.monoNanosNow` around a fold executed inside
  `IO.Ref.modify`, and the measured calls are wrapped in `@[noinline]`
  definitions.  Both are required: the Lean C backend freely hoists
  pure subterms, so a naive `let t0 ← …; f; let t1 ← …` (or a fold that
  re-uses an expression already bound to a buffer) ends up measuring two
  adjacent clock reads or a `List.length` walk instead of the call.
* Iteration counts are adaptive (target ~200 ms per line); `B/op` is the
  payload size, so the `MB/s` column is comparable across workloads.

## Results (2026-08-01, `v4.32.0`, C backend)

Baseline was measured before the session's fixes; the *after* column is
the current tree (`#3` slimmed `UInt256` word codec in `Binary`, `#4`
static-element fast path in `decodeElems`; `#2` was attempted and
reverted, see below).  Throughput in MB/s; representative per-op µs in
parentheses.

| workload | payload | encode before → after | decode before → after |
|---|---|---|---|
| `words/2048` | 64 KiB (2048 × uint256) | 12.0 → 16.0 (5451→4094 µs) | 14.3 → 19.3 (4588→3393 µs) |
| `words/8192` | 256 KiB | 8.7 → 11.9 (30169→22081 µs) | 12.4 → 17.9 (21126→14691 µs) |
| `words/32768` | 1 MiB | 7.9 → 8.7 (133575→120297 µs) | 12.7 → 17.4 (82793→60427 µs) |
| `fixed/4096` | 128 KiB fixed array | 11.5 → 15.0 (11428→8751 µs) | 13.3 → 18.9 (9825→6952 µs) |
| `bytes/1m` | 1 MiB dynamic bytes | 19.5 → 20.1 | 38.0 → 43.3 |
| `barr/1024` | array of 1024 × bytes | 15.5 → 17.5 (7400→6560 µs) | 18.1 → 21.8 (6351→5274 µs) |
| `barr/4096` | array of 4096 × bytes | 9.7 → 11.0 | 16.1 → 17.7 |
| `nested/32/32` | array of arrays of bytes | 12.0 → 13.4 (8364→7469 µs) | 17.4 → 21.8 (5797→4613 µs) |
| `mixed` | 5-field tuple | 16.5 → 21.4 (25→19 µs) | 22.4 → 28.1 (18→14 µs) |
| `string/8k` | 8 KiB string | 32.2 → 35.4 | 49.0 → 46.0 |
| `packed/fixed8/4096` | packed 4096 × uint8 | 16.9 → 23.7 (7775→5522 µs) | 11.3 → 16.8 (11619→7816 µs) |

`decodeStrict` costs the same as `decode` plus the exact-consumption
check; it tracks `decode` in every row and is not a separate bottleneck.

### Micro-benchmarks (per-operation cost)

| primitive | before | after |
|---|---|---|
| `UInt256.toBEBytes` (one 32-byte word out) | ~0.8 µs | ~0.6 µs |
| `UInt256.ofBEBytes` (one 32-byte word in) | ~1.0 µs | ~0.2–0.3 µs |
| `decodeUint` (front word read) | ~1.6–2 µs | ~0.8 µs |
| direct word-walk reference (2048 words, no `Get2`) | ~3.3 ms | ~2.7 ms |
| `pad32` on 64 KiB | ~1.7 ms (40 MB/s) | ~1.5 ms (43 MB/s) |
| `decodeBytesPrefix` on 64 KiB | ~0.9 ms (74 MB/s) | ~0.8 ms (80 MB/s) |
| `Builder.toList` of 1024 composed words | ~0.8 ms (40 MB/s) | ~0.7 ms (47 MB/s) |

## Scaling

The linear-decoder work from #27 holds: word decode grows 2048 → 8192 →
32768 elements roughly linearly (4.6 ms → 21.1 ms → 82.8 ms before;
3.4 ms → 14.7 ms → 60–80 ms after).  Array-of-bytes decode is likewise
linear.  **Encode** is mildly superlinear at the 1 MiB scale
(`barr/4096`: 4.6×, then 6.4× per 4×), which is GC pressure from
allocation, not a walk that re-scans the buffer.

## Where the time goes

Per-word accounting for an all-`uint256` array:

* **encode ≈ 2.0–2.6 µs/word** (was ~2.7 µs) — `toBEBytes` alone is
  ~0.6 µs, and the `Part` machinery materializes each head at least
  twice (`headSizes` computes `head.toList.length`, then `Builder.toList`
  materializes again), plus `vs.map partOf` and list building.
* **decode ≈ 1.6–1.9 µs/word** (was 2.2–2.6 µs) — `decodeUint`
  (~0.8 µs after `#3`) plus the walker glue (`Get2` result construction,
  `drop 32`, conses) — the `#4` static fast path removed most of the
  `Get2` bind/closure overhead.

Root causes, in order of impact:

1. **`List UInt8` as the byte representation.** Every byte is a heap
   cons cell; a word round-trip allocates ~100 cells of intermediates
   (`encodeBEU` still does LE + reverse; `decode` allocates result
   structures per element).  `Builder.toList` and `pad32` both plateau
   at ~40–50 MB/s on pure list building — that is the representation's
   ceiling even before any codec logic.
2. **The per-word `UInt256` byte codec** — now slimmed (`#3`): the old
   `List Nat` + reverse + map pipeline became a direct `foldl`/one-pass
   encode; `ofBEBytes` dropped from ~1.0 to ~0.2 µs.
3. **Encoder double materialization.** `putHeads` calls
   `tail.toList.length` per dynamic part (materializing each tail), then
   `putTails`/`toList` materializes them again; nested dynamic layouts
   re-materialize subtrees once per level.  Attempts to materialize once
   eagerly regressed (see `#2` below); the honest fix is a size-carrying
   `Builder` or a `ByteArray` payload.
4. **Allocation/GC.** RSS peaks ~40× the encoded size on a 6.4 MiB
   decode; this is what makes large encodes superlinear.

## Fixes implemented in this session

### `#3` — slimmed the `Binary` word codec (done)

`Binary/UInt8.lean`'s `encodeLEU`/`encodeBEU`/`decodeLEU`/`decodeBEU`
no longer go through a `List Nat` intermediate (`encodeLE` +
`natsToUInt8`, `uint8ToNats` + `decodeBE`): they build/decode the
`UInt8` list directly (`encodeLEU` one pass + one `reverse` for BE;
`decodeBEU` a single allocation-free `foldl`).  All theorem statements
are unchanged; the roundtrip and bound proofs were re-proved against the
new definitions (the `foldl`/`foldr` power-sum identities behind the
single-pass `decodeBEU` are new lemmas).  Effect: `ofBEBytes` ~1.0 →
0.2 µs, `decodeUint` ~1.6–2 → 0.8 µs, encode of word-heavy workloads
~20–25% faster, decode ~10–30% faster.  Changes live in the `binary`
dependency (`.lake/packages/binary`); the patch is in
`docs/binary-word-codec.patch` for the fork/PR, and `lakefile.toml`
still pins the upstream `main` rev.

### `#4` — static fast path in `decodeElems` (done)

`decodeElems` now branches on `t.isStatic`: static elements are read with
a direct loop (`decode t head` + recursion, no `Get2` bind/pure closures
per element), dynamic elements keep the monadic walk unchanged.  The
walker theorem families (`decodeElems_static_append`, `decodeElems_roundtrip`,
`decodeElems_sound`) were split into static/dynamic cases; the static
cases use the new `decode_static_at_offset` lemma (a static element's
encoding sits at its head offset).  Effect: word decode ~30% faster,
dynamic-array and tuple decode ~20% faster, packed decode ~30% faster;
the gap to the direct-walk reference (`micro/directWords`) narrowed from
~0.7 ms to ~0.6 ms per 2048 words.

### `#2` — `putParts` single materialization (attempted, reverted)

An eager single-materialization `putParts` (materialize every head/tail
once, emit the tails as-is) was implemented and measured **~30% slower**
on dynamic arrays (`barr/1024` encode 7.4 → 9.8 ms): holding all
materialized tails live at once roughly doubles peak memory and GC
pressure versus the classical composition's transient size pass
(`putHeads`' `tail.toList.length`), and the extra list copy (flatten /
re-walk) ate the saving.  Reverted; `putParts` keeps the composition.
Removing the second materialization for real needs a size-carrying
`Builder`/`Part` (a `size` field maintained by `ofList`/`append`) or a
`ByteArray` payload — either is a larger, proof-heavy change.

### `#1` — ByteArray-backed fast codec (deferred)

Still the biggest remaining lever (est. 20–100×) and the biggest change:
the entire theorem layer is stated over `List UInt8`.  Keep the verified
`List` codec as the reference and add a `ByteArray`-based fast path with
boundary conversion; see the proposal below.

## Proposed next steps

Prioritized by (impact × risk), all compatible with keeping the verified
`List`-based theorem layer as the reference:

1. **ByteArray-backed fast codec (biggest win, biggest effort).**
   Add `EvmAbi.Fast` (or a `ByteArray` variant of `Builder`/`Get2`)
   with big-endian word reads/writes as direct loops and `ByteArray`
   payload copies.  Keep the `List UInt8` API and theorems untouched;
   convert at the boundary (`buf.data.toList`/`toByteArray`).  Expected
   20–100× on throughput.  Proof strategy: reuse the existing theorems
   by bridging, and/or `native_decide`-style regression tests on the
   fast path.
2. **Size-carrying `Builder` (medium risk, ~1.5–2× on dynamic encode).**
   Add a `size : Nat` field to `Builder` (maintained by `ofList`/`append`)
   so `putHeads` reads `tail.size` instead of `tail.toList.length` — the
   second materialization disappears without holding tails live.  Touches
   every `Builder` construction and its proofs, so it is a moderate
   sweep, but it is the honest fix for the `putParts` doubling that
   eager materialization failed to capture.
3. **Slim the word codec further (medium win on word-heavy loads).**
   The current slimmed `encodeBEU` still does LE+reverse (two passes);
   a direct MSB-first loop needs `256^(len-1)` per byte, so the reverse
   stays unless the target is `ByteArray` (part of fix 1).
4. **Shave the decoder walker glue further.**  The `Get2` result
   construction per element (4-field record + subtype + cons) is now the
   dominant remaining walker cost; a specialized accumulator for
   `decodeElems` could recover another ~10% on word-heavy decodes, at
   the cost of the theorem split already paid for `#4`.

Measured overheads to watch when evaluating fixes: `Builder.toList`
(~45 MB/s) and `pad32` (~43 MB/s) must improve together with the word
codec, or they become the new floor.
