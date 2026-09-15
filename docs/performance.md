# Performance

Every number here comes from `Bench`, on an Apple M-series machine:

```bash
lake build bench && ./.lake/build/bin/bench
```

Last refreshed against `f8f7a10` plus the `address` fix below.  Re-run the
whole bench when you touch a codec path, not just the row you aimed at — that
regression went unrecorded for two releases.

**Compiled only.** The builder rests on the `@[extern]` `ByteArray.push` and
`ByteArray.emptyWithCapacity`, so an interpreted run (`lake env lean --run
Bench.lean`) inverts most of these rows.

Each codec exists twice: a `List UInt8` *specification* that the proofs are
stated over, and a `ByteArray` *runtime* form proved equal to it. Nothing
below is a second implementation to keep in step — `encode = (put t v).toList`
and `encodeByteArray = (put t v).run` are the same encoder materialised two
ways.

## The encoder: three tiers

`Spec.encode` concatenates with `++` at every level, so a `d`-deep value has
its bytes re-copied `d` times. `Builder` makes concatenation an `O(1)`
constructor and `run` fills a pre-sized `ByteArray` in one pass.

| shape | `Spec.encode` + `toByteArray` | `Spec.encodeByteArray` | speedup |
|---|---|---|---|
| `bytes[]`, 500 × 256 B | 2065 µs | 388 µs | 5.3× |
| `bytes[]`, 2000 × 256 B | 8202 µs | 1605 µs | 5.1× |
| `uint256[]`, 1000 full-width words | 956 µs | 503 µs | 1.9× |
| nested tuples, depth 50 | 1682 µs | 44 µs | 38× |
| nested tuples, depth 200 | 24768 µs | 178 µs | 139× |

The flat rows show the constant factor; the nested rows show the asymptotics —
quadratic against linear, so the gap widens with depth.

Both are *specifications* now. `encode` builds no tree: one pass sizes every
dynamic subvalue, a second writes the encoding forward into a buffer sized
exactly once, reading each offset off that size tree in `O(1)`. Against the
builder, on packed `ValBA` payloads:

| shape | `Spec.encodeByteArray` | `encode` | speedup |
|---|---|---|---|
| `bytes[]`, 500 × 256 B | 384 µs | 21 µs | 18× |
| `bytes[]`, 2000 × 256 B | 1553 µs | 83 µs | 19× |
| `bytes[]`, 2000 × 100 B (unaligned) | 845 µs | 89 µs | 9.5× |

Part of that gap is the payload type — the specification's payloads are
`List UInt8` — and the rest is the tree: `putBA` builds a `Part`, two
`Builder`s and an `append` node per component for `emit` to walk.

Both columns also depend on how fast one 32-byte word is produced, which is
`lean-binary`'s job: its `Binary.Fast` peels eight bytes at a time through a
`UInt64` instead of one at a time through bignum division, and registers the
result with `@[csimp]`, so this library needed no change to benefit. That is
worth 4.1× to the specification encoder and 5.0× to `Spec.encodeByteArray` on
the `uint256[]` row — and, because it sits below both, it is why the builder's
own advantage there is only 1.9×.

## The decoder: offset cursors against list cursors

`Spec.decode` walks two `List UInt8` cursors; `decodeStrict` walks the same
layout as two *offsets* into one shared `ByteArray`, reading words with an
indexed read and materialising only the payloads that a `bytes`/`string`/
`bytesN` value actually is. Decoding a `bytes[]`:

    500 elements  (160KB)   3370 ->  968 us    3.5x
    2000 elements (640KB)  13635 -> 3907 us    3.5x

## Compiled codecs against generic ones

`abi_codec` emits a codec specialised to one type. Compilation removes the
*layout* overhead and nothing else — the `Ty` match per value, the `isStatic`
test per component and per array element, the `List Part` a tuple or array
allocates, and the three walks `putParts` makes over it — so the win depends
on how expensive the words themselves are.

Encoding, medians of three runs:

| shape | `encode` | compiled | |
|---|---|---|---|
| `(bool × 8)` | 201 ns | **176 ns** | 1.14× faster |
| `(address, uint256)` — one call's arguments | **73 ns** | 285 ns | 3.9× slower |
| `(address, uint256, bytes)` | **228 ns** | 382 ns | 1.68× slower |
| `bool[]`, 100 elements | **1.49 µs** | 2.54 µs | 1.71× slower |
| `uint256[]`, 100 full-width words | **1.48 µs** | 3.83 µs | 2.59× slower |
| `(uint256, bool)[]`, 100 elements | **5.81 µs** | 8.04 µs | 1.38× slower |
| `bytes[]`, 100 × 256 B | **3.68 µs** | 11.13 µs | 3.02× slower |

**Compilation mostly no longer pays on the encode side.** It removes the
*layout* overhead — the `Ty` match per value, the `isStatic` test per
component, the `List Part` a tuple or array allocates — which is what the
streaming encoder removed for every type at once, and `abi_codec` still
assembles a `Builder`. The gap tracks how much layout there was: widest on
`bytes[]`, and reversed only on `(bool × 8)`, which has almost none and where
the compiled codec's straight-line head section edges ahead.  The two
`address` rows are the section below, not a layout effect.

### `address`: regressed at #45, fixed here

#45 made the payload raw bytes, but `encodeAddress` is stated through the
value (`encodeUint (decodeBEU a)`) — so both codecs moved bytes the buffer
already held by way of a bignum. Against a build of #45's parent:

| generic row | #44 | #45 | now |
|---|---|---|---|
| `(address, uint256)` encode | 56 ns | 254 ns | **74 ns** |
| `(address, uint256, bytes)` encode | 192 ns | 403 ns | **220 ns** |
| `(address, uint256)` decode | 171 ns | 383 ns | **171 ns** |

`encodeAddress_eq` and `decodeAddress_eq_window` put the word at twelve zero
bytes then the address, so encoding is a `pushZeros32` and an append, decoding
a zero check and one `extract`.

Still open: the compiled encoder builds through `putAddress` (285 ns above vs
the generic 73), and #46 left `address[]` unfused because this allocation
dwarfed the match it would remove.

Decoding was untouched by the streaming-encoder work and still mostly pays:

| shape | `decodeStrict` | compiled | |
|---|---|---|---|
| `(bool × 8)` | 560 ns | **269 ns** | 2.08× faster |
| `(uint256, bool)[]`, 100 elements | 20.31 µs | **11.08 µs** | 1.83× faster |
| `(address, uint256)` | 174 ns | **111 ns** | 1.57× faster |
| `bool[]`, 100 elements | 7.39 µs | **4.89 µs** | 1.51× faster |
| `bytes[]`, 100 × 256 B | 10.28 µs | **7.99 µs** | 1.29× faster |
| `uint256[]`, 100 full-width words | **3.03 µs** | 5.47 µs | 1.81× slower |

The one loss is `uint256[]`, where the generic decoder has a fused `uint`
array walk that the compiled one does not.

## Where the time goes

Every table above compares two ways of assembling the same bytes, so they
measure *layout*. `Bench`'s word-codec section measures the bytes themselves,
which for ordinary calldata is the larger half: addresses, token amounts and
hashes are all full-width, and `uint256[]` costs ~20× per element what
`bool[]` does through the very same layout.

An ABI word used to be a `Nat` — `UInt256` wrapped `BitVec 256` = `Fin (2 ^ 256)`,
a heap GMP bignum above `2 ^ 63`, so every `n >>> 64` on the way out and every
`acc <<< 64` on the way back in allocated. `UInt256` is four `UInt64` limbs now
(lean-binary#5), which settled the write side: writing goes straight from the
limbs and no longer touches a bignum at any width. Per word:

| | full width | value < 2^63 |
|---|---|---|
| write 32 big-endian bytes | 18 ns | 18 ns |
| read 32 big-endian bytes | 772 ns | 22 ns |
| read into limbs, `ba[i]!` | 16 ns | 16 ns |

The write columns have converged and dropped: lean-binary writes a word at a
known offset with its bounds proved rather than re-checked per byte, so the
32 `ByteArray.push`es that cost 79 ns are gone. Reading is the row still to
close — `Binary.decodeBEBytesFrom` accumulates into a `Nat`, so a full-width
read is 46× a limb read, and even a small one is 6 ns above it.

That 6 ns is collectable where the value is known small, which for the ABI is
every length and offset word: `natAtBAFast` reads the four limbs and returns
the low one when the top three are zero, falling back to the accumulation when
they are not, swapped in by `@[csimp]`.

The limb read is half of it. The other half is that `beWord8At` takes its
in-bounds proof as an argument, so the eight reads are `ba[i]` and compile to
unchecked loads; `ba[i]!` would re-test `i < ba.size` and carry a panic branch
for every byte. The decoder has already checked `off + 32 ≤ ba.size` to decide
whether the word exists at all, so the proof is free — the last table row is
*not* a floor, since it is written with `ba[i]!` and the real reader is below
it. Together, on `decode bytes[]` 2000: 292 → 260 → 229 µs/op, 1.28×. The gain
tracks words read per element — `bytes32[]`, which reads one length word for a
whole array, holds at 170 either way.

What was available here is the work that never needed a bignum. The ABI writes
a word for every array length, dynamic offset, `bytes` length and `bool`, all
far below `2 ^ 64`, so `word32Small` copies the 24 leading zeros rather than
computing them (2.0× on `bytes[]`), and dynamic padding is copied rather than
pushed (`Chunks.emitZeros`, 1.16× on the unaligned row) — and, where the
payload is already word aligned, not written at all (`Builder.appendZeros`,
45 ns → 28 ns a value, the floor of writing the payload alone; 1.2× on
`bytes32[]`). After those, `bytes[]`
encodes at 0.44 ns/byte and decodes at 0.34 ns/byte — memcpy-bound, and what
is left above that floor is the word codec.

Full-width words used to pay the scratch buffer anyway: `putWord` allocated
a 32-byte `ByteArray` per word, filled it, and `emit` copied it again. The
`Chunks.word` leaf removes both — the limbs ride in the tree and
`Chunks.emitWord` pushes them straight into the pre-sized output. `encode
uint256[]` 1000: 144 → 86 µs/op, parity with go-ethereum. One sharp edge:
`Binary.pushBEChunk` takes its accumulator *borrowed*, so every call copies
the output built so far — `emitWord` unrolls it into straight-line `push`es
instead. When a linear loop measures quadratic, read the generated C: a
`lean_dec_ref` *after* an argument is passed means the callee borrows it.

The decode mirror: the generic walk costs ~eight allocations per element,
`decodeUintElems` reads a `uint256[]` word with a bounds check, a `UInt256`
and a cons, swapped in by `@[csimp]` at the `decodeBAVal` boundary (a
`mutual` block's bodies are compiled before any attribute placed after
them). `decode uint256[]` 2000: 173 → 66 µs/op, 1.3× ahead of go-ethereum.

## Measured negatives

Recorded so they are not retried. Each was implemented and benchmarked, not
reasoned about.

* **A direct chain of `ByteArray` appends for all-static types**, skipping the
  builder: ~6% faster on `(address, uint256)`, **10× slower** on `(bool × 8)`
  (176 ns → 1717 ns). `Builder.run` appends into an accumulator it uniquely
  owns; a chain of `++` does not keep that ownership, so the accumulator is
  copied instead of extended.
* **Writing a small word's leading zeros as a `zeros` run**, rather than the
  single `chunk` leaf `word32Small` builds: 1.53× on `bytes[]`, but 1.37×
  *slower* on `bool[]`, where the extra `append` node and second `emit` step
  cost more than the pushes they save.
* **`Builder.zeros 0 = empty`**, so the empty run is a nullary constructor
  rather than a `zeros` node, in place of `appendZeros` skipping the append:
  45 ns → 36 ns a value, against 28 ns for the skip. It drops the `zeros`
  leaf and the zero-length `copySlice` `emit` makes of it, but the `append`
  node, its `Builder` and the extra `emit` step stay — an operand has to
  exist to be appended. Half the win, and `toList_zeros` stops being `rfl`.
* **Chunking `allZerosBA`'s padding check** through `beWord8`: 25 ns → 15 ns
  per 28-byte check, 6% of the `decodeStrict` row it sits in — not worth the
  correctness argument.
* **Reading a word's limbs as a `UInt256`** — `(UInt256.ofBEByteArrayAt ba
  off).l3` — in place of four bare `UInt64` locals: no change at all on any
  row, twice measured. Assembling the structure costs about what the bignum
  accumulation cost, so the limb read only pays when nothing is allocated to
  hold the limbs. `Bench`'s `limbs (checked reads)` row is the shape that works
  — bare locals, no structure.
* **A `UInt64` length in place of the `Nat` one** — sound, the `2 ^ 64` cap being
  exactly `UInt64.size`. The twelve `Nat` ops an element in
  `decodeBytesPrefixBAVal` go 4.3 → 1.27 ns, 0.95 of it `len < 2 ^ 64` comparing
  against a *bignum* literal. That is 2.6% of a 117 ns element, under its row's
  own spread, bought with a `toNat` on every take/drop proof — the specification
  is `List`-indexed. And the word read spends 32 `lean_nat_add`s an element
  against these twelve: the arithmetic is in the indices, not the lengths.
* **`USize` indices and `ByteArray.uget`** for those reads — 1.48× on a limb read,
  and unreachable. Nothing takes a `Nat` offset to a `USize` one soundly:
  `USize.toNat_ofNat` gives `n % 2 ^ System.Platform.numBits`, `usize` truncates
  with no lemma back, and `a.size < USize.size` is unprovable. Core justifies
  `uget` in prose, as a runtime invariant; taking it costs an assumption in the
  public API.

* **`putUint` as a `word` leaf**, like `putWord`: `bytes[]` +5%, `bool[]`
  +37%. For a *small* word the chunk path was already cheap — one
  `copySlice` beats 32 per-byte pushes. The leaf only wins where it deletes
  the full-width word's alloc-and-fill; `putUint` keeps the chunk.
* **`UInt256.ofNat` anywhere near a hot path** — ~560 ns even for tiny `n`
  (the `BitVec.ofNat` route), against 4 ns for `⟨0, 0, 0, UInt64.ofNat n⟩`.
  The old warning here said "no `ofNat` round trip per word"; it still
  bites, now with a number.

Generating EVM bytecode rather than Lean remains the interesting direction.

## Writing a benchmark row

Lean floats closed subterms to cached top-level constants, so a row written as
`fun _ => f topLevelData` is evaluated once and then times a field read — an
early draft of the word-codec section reported 32000 `ByteArray.push`es in
"3 ns". `timed` hands every action its iteration index, and the index has to
reach the *work*, not just the returned sum. A row that closes over a function
parameter is already safe; one written against top-level definitions is not.
