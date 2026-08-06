# Performance

Every number here comes from `Bench`, on an Apple M-series machine:

```bash
lake build bench && ./.lake/build/bin/bench
```

**Compiled only.** The builder rests on the `@[extern]` `ByteArray.push` and
`ByteArray.emptyWithCapacity`, so an interpreted run (`lake env lean --run
Bench.lean`) inverts most of these rows.

Each codec exists twice: a `List UInt8` *specification* that the proofs are
stated over, and a `ByteArray` *runtime* form proved equal to it. Nothing
below is a second implementation to keep in step — `encode = (put t v).toList`
and `encodeByteArray = (put t v).run` are the same encoder materialised two
ways.

## The encoder: builder against specification

`Spec.encode` concatenates with `++` at every level, so a `d`-deep value has
its bytes re-copied `d` times. `Builder` makes concatenation an `O(1)`
constructor and `run` fills a pre-sized `ByteArray` in one pass.

| shape | `Spec.encode` + `toByteArray` | `Spec.encodeByteArray` | speedup |
|---|---|---|---|
| `bytes[]`, 500 × 256 B | 2429 µs | 406 µs | 6.0× |
| `bytes[]`, 2000 × 256 B | 9777 µs | 1562 µs | 6.3× |
| `uint256[]`, 1000 full-width words | 1001 µs | 572 µs | 1.8× |
| nested tuples, depth 50 | 1301 µs | 43 µs | 30× |
| nested tuples, depth 200 | 16945 µs | 184 µs | 92× |

The flat rows show the constant factor; the nested rows show the asymptotics —
quadratic against linear, so the gap widens with depth.

Both columns also depend on how fast one 32-byte word is produced, which is
`lean-binary`'s job: its `Binary.Fast` peels eight bytes at a time through a
`UInt64` instead of one at a time through bignum division, and registers the
result with `@[csimp]`, so this library needed no change to benefit. That is
worth 4.1× to the specification encoder and 5.0× to `Spec.encodeByteArray` on
the `uint256[]` row — and, because it sits below both, it is why the builder's
own advantage there is only 1.8×.

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

| shape | `encode` | compiled | `decodeStrict` | compiled |
|---|---|---|---|---|
| `(bool × 8)` | 378 ns | **168 ns** (2.25×) | 673 ns | **373 ns** (1.8×) |
| `bool[]`, 100 elements | 4792 ns | **2451 ns** (1.95×) | 8572 ns | **6148 ns** (1.4×) |
| `bytes[]`, 100 × 256 B | 16.2 µs | 13.7 µs (1.18×) | 13.1 µs | 10.9 µs (1.20×) |
| `(uint256, bool)[]`, 100 elements | 65.0 µs | 54.5 µs (1.19×) | 115.1 µs | 104.0 µs (1.11×) |
| `(address, uint256)` — one call's arguments | 652 ns | 594 ns (1.10×) | 1100 ns | 1041 ns (1.06×) |
| `uint256[]`, 100 full-width words | 53.3 µs | 50.5 µs (1.06×) | 98.1 µs | 96.9 µs (1.01×) |

The first two rows are what compilation is worth: cheap words, so the layout
*is* the work. The rest are dominated by the word codec below, so there is
little left for the compiler to remove.

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
| write 32 big-endian bytes | 85 ns | 83 ns |
| read 32 big-endian bytes | 803 ns | 22 ns |
| read into limbs, `ba[i]!` | 16 ns | 16 ns |

The write columns have converged, and what is left of them is not arithmetic:
writing is 32 `ByteArray.push`es either way, against 5 ns to copy the same
bytes. Reading is the row still to close — `Binary.decodeBEBytesFrom`
accumulates into a `Nat`, so a full-width read is 50× a limb read, and even a
small one is 6 ns above it.

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
pushed (`Chunks.emitZeros`, 1.16× on the unaligned row). After both, `bytes[]`
encodes at 0.44 ns/byte and decodes at 0.34 ns/byte — memcpy-bound, and what
is left above that floor is the word codec.

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
* **Chunking `allZerosBA`'s padding check** through `beWord8`: 25 ns → 15 ns
  per 28-byte check, 6% of the `decodeStrict` row it sits in — not worth the
  correctness argument.
* **Reading a word's limbs as a `UInt256`** — `(UInt256.ofBEByteArrayAt ba
  off).l3` — in place of four bare `UInt64` locals: no change at all on any
  row, twice measured. Assembling the structure costs about what the bignum
  accumulation cost, so the limb read only pays when nothing is allocated to
  hold the limbs. `Bench`'s `limbs (ceiling)` row is the shape that works.

Generating EVM bytecode rather than Lean remains the interesting direction.

## Writing a benchmark row

Lean floats closed subterms to cached top-level constants, so a row written as
`fun _ => f topLevelData` is evaluated once and then times a field read — an
early draft of the word-codec section reported 32000 `ByteArray.push`es in
"3 ns". `timed` hands every action its iteration index, and the index has to
reach the *work*, not just the returned sum. A row that closes over a function
parameter is already safe; one written against top-level definitions is not.
