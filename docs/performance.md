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

An ABI word is a `UInt256`, which wraps `BitVec 256` = `Fin (2 ^ 256)` =
`Nat` — above `2 ^ 63` a heap GMP bignum, so every `n >>> 64` on the way out
and every `acc <<< 64` on the way back in allocates. Per word:

| | full width | value < 2^63 |
|---|---|---|
| write 32 big-endian bytes | 523 ns | 93 ns |
| read 32 big-endian bytes | 854 ns | 22 ns |

The second column is the same codec on a value `Nat` keeps unboxed, so the gap
to it is the bignum and nothing else: **82% of a write and 97% of a read**.
Reading straight into four `UInt64` limbs is 16 ns, so a four-limb `UInt256`
would be worth ~5.6× and ~53× — but that is a `lean-binary` change, since it
moves the representation every proof in `Binary.UInt256` is stated over. There
is no four-limb *write* figure because with the bignum gone writing is 32
`ByteArray.push`es either way: 78 ns, against 5 ns to copy the same bytes.

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

Generating EVM bytecode rather than Lean remains the interesting direction.

## Writing a benchmark row

Lean floats closed subterms to cached top-level constants, so a row written as
`fun _ => f topLevelData` is evaluated once and then times a field read — an
early draft of the word-codec section reported 32000 `ByteArray.push`es in
"3 ns". `timed` hands every action its iteration index, and the index has to
reach the *work*, not just the returned sum. A row that closes over a function
parameter is already safe; one written against top-level definitions is not.
