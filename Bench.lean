import EvmAbi
import EvmAbi.Codec.Strict
import EvmAbi.Packed

/-!
# Bench

Engineering-level benchmarks for the `EvmAbi` codec, compiled to native
code via a `lean_exe` target (`lake build bench`).  The executable runs
encode / decode / decodeStrict / packed workloads and micro-benchmarks
of the hot primitives, reporting per-operation cost and throughput.

Run: `lake build bench && .lake/build/bin/bench [workload-filter]`

The workloads are chosen to separate the layers:

* `words/<n>`       — array of `uint256`: pure 32-byte-word head walking.
* `bytes/<k>`       — a single large dynamic `bytes` payload.
* `barr/<n>`        — array of dynamic `bytes` (offset words + tails).
* `nested/<o>/<i>`  — array of arrays of `bytes`: nested dynamic layout.
* `mixed`           — hand-written heterogeneous tuple.
* `string/<k>`      — `string` payload (UTF-8 encode/decode).
* `fixed/<n>`       — fixed array of `uint256`.
* packed workloads  — `abi.encodePacked` / `decodePacked`.

Scaling a workload by 4× should cost ~4× (linear decoder/encoder); if
the ratio is superlinear the walk is touching the buffer repeatedly.
-/

namespace Bench

open EvmAbi
open Ty
open Builder
open Binary

/-! ## iteration and timing helpers -/

/-- Tail-recursive counting loop: `f` is applied `n` times and its
results accumulate into `acc`.  Compiles to a loop; no allocation per
iteration, so micro-benchmarks measure the payload, not the harness. -/
def loop (n : Nat) (acc : Nat) (f : Nat → Nat → Nat) : Nat :=
  match n with
  | 0 => acc
  | k + 1 => loop k (f k acc) f

/-- Time `fold iters` and report.  `payloadBytes` is the size of one
operation's data (used for the MB/s column).

The fold is evaluated inside an `IO.Ref.modify` so the compiled code
cannot hoist the (pure) work out of the timing window: the Lean C
backend freely reorders pure subterms, and two adjacent clock reads
measured before the work would otherwise report pure jitter.
-/
def timed (name : String) (payloadBytes : Nat) (fold : Nat → Nat) : IO Unit := do
  let ref ← IO.mkRef 0
  let t0 ← IO.monoNanosNow
  ref.modify (fun _ => fold 10)
  let t1 ← IO.monoNanosNow
  let per := (t1 - t0) / 10
  let iters := max 1 (min 5000 ((200 * 1000000) / max 1 per))
  let s0 ← IO.monoNanosNow
  ref.modify (fun _ => fold iters)
  let s1 ← IO.monoNanosNow
  let acc ← ref.get
  let ns := s1 - s0
  let perOpNs := ns / iters
  let mbps := (payloadBytes.toFloat * iters.toFloat * 1000.0) / ns.toFloat
  IO.println
    (name ++ " | " ++ toString payloadBytes ++ " B/op | " ++ toString iters ++ " iters | "
      ++ toString (ns / 1000000) ++ " ms | " ++ toString (perOpNs / 1000) ++ " µs/op | "
      ++ Float.toString mbps ++ " MB/s | sum " ++ toString acc)
  (← IO.getStdout).flush

/-! ## value generators -/

/-- A fixed `uint256` value used everywhere a plain word is needed. -/
def w42 : (Ty.uint 256).Val := ⟨42, by decide⟩

/-- `(T[])`-shaped value with `n` elements produced by `mk`. -/
def arrayOf (t : Ty) (mk : Nat → t.Val) (n : Nat) (hn : n < 2 ^ 256) : (Ty.array t).Val :=
  ⟨(List.range n).map mk, by rw [List.length_map, List.length_range]; exact hn⟩

/-- `(T[n])`-shaped value with `n` elements produced by `mk`. -/
def fixedArrayOf (t : Ty) (mk : Nat → t.Val) (n : Nat) : (Ty.fixedArray t n).Val :=
  ⟨(List.range n).map mk, by rw [List.length_map, List.length_range]⟩

/-- A `bytes` element whose size cycles 1..64, so dynamic tails vary. -/
def bytesElemCyclic : Nat → Ty.bytes.Val := fun i =>
  have hmod : i % 64 < 64 := Nat.mod_lt i (by decide : 0 < 64)
  have hk1 : i % 64 + 1 ≤ 64 := by omega
  ⟨List.replicate (i % 64 + 1) 3, by
    rw [List.length_replicate]
    exact Nat.lt_of_le_of_lt hk1 (by decide : 64 < 2 ^ 256)⟩

/-- A fixed-size `bytes` element (all `k` bytes are `3`). -/
def bytesElem (k : Nat) (hk : k < 2 ^ 256) : Ty.bytes.Val :=
  ⟨List.replicate k 3, by rw [List.length_replicate]; exact hk⟩

/-- Array of dynamic `bytes` with varying element sizes. -/
def bytesArrayVal (n : Nat) (hn : n < 2 ^ 256) : (Ty.array Ty.bytes).Val :=
  arrayOf Ty.bytes bytesElemCyclic n hn

/-- Array of `uint256` words. -/
def wordsArrayVal (n : Nat) (hn : n < 2 ^ 256) : (Ty.array (Ty.uint 256)).Val :=
  arrayOf (Ty.uint 256) (fun _ => w42) n hn

/-- Array of arrays of `bytes`: inner arrays have `i` fixed-size
elements, the outer array has `o` of them. -/
def nestedVal (o i : Nat) (ho : o < 2 ^ 256) (hi : i < 2 ^ 256) :
    (Ty.array (Ty.array Ty.bytes)).Val :=
  let inner (k : Nat) (hk : k < 2 ^ 256) : (Ty.array Ty.bytes).Val :=
    ⟨List.replicate k (bytesElem 32 (by decide)), by rw [List.length_replicate]; exact hk⟩
  ⟨List.replicate o (inner i hi), by rw [List.length_replicate]; exact ho⟩

/-- A heterogeneous static+dynamic tuple. -/
def mixedTupleVal : (Ty.tuple [Ty.uint 256, Ty.bytes, Ty.address, Ty.bool, Ty.bytes]).Val :=
  (w42,
   bytesElem 64 (by decide),
   ⟨7, by decide⟩,
   true,
   bytesElem 128 (by decide),
   ())

/-- A `string` value, constructed with a runtime length check. -/
def mkStringVal (s : String) : Option Ty.string.Val :=
  if h : s.toUTF8.size < 2 ^ 256 then some ⟨s, h⟩ else none

/-- Fixed array of `uint256` words. -/
def fixedWordsVal (n : Nat) : (Ty.fixedArray (Ty.uint 256) n).Val :=
  fixedArrayOf (Ty.uint 256) (fun _ => w42) n

/-- Fixed array of `uint8` for the packed workloads. -/
def fixedBytes8Val (n : Nat) : (Ty.fixedArray (Ty.uint 8) n).Val :=
  fixedArrayOf (Ty.uint 8) (fun _ => ⟨7, by decide⟩) n

/-- A heterogeneous packed tuple of scalars. -/
def packedTupleVal : (Ty.tuple [Ty.uint 8, Ty.uint 16, Ty.bool, Ty.address, Ty.bytesN 20]).Val :=
  (⟨7, by decide⟩,
   ⟨1000, by decide⟩,
   true,
   ⟨12345, by decide⟩,
   ⟨List.replicate 20 9, by rw [List.length_replicate]⟩,
   ())

/-! ## workload drivers -/

/-- Opaque wrappers so the compiled code cannot common-subexpression-
eliminate the measured call with the precomputed buffer: the C backend
freely shares identical pure subterms, which would move the encode out
of the timing window and leave only a `List.length` walk behind. -/
@[noinline] def encodeLength (t : Ty) (v : t.Val) : Nat := (encode t v).length

@[noinline] def decodeOK (t : Ty) (buf : List UInt8) : Nat :=
  if (decode t buf).isSome then 1 else 0

@[noinline] def strictOK (t : Ty) (buf : List UInt8) : Nat :=
  if (decodeStrict t buf).isSome then 1 else 0

@[noinline] def encodePackedLength (t : Ty) (v : t.Val) : Nat := (encodePacked t v).length

@[noinline] def decodePackedOK (t : Ty) (buf : List UInt8) : Nat :=
  if (decodePacked t buf).isSome then 1 else 0

/-- Benchmark `encode`, `decode` and `decodeStrict` of one value. -/
def benchCodec (name : String) (t : Ty) (v : t.Val) : IO Unit := do
  let buf := encode t v
  let n := buf.length
  timed (name ++ "/encode") n (fun iters =>
    loop iters 0 (fun _ acc => acc + encodeLength t v))
  timed (name ++ "/decode") n (fun iters =>
    loop iters 0 (fun _ acc => acc + decodeOK t buf))
  timed (name ++ "/strict") n (fun iters =>
    loop iters 0 (fun _ acc => acc + strictOK t buf))

/-- Benchmark `encodePacked` / `decodePacked` of one value. -/
def benchPacked (name : String) (t : Ty) (v : t.Val) : IO Unit := do
  let buf := encodePacked t v
  let n := buf.length
  timed (name ++ "/encode") n (fun iters =>
    loop iters 0 (fun _ acc => acc + encodePackedLength t v))
  timed (name ++ "/decode") n (fun iters =>
    loop iters 0 (fun _ acc => acc + decodePackedOK t buf))

/-! ## micro-benchmarks -/

/-- `UInt256.toBEBytes`: the per-word byte-list encoder. -/
def benchWordEncode : IO Unit := do
  let t ← IO.monoNanosNow
  let w := UInt256.ofNat (t % 1000)
  timed "micro/toBEBytes" 32 (fun iters =>
    loop iters 0 (fun _ acc => acc + (UInt256.toBEBytes w).length))

/-- `UInt256.ofBEBytes`: the per-word byte-list decoder. -/
def benchWordDecode : IO Unit := do
  let t ← IO.monoNanosNow
  let wb := UInt256.toBEBytes (UInt256.ofNat (t % 1000))
  timed "micro/ofBEBytes" 32 (fun iters =>
    loop iters 0 (fun _ acc => acc + (UInt256.ofBEBytes wb).toNat))

/-- `decodeUint` on a word buffer: the per-word front read. -/
def benchDecodeUint : IO Unit := do
  let buf := encodeUint 42
  timed "micro/decodeUint" 32 (fun iters =>
    loop iters 0 (fun _ acc => acc + if (decodeUint buf).isSome then 1 else 0))

/-- `pad32` on a 64 KiB payload: the dynamic-bytes padding path. -/
def benchPad32 : IO Unit := do
  let bs := List.replicate 65536 1
  timed "micro/pad32/64k" 65536 (fun iters =>
    loop iters 0 (fun _ acc => acc + (pad32 bs).length))

/-- `decodeBytesPrefix` on a 64 KiB payload. -/
def benchBytesPrefix : IO Unit := do
  let buf := encodeBytes (List.replicate 65536 1)
  timed "micro/bytesPrefix/64k" 65536 (fun iters =>
    loop iters 0 (fun _ acc => acc + if (decodeBytesPrefix buf).isSome then 1 else 0))

/-- Materializing a 32 KiB builder chain: the pure `Builder.toList` cost. -/
def benchBuilder : IO Unit := do
  let b : Builder := List.foldl (fun acc _ => acc ++ putUint 42) ∅ (List.range 1024)
  timed "micro/builder/32k" 32768 (fun iters =>
    loop iters 0 (fun _ acc => acc + b.toList.length))

/-- Direct reference walk: decode `n` consecutive words with no `Get2`
monad, no subtype reconstruction — the floor the decoder walkers are
compared against. -/
def directWords (n : Nat) (buf : List UInt8) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => match decodeUint buf with
      | some _ => 1 + directWords k (buf.drop 32)
      | none => 0

/-- The `Get2` walker overhead measured against `directWords`. -/
def benchDirectWords : IO Unit := do
  let v := wordsArrayVal 2048 (by decide)
  let buf := encode (Ty.array (Ty.uint 256)) v
  timed "micro/directWords/2048" 65568 (fun iters =>
    loop iters 0 (fun _ acc => acc + directWords 2048 buf))

/-! ## main -/

def mainImpl : IO Unit := do
  IO.println "== EvmAbi benchmarks (native) =="

  -- scaling series: words 2048/8192/32768 (64 KiB / 256 KiB / 1 MiB)
  benchCodec "words/2048" (Ty.array (Ty.uint 256)) (wordsArrayVal 2048 (by decide))
  benchCodec "words/8192" (Ty.array (Ty.uint 256)) (wordsArrayVal 8192 (by decide))
  benchCodec "words/32768" (Ty.array (Ty.uint 256)) (wordsArrayVal 32768 (by decide))

  -- fixed array of words
  benchCodec "fixed/4096" (Ty.fixedArray (Ty.uint 256) 4096) (fixedWordsVal 4096)

  -- dynamic payloads
  benchCodec "bytes/1m" Ty.bytes (bytesElem 1048576 (by decide))
  benchCodec "barr/256" (Ty.array Ty.bytes) (bytesArrayVal 256 (by decide))
  benchCodec "barr/1024" (Ty.array Ty.bytes) (bytesArrayVal 1024 (by decide))
  benchCodec "barr/4096" (Ty.array Ty.bytes) (bytesArrayVal 4096 (by decide))
  benchCodec "nested/32/32" (Ty.array (Ty.array Ty.bytes)) (nestedVal 32 32 (by decide) (by decide))

  -- mixed tuple and string
  benchCodec "mixed" (Ty.tuple [Ty.uint 256, Ty.bytes, Ty.address, Ty.bool, Ty.bytes]) mixedTupleVal
  match mkStringVal (String.join (List.replicate 4096 "ab")) with
  | some sv => benchCodec "string/8k" Ty.string sv
  | none => IO.println "string workload: skipped (bound check failed)"

  -- packed
  benchPacked "packed/fixed8/4096" (Ty.fixedArray (Ty.uint 8) 4096) (fixedBytes8Val 4096)
  benchPacked "packed/tuple" (Ty.tuple [Ty.uint 8, Ty.uint 16, Ty.bool, Ty.address, Ty.bytesN 20])
    packedTupleVal

  -- micro-benchmarks
  benchWordEncode
  benchWordDecode
  benchDecodeUint
  benchPad32
  benchBytesPrefix
  benchBuilder
  benchDirectWords

end Bench

def main : IO Unit := Bench.mainImpl
