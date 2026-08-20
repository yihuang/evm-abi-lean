import Binary.ByteArray
import EvmAbi.Word

/-!
# EvmAbi.Builder

The write and read layer.  `Builder` bridges the `List UInt8` the proofs
are stated over and the contiguous `ByteArray` execution wants; `Get2` is
its dual on the reading side, a prefix reader over two cursors.

`List UInt8` is the right *specification* type — `++` is associative on the
nose, `take`/`drop` have a rich algebra — and the wrong *runtime* type: a cons
cell and a boxed byte per byte, and a nest of `++`s that re-copies a value's
bytes once per level of nesting.

The classic fix (Haskell's `Data.Binary.Builder`) is to make concatenation
free by *not* concatenating.  `Chunks` is a tree whose `append` is a
constructor, with leaves for a literal byte list, a `ByteArray` kept as-is (so
`String.toUTF8` payloads are never unpacked), and a run of zero bytes (so
padding is never materialised); `Builder.run` fills a pre-sized `ByteArray`
from it in one pass.

`Builder` pairs that tree with its **cached** byte count.  The cache is not a
detail: the ABI head/tail layout asks for the size of every tail while writing
the offset words, so a `size` that walked the tree would put the `O(n · depth)`
cost straight back.  `size_eq` keeps the cache honest by construction and,
being a `Prop`, is erased at run time.

`Builder.toList` is the **denotation** — the only thing the proofs see, never
called at run time — and

```
data_toList_run : b.run.data.toList = b.toList
```

is what makes the layer useful: any `List UInt8` statement transports to the
`ByteArray` that `run` produces without reproving anything.  `EvmAbi.Spec`
writes its `put` against this one builder, so `encode = (put t v).toList` and
`encodeByteArray = (put t v).run` are the same encoder materialized two ways
— there is no second encoder to keep in step.

One caveat for proofs: `append` is a *constructor*, so it is associative and
`empty`-neutral only up to `toList`.  Never state a `Builder`-valued equation
that needs those laws; state it of the denotation.

ABI-agnostic apart from the two word primitives (`putWord`, `word32Small`):
otherwise just the Lean 4 core library and `Binary.ByteArray`.
-/
namespace EvmAbi

open Binary

/-- The shape of a builder: a tree whose leaves are byte runs and whose
`append` nodes cost `O(1)`.  Wrapped by `Builder`, which adds the cached
byte count. -/
inductive Chunks where
  /-- The empty byte string. -/
  | empty : Chunks
  /-- A literal byte list. -/
  | bytes (bs : List UInt8) : Chunks
  /-- A contiguous chunk, kept as-is (used for `String.toUTF8` payloads). -/
  | chunk (ba : ByteArray) : Chunks
  /-- A run of `n` zero bytes (used for padding; never materialised). -/
  | zeros (n : Nat) : Chunks
  /-- One 32-byte EVM word, kept as limbs (used by `putWord`; never
  materialised — `emit` writes it straight into the output buffer). -/
  | word (w : UInt256) : Chunks
  /-- Concatenation — a constructor, so it costs `O(1)`. -/
  | append (a b : Chunks) : Chunks

namespace Chunks

/-! ## denotation

`toList` is the specification: it says which byte string a tree stands for.
Every theorem below is stated through it, and nothing at runtime ever calls
it. -/

/-- The byte string a chunk tree denotes. -/
def toList : Chunks → List UInt8
  | .empty => []
  | .bytes bs => bs
  | .chunk ba => ba.data.toList
  | .zeros n => List.replicate n 0
  | .word w => bytesOfWord w
  | .append a b => a.toList ++ b.toList

/-! ## execution

`emit` appends a tree onto an accumulator with `ByteArray.push`; `Builder.run`
pre-sizes the accumulator from the cached size, so the whole traversal is one
linear pass with no reallocation.

`acc ++ ba` per `.chunk` leaf looks quadratic but is not.  Compiled,
`ByteArray.append` is `fastAppend`, `b.copySlice 0 a a.size b.size false`,
which copies `b` *into* `a`, in place while `a` is uniquely referenced; `emit`
threads `acc` linearly, so it is.  Measured on `uint256[]`, encoding is
linear in the element count over a 16× range.  (Words themselves no longer
go through `.chunk` at all — `putWord` stores a `.word` leaf and `emitWord`
pushes the limbs directly.)

**Invariant**: nothing may hold a second reference to `acc` across an `emit`
call.  Reading `acc.size` back for a check would silently make every chunk
append a full copy again. -/

/-- Push a literal byte list onto the accumulator. -/
def emitBytes (acc : ByteArray) : List UInt8 → ByteArray
  | [] => acc
  | b :: bs => emitBytes (acc.push b) bs

theorem data_toList_emitBytes (acc : ByteArray) (bs : List UInt8) :
    (emitBytes acc bs).data.toList = acc.data.toList ++ bs := by
  induction bs generalizing acc with
  | nil => simp [emitBytes]
  | cons b bs ih => simp [emitBytes, ih, ByteArray.data_push]

/-- Push `n` zero bytes onto the accumulator. -/
def emitZeros (acc : ByteArray) : Nat → ByteArray
  | 0 => acc
  | n + 1 => emitZeros (acc.push 0) n

theorem data_toList_emitZeros (acc : ByteArray) (n : Nat) :
    (emitZeros acc n).data.toList = acc.data.toList ++ List.replicate n 0 := by
  induction n generalizing acc with
  | zero => simp [emitZeros]
  | succ n ih => simp [emitZeros, ih, ByteArray.data_push, List.replicate_succ]

/-- `pushBEChunk 8` unrolled into straight-line pushes.  Not cosmetic:
`pushBEChunk` takes its accumulator *borrowed*, so every call pushes onto a
shared `ByteArray` and copies the whole output built so far — harmless on a
32-byte scratch, quadratic here.  Straight-line `push`es keep it uniquely
referenced, so every push is in place. -/
def emitLimb (acc : ByteArray) (x : UInt64) : ByteArray :=
  let x1 := x >>> 8
  let x2 := x1 >>> 8
  let x3 := x2 >>> 8
  let x4 := x3 >>> 8
  let x5 := x4 >>> 8
  let x6 := x5 >>> 8
  let x7 := x6 >>> 8
  ((((((((acc.push x7.toUInt8).push x6.toUInt8).push x5.toUInt8).push
    x4.toUInt8).push x3.toUInt8).push x2.toUInt8).push x1.toUInt8).push x.toUInt8)

theorem emitLimb_eq_pushBEChunk (acc : ByteArray) (x : UInt64) :
    emitLimb acc x = pushBEChunk 8 x acc := rfl

/-- Push one 32-byte word onto the accumulator, most significant limb
first — no per-word scratch buffer, no `copySlice`. -/
def emitWord (acc : ByteArray) (w : UInt256) : ByteArray :=
  emitLimb (emitLimb (emitLimb (emitLimb acc w.l0) w.l1) w.l2) w.l3

theorem data_toList_emitWord (acc : ByteArray) (w : UInt256) :
    (emitWord acc w).data.toList = acc.data.toList ++ bytesOfWord w := by
  -- `toBEByteArrayFast` is the same limb chain seeded empty; expand both
  -- chains with `pushBEChunk_eq` and rewrite across.
  have h : (UInt256.toBEByteArrayFast w).data.toList = bytesOfWord w := by
    rw [← congrFun UInt256.toBEByteArray_eq_fast w]
    exact UInt256.toList_toBEByteArray w
  simp only [emitWord, emitLimb_eq_pushBEChunk, UInt256.toBEByteArrayFast, pushBEChunk_eq,
    toList_emptyWithCapacity, List.nil_append, List.append_assoc] at h ⊢
  rw [h]

/-! ### zero runs, copied rather than pushed

`emitZeros` is the specification, and `data_toList_emitZeros` above is what
every proof uses.  It is also the wrong thing to *run*: a dynamic ABI payload
is padded up to a word, so the encoder asks for a run of up to 31 zero bytes
per `bytes`/`string` value, and pushing them one at a time costs ~40 ns where
copying them out of a static buffer costs ~5 ns (`Bench`'s word-codec
section).

`emitZerosFast` copies, and `@[csimp]` swaps it in at code generation, so the
definition above and every theorem stated of it are untouched.  It has to
appear before `emit`, which is the caller the swap has to reach. -/

/-- A static run of 32 zero bytes to copy padding out of.  A closed term, so
it is allocated once. -/
def zeroBuf : ByteArray := (List.replicate 32 (0 : UInt8)).toByteArray

theorem data_toList_zeroBuf : zeroBuf.data.toList = List.replicate 32 0 :=
  List.toList_data_toByteArray

theorem size_data_zeroBuf : zeroBuf.data.size = 32 := by
  rw [← Array.length_toList, data_toList_zeroBuf, List.length_replicate]

/-- Append at most 32 zero bytes with a single `copySlice`.

`acc` is passed as `copySlice`'s `dest`, which is an owned argument, so it is
extended in place while uniquely referenced; `acc.size` is read from a borrow
and does not disturb that. -/
def pushZeros32 (acc : ByteArray) (n : Nat) : ByteArray :=
  zeroBuf.copySlice 0 acc acc.size n false

theorem data_toList_pushZeros32 (acc : ByteArray) {n : Nat} (h : n ≤ 32) :
    (pushZeros32 acc n).data.toList = acc.data.toList ++ List.replicate n 0 := by
  have hsz : acc.size = acc.data.size := rfl
  have hsplit : List.replicate n (0 : UInt8) ++ List.replicate (32 - n) 0 = List.replicate 32 0 := by
    rw [List.replicate_append_replicate]
    congr 1
    omega
  have htake : List.take n zeroBuf.data.toList = List.replicate n 0 := by
    rw [data_toList_zeroBuf, ← hsplit]
    exact take_append_of_length List.length_replicate
  simp only [pushZeros32, ByteArray.copySlice, hsz, Nat.zero_add, Nat.sub_zero,
    size_data_zeroBuf, Nat.min_eq_left h, Array.toList_append, Array.toList_extract,
    List.extract_eq_take_drop, List.drop_zero, htake]
  -- the head slice is all of `acc`, and the tail slice starts past its end
  rw [List.take_of_length_le (Nat.le_of_eq Array.length_toList),
    show acc.data.size - (acc.data.size + n) = 0 from by omega, List.take_zero,
    List.append_nil]

/-- Zero runs by copy: a full buffer at a time, then the remainder. -/
def emitZerosFast (acc : ByteArray) (n : Nat) : ByteArray :=
  if n ≤ 32 then pushZeros32 acc n
  else emitZerosFast (pushZeros32 acc 32) (n - 32)
termination_by n

theorem data_toList_emitZerosFast (acc : ByteArray) (n : Nat) :
    (emitZerosFast acc n).data.toList = acc.data.toList ++ List.replicate n 0 := by
  induction acc, n using emitZerosFast.induct with
  | case1 acc n h => rw [emitZerosFast, if_pos h, data_toList_pushZeros32 acc h]
  | case2 acc n h ih =>
      rw [emitZerosFast, if_neg h, ih, data_toList_pushZeros32 acc (Nat.le_refl 32),
        List.append_assoc, List.replicate_append_replicate,
        show 32 + (n - 32) = n from by omega]

/-- The swap.  A `Prop`-level equation between the two implementations, so
the compiled encoder copies its padding while the proofs keep pushing it. -/
@[csimp] theorem emitZeros_eq_fast : @emitZeros = @emitZerosFast := by
  funext acc n
  apply ByteArray.data_inj
  rw [← Array.toList_inj, data_toList_emitZeros, data_toList_emitZerosFast]

/-- Append a chunk tree onto an accumulator. -/
def emit (acc : ByteArray) : Chunks → ByteArray
  | .empty => acc
  | .bytes bs => emitBytes acc bs
  | .chunk ba => acc ++ ba
  | .zeros n => emitZeros acc n
  | .word w => emitWord acc w
  | .append a b => emit (emit acc a) b

theorem data_toList_emit (acc : ByteArray) (c : Chunks) :
    (emit acc c).data.toList = acc.data.toList ++ c.toList := by
  induction c generalizing acc with
  | empty => simp [emit, toList]
  | bytes bs => simp [emit, toList, data_toList_emitBytes]
  | chunk ba => simp [emit, toList]
  | zeros n => simp [emit, toList, data_toList_emitZeros]
  | word w => simp [emit, toList, data_toList_emitWord]
  | append a b iha ihb => simp [emit, toList, iha, ihb, List.append_assoc]

end Chunks

/-! ## a word written by copy

`pushZeros32` is what makes `word32Small` cheap: a word whose value fits in
eight bytes has 24 leading zero bytes, and copying them out of `zeroBuf`
beats computing them.  The two `encodeBEU` facts below are what make it
sound; they are really `Binary` lemmas, and live here because this is their
only use. -/

/-- Zero encodes as zeros, at any width. -/
theorem encodeBEU_zero (m : Nat) : encodeBEU m 0 = List.replicate m 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Nat.add_comm, encodeBEU_add 1 m 0, Nat.zero_div, ih,
        show encodeBEU 1 0 = List.replicate 1 0 from rfl,
        List.replicate_append_replicate, Nat.add_comm]

/-- **The leading zeros are free**: a value that fits in `k` bytes has the
other `m` bytes of its `k + m`-wide encoding zero, so they need not be
computed — only copied. -/
theorem encodeBEU_pad {k n : Nat} (h : n < 256 ^ k) (m : Nat) :
    encodeBEU (k + m) n = List.replicate m 0 ++ encodeBEU k n := by
  rw [encodeBEU_add k m n, Nat.div_eq_of_lt h, encodeBEU_zero]

/-- A 32-byte big-endian word whose value fits in eight bytes: the 24 leading
zeros copied in one `copySlice`, then the single `UInt64` chunk that can be
non-zero.  `encodeBEBytes 32` instead pushes all 32 bytes one at a time,
three quarters of them known to be zero. -/
def word32Small (n : Nat) : ByteArray :=
  pushBEChunk 8 (UInt64.ofNat n) (Chunks.pushZeros32 (ByteArray.emptyWithCapacity 32) 24)

theorem data_toList_word32Small {n : Nat} (h : n < 2 ^ 64) :
    (word32Small n).data.toList = encodeBEU 32 n := by
  have h8 : n < 256 ^ 8 := by omega
  rw [word32Small, pushBEChunk_eq, Chunks.data_toList_pushZeros32 _ (by omega),
    encodeBEU_window (by omega), show (ByteArray.emptyWithCapacity 32).data.toList = [] from rfl,
    List.nil_append, show (32 : Nat) = 8 + 24 from rfl, encodeBEU_pad h8 24]

/-- A byte-string builder: a chunk tree together with its byte count.

The count is cached rather than computed because the ABI head/tail layout
asks for the size of every tail while writing the offset words; recomputing
it by walking the tree would reintroduce the very `O(n · depth)` cost the
builder exists to remove.  `size_eq` is a `Prop`, so it is erased at
runtime — a `Builder` is a chunk tree and a `Nat`. -/
structure Builder where
  /-- The chunk tree. -/
  chunks : Chunks
  /-- Cached byte count. -/
  size : Nat
  /-- The cache is honest — maintained by every constructor below. -/
  size_eq : size = chunks.toList.length

namespace Builder

/-! ## constructors

Each is `O(1)` except `bytes`, which measures the list it is handed once. -/

/-- The empty builder. -/
def empty : Builder := ⟨.empty, 0, rfl⟩

/-- A literal byte list. -/
def ofList (bs : List UInt8) : Builder := ⟨.bytes bs, bs.length, rfl⟩

/-- A literal byte list whose length is already known.  `ofList` measures
the list; this variant takes the measurement, so a caller that needs the
length anyway — a `bytes` value's length word, say — walks the list once
instead of twice.  The size cache is only honest because `h` is there. -/
def ofListLen (bs : List UInt8) (len : Nat) (h : len = bs.length) : Builder :=
  ⟨.bytes bs, len, h⟩

/-- A contiguous chunk, kept as-is. -/
def chunk (ba : ByteArray) : Builder := ⟨.chunk ba, ba.size, ByteArray.size_eq_toList_length ba⟩

/-- A run of `n` zero bytes; nothing is materialised. -/
def zeros (n : Nat) : Builder := ⟨.zeros n, n, by simp [Chunks.toList]⟩

/-- Concatenation: `O(1)`, and the size cache adds up. -/
def append (a b : Builder) : Builder :=
  ⟨.append a.chunks b.chunks, a.size + b.size, by
    simp [Chunks.toList, a.size_eq, b.size_eq]⟩

instance : Append Builder := ⟨Builder.append⟩
instance : EmptyCollection Builder := ⟨Builder.empty⟩

/-- Append a run of `n` zero bytes, adding nothing when `n = 0`.  The empty
run is not a corner case — a `bytesN 32`, and any `bytes` or `string` already
a multiple of 32 long, pads by nothing — and `b ++ zeros 0` still allocates
two nodes for `emit` to walk and write nothing: 46 ns per value against 29
skipped.  Every padding run in the encoders goes through this. -/
def appendZeros (b : Builder) (n : Nat) : Builder :=
  if n = 0 then b else b ++ zeros n

/-! ## denotation -/

/-- The byte string a builder denotes. -/
def toList (b : Builder) : List UInt8 := b.chunks.toList

@[simp] theorem toList_empty : (∅ : Builder).toList = [] := rfl
@[simp] theorem toList_ofList (bs : List UInt8) : (Builder.ofList bs).toList = bs := rfl
@[simp] theorem toList_ofListLen (bs : List UInt8) (len : Nat) (h : len = bs.length) :
    (Builder.ofListLen bs len h).toList = bs := rfl
@[simp] theorem toList_chunk (ba : ByteArray) : (Builder.chunk ba).toList = ba.data.toList := rfl
@[simp] theorem toList_zeros (n : Nat) : (Builder.zeros n).toList = List.replicate n 0 := rfl
@[simp] theorem toList_append (a b : Builder) : (a ++ b).toList = a.toList ++ b.toList := rfl

@[simp] theorem toList_appendZeros (b : Builder) (n : Nat) :
    (appendZeros b n).toList = b.toList ++ List.replicate n 0 := by
  by_cases h : n = 0 <;> simp [appendZeros, h]

/-- The cached size agrees with the denotation — this is why `run` can size
its buffer in advance, and why the offset words the ABI layout computes from
`size` are the offsets the specification demands. -/
@[simp] theorem size_eq_length_toList (b : Builder) : b.size = b.toList.length := b.size_eq

/-! ## word primitive -/

/-- Write one 32-byte EVM word, big-endian.  A `word` leaf, not a `chunk`:
the value rides in the tree as its four limbs, and `Chunks.emitWord` pushes
them straight into the output buffer — so no per-word 32-byte `ByteArray` is
allocated and then re-copied, and ABI encodings are mostly words. -/
def putWord (w : UInt256) : Builder := ⟨.word w, 32, (length_bytesOfWord w).symm⟩

@[simp] theorem toList_putWord (w : UInt256) : (putWord w).toList = bytesOfWord w := rfl

/-! ## execution -/

/-- Run a builder into a contiguous `ByteArray`, sized exactly in advance. -/
def run (b : Builder) : ByteArray := Chunks.emit (ByteArray.emptyWithCapacity b.size) b.chunks

/-- **The bridge**: running a builder produces exactly the bytes it denotes.
Every `List UInt8` statement about `b.toList` transports to `b.run`. -/
@[simp] theorem data_toList_run (b : Builder) : b.run.data.toList = b.toList := by
  have h : (ByteArray.emptyWithCapacity b.size).data.toList = [] := rfl
  rw [run, Chunks.data_toList_emit, h, List.nil_append, toList]

@[simp] theorem size_run (b : Builder) : b.run.size = b.size := by
  rw [ByteArray.size_eq_toList_length, data_toList_run, size_eq_length_toList]

/-- The other direction: `run` is `List.toByteArray` of the denotation, so a
builder and the list it denotes are interchangeable at the I/O boundary. -/
theorem run_eq_toByteArray (b : Builder) : b.run = b.toList.toByteArray := by
  apply ByteArray.data_inj
  rw [← Array.toList_inj, data_toList_run, List.toList_data_toByteArray]

end Builder

/-! ## Get2: the dual-cursor reader -/

namespace Get2

/-- The result of a `Get2` run: the decoded value together with the
advanced head and tail cursors and the new expected tail frontier. -/
@[ext]
structure Result (α : Type) where
  /-- The decoded value. -/
  val : α
  /-- Remaining head cursor. -/
  head : List UInt8
  /-- Remaining tail cursor. -/
  tails : List UInt8
  /-- New expected tail frontier. -/
  frontier : Nat

end Get2

/-- A dual-cursor prefix reader: consumes from a *head cursor* (the head
section of a canonical layout) and a *tail cursor* (the tails), threading
the expected tail frontier `E`.  Each component step advances one or both
cursors monotonically — no re-dropping from the front of the buffer — so
canonical layouts decode in a single pass.  The frontier is the absolute
position the next dynamic tail must occupy; a dynamic component's offset
word must equal it exactly. -/
structure Get2 (α : Type) where
  run : List UInt8 → List UInt8 → Nat → Option (Get2.Result α)

namespace Get2

instance : Monad Get2 where
  pure a := ⟨fun head tails E => some ⟨a, head, tails, E⟩⟩
  bind x f := ⟨fun head tails E =>
    match x.run head tails E with
    | none => none
    | some r => (f r.val).run r.head r.tails r.frontier⟩

/-- Failure, cursors untouched. -/
def fail : Get2 α := ⟨fun _ _ _ => none⟩

@[simp] theorem pure_run (a : α) (head tails : List UInt8) (E : Nat) :
    (pure a : Get2 α).run head tails E = some ⟨a, head, tails, E⟩ := rfl

@[simp] theorem bind_run (x : Get2 α) (f : α → Get2 β) (head tails : List UInt8) (E : Nat) :
    (x >>= f).run head tails E = (match x.run head tails E with
      | none => none
      | some r => (f r.val).run r.head r.tails r.frontier) := rfl

@[simp] theorem fail_run (head tails : List UInt8) (E : Nat) :
    (fail : Get2 α).run head tails E = none := rfl

end Get2

/-! ## GetBA: the dual-cursor reader over one `ByteArray` -/

namespace GetBA

/-- The result of a `GetBA` run: the value, the advanced cursor *offsets*,
and the new expected tail frontier. -/
structure Result (α : Type) where
  /-- The decoded value. -/
  val : α
  /-- Remaining head cursor, as an offset. -/
  head : Nat
  /-- Remaining tail cursor, as an offset. -/
  tails : Nat
  /-- New expected tail frontier. -/
  frontier : Nat

/-- The offsets read as the sub-lists they stand for — the translation the
agreement lemmas are stated over. -/
def Result.toList (ba : ByteArray) (r : Result α) : Get2.Result α :=
  ⟨r.val, ba.data.toList.drop r.head, ba.data.toList.drop r.tails, r.frontier⟩

end GetBA

/-- A dual-cursor prefix reader over one `ByteArray`: the `Get2` analogue
with the two cursors as offsets into a shared buffer. -/
structure GetBA (α : Type) where
  run : ByteArray → Nat → Nat → Nat → Option (GetBA.Result α)

namespace GetBA

instance : Monad GetBA where
  pure a := ⟨fun _ ho to E => some ⟨a, ho, to, E⟩⟩
  bind x f := ⟨fun ba ho to E =>
    match x.run ba ho to E with
    | none => none
    | some r => (f r.val).run ba r.head r.tails r.frontier⟩

@[simp] theorem pure_run (a : α) (ba : ByteArray) (ho to E : Nat) :
    (pure a : GetBA α).run ba ho to E = some ⟨a, ho, to, E⟩ := rfl

@[simp] theorem bind_run (x : GetBA α) (f : α → GetBA β) (ba : ByteArray) (ho to E : Nat) :
    (x >>= f).run ba ho to E = (match x.run ba ho to E with
      | none => none
      | some r => (f r.val).run ba r.head r.tails r.frontier) := rfl

end GetBA

end EvmAbi
