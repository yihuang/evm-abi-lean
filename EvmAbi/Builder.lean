import Binary.ByteArray
import EvmAbi.Word

/-!
# EvmAbi.Builder

A byte-string **builder** (roadmap node 13): the bridge between the
`List UInt8` the proofs are stated over and the contiguous `ByteArray`
execution wants.

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
`ByteArray` that `run` produces without reproving anything.  `EvmAbi.Encode`
builds the ABI encoder on this and inherits the whole roundtrip stack.

ABI-agnostic: depends only on the Lean 4 core library and `Binary.ByteArray`.
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
  | .append a b => a.toList ++ b.toList

/-! ## execution

`emit` appends a tree onto an accumulator with `ByteArray.push`; `Builder.run`
pre-sizes the accumulator from the cached size, so the whole traversal is one
linear pass with no reallocation. -/

/-- Push a literal byte list onto the accumulator. -/
def emitBytes (acc : ByteArray) : List UInt8 → ByteArray
  | [] => acc
  | b :: bs => emitBytes (acc.push b) bs

/-- Push `n` zero bytes onto the accumulator. -/
def emitZeros (acc : ByteArray) : Nat → ByteArray
  | 0 => acc
  | n + 1 => emitZeros (acc.push 0) n

/-- Append a chunk tree onto an accumulator. -/
def emit (acc : ByteArray) : Chunks → ByteArray
  | .empty => acc
  | .bytes bs => emitBytes acc bs
  | .chunk ba => acc ++ ba
  | .zeros n => emitZeros acc n
  | .append a b => emit (emit acc a) b

theorem data_toList_emitBytes (acc : ByteArray) (bs : List UInt8) :
    (emitBytes acc bs).data.toList = acc.data.toList ++ bs := by
  induction bs generalizing acc with
  | nil => simp [emitBytes]
  | cons b bs ih => simp [emitBytes, ih, ByteArray.data_push]

theorem data_toList_emitZeros (acc : ByteArray) (n : Nat) :
    (emitZeros acc n).data.toList = acc.data.toList ++ List.replicate n 0 := by
  induction n generalizing acc with
  | zero => simp [emitZeros]
  | succ n ih => simp [emitZeros, ih, ByteArray.data_push, List.replicate_succ]

theorem data_toList_emit (acc : ByteArray) (c : Chunks) :
    (emit acc c).data.toList = acc.data.toList ++ c.toList := by
  induction c generalizing acc with
  | empty => simp [emit, toList]
  | bytes bs => simp [emit, toList, data_toList_emitBytes]
  | chunk ba => simp [emit, toList]
  | zeros n => simp [emit, toList, data_toList_emitZeros]
  | append a b iha ihb => simp [emit, toList, iha, ihb, List.append_assoc]

end Chunks

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

/-! ## denotation -/

/-- The byte string a builder denotes. -/
def toList (b : Builder) : List UInt8 := b.chunks.toList

@[simp] theorem toList_empty : (∅ : Builder).toList = [] := rfl
@[simp] theorem toList_ofList (bs : List UInt8) : (Builder.ofList bs).toList = bs := rfl
@[simp] theorem toList_chunk (ba : ByteArray) : (Builder.chunk ba).toList = ba.data.toList := rfl
@[simp] theorem toList_zeros (n : Nat) : (Builder.zeros n).toList = List.replicate n 0 := rfl
@[simp] theorem toList_append (a b : Builder) : (a ++ b).toList = a.toList ++ b.toList := rfl

/-- The cached size agrees with the denotation — this is why `run` can size
its buffer in advance, and why the offset words the ABI layout computes from
`size` are the offsets the specification demands. -/
@[simp] theorem size_eq_length_toList (b : Builder) : b.size = b.toList.length := b.size_eq

/-! ## word primitive -/

/-- Write one 32-byte EVM word, big-endian. -/
def putWord (w : UInt256) : Builder := ofList (bytesOfWord w)

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

end EvmAbi
