import EvmAbi.Spec
import EvmAbi.Codec.ByteArray
import EvmAbi.Codec.Runtime
import EvmAbi.ValBA

namespace EvmAbi.Codec

open Ty
open Binary
open Builder
open EvmAbi.Codec.ByteArray

/-! ## the runtime encoder, streamed

`putBA` builds a `Part`, two `Builder`s and an `append` node per component,
and `emit` then walks them all.  The writers below skip the tree: each
appends a value's bytes straight into a pre-sized buffer.

Static values are the easy case — their layout is plain concatenation
(`toList_putParts_static`), so `emitVal` writes one in a single pass.  A
dynamic component needs more: its head slot holds an offset that depends on
every preceding tail's size, which is what the size tree below supplies.

The `@[csimp]` swap sits on `encode`, not `putBA`: two builders with
different trees are never equal, but the `ByteArray`s they run to are. -/

private theorem toList_putHeads_static {t : Ty} (h : t.isStatic = true)
    (vs : List (ValBA t)) (acc : Nat) :
    (putHeads acc (vs.map (partOfBA t))).toList
      = (vs.map fun v => (putBA t v).toList).flatten := by
  induction vs generalizing acc with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.map_cons, partOfBA, h, putHeads, Builder.toList_append, ih acc,
        List.flatten_cons]

private theorem toList_putTails_static {t : Ty} (h : t.isStatic = true)
    (vs : List (ValBA t)) :
    (putTails (vs.map (partOfBA t))).toList = [] := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa only [List.map_cons, partOfBA, h, putTails] using ih

/-- Static parts lay out as concatenation: the heads are the encodings and
the tail section is empty. -/
theorem toList_putParts_static {t : Ty} (h : t.isStatic = true) (vs : List (ValBA t)) :
    (putParts (vs.map (partOfBA t))).toList
      = (vs.map fun v => (putBA t v).toList).flatten := by
  rw [putParts, Builder.toList_append, toList_putHeads_static h, toList_putTails_static h,
    List.append_nil]

/-- The components' encodings, concatenated — what a static tuple's parts
lay out as. -/
private def tupleEncodings : (ts : List Ty) → TupleValBA ts → List UInt8
  | [], _ => []
  | t :: ts, (v, vs) => (putBA t v).toList ++ tupleEncodings ts vs

private theorem toList_putHeads_tupleStatic :
    ∀ {ts : List Ty}, Ty.allStatic ts = true → ∀ (vs : TupleValBA ts) (acc : Nat),
      (putHeads acc (partsOfTupleBA ts vs)).toList = tupleEncodings ts vs
  | [], _, _, _ => by simp [partsOfTupleBA, putHeads, tupleEncodings]
  | t :: ts, ht, (v, vs), acc => by
      obtain ⟨ht1, ht2⟩ : Ty.isStatic t = true ∧ Ty.allStatic ts = true := by
        simpa [Ty.allStatic] using ht
      simp only [partsOfTupleBA, partOfBA, ht1, putHeads, Builder.toList_append,
        toList_putHeads_tupleStatic ht2 vs acc, tupleEncodings]

private theorem toList_putTails_tupleStatic :
    ∀ {ts : List Ty}, Ty.allStatic ts = true → ∀ (vs : TupleValBA ts),
      (putTails (partsOfTupleBA ts vs)).toList = []
  | [], _, _ => by simp [partsOfTupleBA, putTails]
  | t :: ts, ht, (v, vs) => by
      obtain ⟨ht1, ht2⟩ : Ty.isStatic t = true ∧ Ty.allStatic ts = true := by
        simpa [Ty.allStatic] using ht
      simpa only [partsOfTupleBA, partOfBA, ht1, putTails]
        using toList_putTails_tupleStatic ht2 vs

/-- Static tuple parts lay out as concatenation — the `partsOfTupleBA`
sibling of `toList_putParts_static`. -/
theorem toList_putParts_tupleStatic {ts : List Ty} (ht : Ty.allStatic ts = true)
    (vs : TupleValBA ts) :
    (putParts (partsOfTupleBA ts vs)).toList = tupleEncodings ts vs := by
  rw [putParts, Builder.toList_append, toList_putHeads_tupleStatic ht,
    toList_putTails_tupleStatic ht, List.append_nil]

/-- Write one `uint` word from a `Nat`, without ever building a `UInt256`:
`UInt256.ofNat` goes through `BitVec.ofNat 256`, which is bignum work even
for `0`.  Below `2 ^ 64` — every array length and offset in practice — the
24 leading zeros are one `copySlice` and the value one limb; above it, the
limbs come straight off the `Nat`. -/
def emitUintWord (acc : ByteArray) (n : Nat) : ByteArray :=
  if n < 2 ^ 64 then pushBELimb (UInt64.ofNat n) (Chunks.pushZeros32 acc 24)
  else encodeBEBytesFast.loop acc 32 n

theorem data_toList_emitUintWord (acc : ByteArray) (n : Nat) :
    (emitUintWord acc n).data.toList = acc.data.toList ++ encodeUint n := by
  rw [emitUintWord]
  split
  · next hn =>
      rw [pushBELimb_eq, Chunks.data_toList_pushZeros32 _ (by omega), encodeUint_eq,
        encodeBEU_window (by omega), show (32 : Nat) = 8 + 24 from rfl,
        encodeBEU_pad (show n < 256 ^ 8 by omega) 24, List.append_assoc]
  · next _ => rw [encodeBEBytesFast.loop_eq, encodeUint_eq]

/- A size measure for `Ty`/`List Ty` that is cheap to evaluate and keeps
a `tuple` type strictly larger than the corresponding cons-list, which is
what lets the tuple/list mutual recursions below use a lexicographic
`Nat` measure. -/
mutual
private def tyMeasure : Ty → Nat
  | .uint _ | .int _ | .bool | .address | .bytesN _ | .bytes | .string => 1
  | .array t => tyMeasure t + 2
  | .fixedArray t _ _ => tyMeasure t + 2
  | .tuple head tail => tyListMeasure (head :: tail) + 2

private def tyListMeasure : List Ty → Nat
  | [] => 1
  | t :: ts => tyMeasure t + tyListMeasure ts + 1
end

@[simp] private theorem tyMeasure_array (t : Ty) : tyMeasure (.array t) = tyMeasure t + 2 := by
  rw [tyMeasure]

@[simp] private theorem tyMeasure_fixedArray (t : Ty) (n : Nat) (h : 0 < n) :
    tyMeasure (.fixedArray t n h) = tyMeasure t + 2 := by
  rw [tyMeasure]

@[simp] private theorem tyMeasure_tuple (head : Ty) (tail : List Ty) :
    tyMeasure (.tuple head tail) = tyListMeasure (head :: tail) + 2 := by
  rw [tyMeasure]

@[simp] private theorem tyListMeasure_cons (t : Ty) (ts : List Ty) :
    tyListMeasure (t :: ts) = tyMeasure t + tyListMeasure ts + 1 := by
  rw [tyListMeasure]

/-- Write one primitive static value straight into the accumulator: words by
their limbs, `bytesN` payloads by one append and one padding copy (skipped
when the payload fills its word).  `@[specialize t]` lets the fused element
loop compile a copy with the `Ty` match already resolved. -/
@[inline, specialize t]
def emitPrim (t : Ty) (acc : ByteArray) (v : ValBA t) : ByteArray :=
  match t, v with
  | .uint _, ⟨w, _⟩ => Chunks.emitWord acc w
  | .int _, ⟨i, _⟩ =>
      emitUintWord acc (if 0 ≤ i then i.toNat else 2 ^ 256 - (-i).toNat)
  | .bool, b => emitUintWord acc (if b then 1 else 0)
  | .address, ⟨bs, _⟩ => emitUintWord acc (decodeBEU bs.data.toList)
  | .bytesN _, ⟨bs, _⟩ =>
      if bs.size == 32 then acc ++ bs else Chunks.pushZeros32 (acc ++ bs) (32 - bs.size)
  | _, _ => acc

mutual
/-- Write one static value straight into the accumulator: primitives through
`emitPrim`, static compounds by concatenation.  Dynamic types return `acc`
untouched — `data_toList_emitVal` is guarded by `isStatic`, and the fused arm
never reaches them. -/
def emitVal (acc : ByteArray) : (t : Ty) → ValBA t → ByteArray
  | .uint m, v => emitPrim (.uint m) acc v
  | .int m, v => emitPrim (.int m) acc v
  | .bool, v => emitPrim .bool acc v
  | .address, v => emitPrim .address acc v
  | .bytesN m, v => emitPrim (.bytesN m) acc v
  | .fixedArray t _ _, ⟨vs, _⟩ => emitVals acc t vs
  | .tuple head tail, (v, vs) => emitTupleVals acc (head :: tail) (v, vs)
  | .bytes, _ => acc
  | .string, _ => acc
  | .array _, _ => acc
termination_by t _ => (tyMeasure t, 0)

/-- `emitVal` each element in order. -/
def emitVals (acc : ByteArray) (t : Ty) : List (ValBA t) → ByteArray
  | [] => acc
  | v :: vs => emitVals (emitVal acc t v) t vs
termination_by vs => (tyMeasure t, 1 + vs.length)

/-- `emitVal` each component in order. -/
def emitTupleVals (acc : ByteArray) : (ts : List Ty) → TupleValBA ts → ByteArray
  | [], _ => acc
  | t :: ts, (v, vs) => emitTupleVals (emitVal acc t v) ts vs
termination_by ts _ => (tyListMeasure ts, 1)
end

/-- One structural loop over elements, with the per-element step supplied as a
function parameter.  `@[specialize]` inlines a concrete step at each call site,
so this is the shared body of every fused element loop. -/
@[specialize] def emitValsWith {t : Ty} (write : ByteArray → ValBA t → ByteArray)
    (acc : ByteArray) : List (ValBA t) → ByteArray
  | [] => acc
  | v :: vs => emitValsWith write (write acc v) vs

/-! ### fused element loops

`emitVals` matches on the element `Ty` once per element, and that match compiles
to fourteen `lean_dec` inside `emitVal`.  An array of static elements pays it per
element.  `emitValsWith` fixes the per-element step at the call site instead, so
the loop's body has no `Ty` scrutinee and compiles to no reference-count traffic
at all. -/

/-- `emitVals` is the generic specialized loop at any per-element step that is
`emitVal` at the fixed type. -/
theorem emitVals_eq_with {t : Ty} {write : ByteArray → ValBA t → ByteArray}
    (hwrite : ∀ acc v, write acc v = emitVal acc t v) :
    ∀ (acc : ByteArray) (vs : List (ValBA t)),
      emitVals acc t vs = emitValsWith write acc vs
  | _, [] => by rw [emitVals, emitValsWith]
  | _, v :: _ => by rw [emitVals, emitValsWith, hwrite, emitVals_eq_with hwrite]

/-- An `n`-element static-element array's length word, in a buffer sized for the
whole encoding: that word plus `n` element slots. -/
def staticElemsHead (n : Nat) : ByteArray :=
  emitUintWord (ByteArray.emptyWithCapacity (32 + 32 * n)) n

mutual
theorem data_toList_emitVal :
    ∀ {t : Ty}, t.isStatic = true → ∀ (acc : ByteArray) (v : ValBA t),
      (emitVal acc t v).data.toList = acc.data.toList ++ (putBA t v).toList
  | .uint _, ht, acc, ⟨w, hw⟩ => by
      rw [emitVal, emitPrim, Chunks.data_toList_emitWord, putBA, toList_putWord]
  | .int _, ht, acc, ⟨i, hi⟩ => by
      rw [emitVal, emitPrim, data_toList_emitUintWord, putBA]
      simp only [toList_putInt, encodeInt]
  | .bool, ht, acc, b => by
      rw [emitVal, emitPrim, data_toList_emitUintWord, putBA]
      simp only [toList_putBool, encodeBool]
  | .address, ht, acc, ⟨bs, hbs⟩ => by
      rw [emitVal, emitPrim, data_toList_emitUintWord, putBA, toList_putAddressBA]
      simp [encodeAddress]
  | .bytesN _, ht, acc, ⟨bs, hbs⟩ => by
      rw [emitVal, emitPrim, putBA, toList_putBytesNBA]
      split
      · next hbeq =>
          have h32 : bs.size = 32 := by simpa using hbeq
          simp [encodeBytesN, h32]
      · next _ =>
          rw [Chunks.data_toList_pushZeros32 _ (by omega)]
          simp [encodeBytesN, List.append_assoc]
  | .fixedArray t _ _, ht, acc, ⟨vs, hvs⟩ => by
      have ht' : t.isStatic = true := ht
      rw [emitVal, putBA, toList_putParts_static ht', data_toList_emitVals ht']
  | .tuple head tail, ht, acc, (v, vs) => by
      have ht' : Ty.allStatic (head :: tail) = true := by
        simpa [Ty.isStatic, Ty.allStatic] using ht
      rw [emitVal, putBA,
        show putParts (partOfBA head v :: partsOfTupleBA tail vs) =
          putParts (partsOfTupleBA (head :: tail) (v, vs)) by simp [partsOfTupleBA],
        toList_putParts_tupleStatic ht', data_toList_emitTupleVals ht']
  | .bytes, ht, _, _ => Bool.noConfusion ht
  | .string, ht, _, _ => Bool.noConfusion ht
  | .array _, ht, _, _ => Bool.noConfusion ht
termination_by t => (tyMeasure t, 0)

theorem data_toList_emitVals {t : Ty} (ht : t.isStatic = true) (acc : ByteArray) :
    ∀ (vs : List (ValBA t)),
      (emitVals acc t vs).data.toList
        = acc.data.toList ++ (vs.map fun v => (putBA t v).toList).flatten
  | [] => by simp [emitVals]
  | v :: vs => by
      rw [emitVals, data_toList_emitVals ht (emitVal acc t v) vs,
        data_toList_emitVal ht acc v, List.map_cons, List.flatten_cons, List.append_assoc]
termination_by vs => (tyMeasure t, 1 + vs.length)

theorem data_toList_emitTupleVals :
    ∀ {ts : List Ty}, Ty.allStatic ts = true → ∀ (acc : ByteArray) (vs : TupleValBA ts),
      (emitTupleVals acc ts vs).data.toList = acc.data.toList ++ tupleEncodings ts vs
  | [], _, acc, _ => by simp [emitTupleVals, tupleEncodings]
  | t :: ts, ht, acc, (v, vs) => by
      obtain ⟨ht1, ht2⟩ : Ty.isStatic t = true ∧ Ty.allStatic ts = true := by
        simpa [Ty.allStatic] using ht
      rw [emitTupleVals, data_toList_emitTupleVals ht2 (emitVal acc t v) vs,
        data_toList_emitVal ht1 acc v, tupleEncodings, List.append_assoc]
termination_by ts => (tyListMeasure ts, 1)
end

/-! ### `bytes[]` and `string[]`

A `bytes` or `string` tail is its payload's length word plus padding, so its
size is one `O(1)` read off the payload — no recursion, and the offsets are
a running sum.  These arrays therefore need no size tree: the length word,
every offset word and every tail stream in one forward pass.  The walkers
take the payload projection, so `string` measures by `utf8ByteSize` and
materializes `toUTF8` only in the tail. -/

/-- The tail a dynamic payload of `n` bytes occupies: its length word plus
the padded payload. -/
def dynTailSize (n : Nat) : Nat := 32 + (n + (32 - n % 32) % 32)

/-- The builder's cached tail size is `dynTailSize`. -/
theorem size_putBytesBA (bs : ByteArray) : (putBytesBA bs).size = dynTailSize bs.size := by
  rw [Builder.size_eq_length_toList, toList_putBytesBA, dynTailSize, encodeBytes]
  simp [length_pad32]

/-- Every dynamic part occupies 32 head bytes. -/
private theorem headSizes_dynamic {t : Ty} (hd : t.isStatic = false)
    (vs : List (ValBA t)) :
    headSizes (vs.map (partOfBA t)) = 32 * vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      simp only [List.map_cons, partOfBA, hd, headSizes, Part.headSize, ih,
        List.length_cons]
      omega

/-- Write the offset words: `off` starts at the head section's size and
steps by each tail, sized by `sizeF` without materializing the payload. -/
@[specialize] def emitDynHeads {t : Ty} (sizeF : ValBA t → Nat)
    (acc : ByteArray) (off : Nat) : List (ValBA t) → ByteArray
  | [] => acc
  | v :: vs => emitDynHeads sizeF (emitUintWord acc off) (off + dynTailSize (sizeF v)) vs

/-- Write one dynamic payload: its length word, the payload, its padding —
the padding skipped when the payload is already word-aligned. -/
@[inline] def emitPayload (acc : ByteArray) (bs : ByteArray) : ByteArray :=
  if bs.size % 32 == 0 then emitUintWord acc bs.size ++ bs
  else Chunks.pushZeros32 (emitUintWord acc bs.size ++ bs) ((32 - bs.size % 32) % 32)

theorem data_toList_emitPayload (acc bs : ByteArray) :
    (emitPayload acc bs).data.toList = acc.data.toList ++ encodeBytes bs.data.toList := by
  rw [emitPayload]
  split
  · next hbeq =>
      have h0 : (32 - bs.size % 32) % 32 = 0 := by
        have : bs.size % 32 = 0 := by simpa using hbeq
        omega
      simp [data_toList_emitUintWord, encodeBytes, pad32, h0, List.append_assoc]
  · next _ =>
      rw [Chunks.data_toList_pushZeros32 _ (by omega)]
      simp [data_toList_emitUintWord, encodeBytes, pad32, List.append_assoc]

/-- Write the tails: each element's payload in order. -/
@[specialize] def emitDynTails {t : Ty} (payloadF : ValBA t → ByteArray)
    (acc : ByteArray) : List (ValBA t) → ByteArray
  | [] => acc
  | v :: vs => emitDynTails payloadF (emitPayload acc (payloadF v)) vs

theorem data_toList_emitDynHeads {t : Ty} (hd : t.isStatic = false)
    {sizeF : ValBA t → Nat}
    (hsize : ∀ v : ValBA t, (putBA t v).size = dynTailSize (sizeF v))
    (acc : ByteArray) (off : Nat) (vs : List (ValBA t)) :
    (emitDynHeads sizeF acc off vs).data.toList
      = acc.data.toList ++ (putHeads off (vs.map (partOfBA t))).toList := by
  induction vs generalizing acc off with
  | nil => simp [emitDynHeads, putHeads]
  | cons v vs ih =>
      rw [emitDynHeads, ih, data_toList_emitUintWord]
      simp only [List.map_cons, partOfBA, hd, putHeads, Builder.toList_append,
        toList_putUint, hsize v, List.append_assoc]

theorem data_toList_emitDynTails {t : Ty} (hd : t.isStatic = false)
    {payloadF : ValBA t → ByteArray}
    (hput : ∀ v : ValBA t, (putBA t v).toList = encodeBytes (payloadF v).data.toList)
    (acc : ByteArray) (vs : List (ValBA t)) :
    (emitDynTails payloadF acc vs).data.toList
      = acc.data.toList ++ (putTails (vs.map (partOfBA t))).toList := by
  induction vs generalizing acc with
  | nil => simp [emitDynTails, putTails]
  | cons v vs ih =>
      rw [emitDynTails, ih, data_toList_emitPayload]
      simp only [List.map_cons, partOfBA, hd, putTails, Builder.toList_append, hput v,
        List.append_assoc]

/-! The per-type facts the walkers are instantiated with. -/

private theorem size_putBA_bytes : ∀ v : ValBA .bytes,
    (putBA .bytes v).size = dynTailSize v.val.size
  | ⟨_, _⟩ => by simp only [putBA, size_putBytesBA]

private theorem toList_putBA_bytes : ∀ v : ValBA .bytes,
    (putBA .bytes v).toList = encodeBytes v.val.data.toList
  | ⟨_, _⟩ => by simp only [putBA, toList_putBytesBA]

private theorem toUTF8_size (s : String) : s.toUTF8.size = s.utf8ByteSize :=
  Nat.add_zero _

private theorem size_putBA_string : ∀ v : ValBA .string,
    (putBA .string v).size = dynTailSize v.val.utf8ByteSize
  | ⟨s, _⟩ => by
      simp only [putBA]
      show (putBytesBA s.toUTF8).size = _
      rw [size_putBytesBA, toUTF8_size]

private theorem toList_putBA_string : ∀ v : ValBA .string,
    (putBA .string v).toList = encodeBytes (v.val.toUTF8).data.toList
  | ⟨s, _⟩ => by simp only [putBA, toList_putString, encodeString]

/-! `putBA`'s container arms, unfolded once so proofs can name them. -/

private theorem putBA_array {t : Ty} (vs : List (ValBA t)) (h : vs.length < 2 ^ 64) :
    putBA (.array t) ⟨vs, h⟩ = putUint vs.length ++ putParts (vs.map (partOfBA t)) := by
  rw [putBA]

private theorem putBA_fixedArray {t : Ty} {n : Nat} (hn : 0 < n)
    (vs : List (ValBA t)) (h : vs.length = n) :
    putBA (.fixedArray t n hn) ⟨vs, h⟩ = putParts (vs.map (partOfBA t)) := by rw [putBA]

private theorem putBA_tuple {head : Ty} {tail : List Ty} (v : ValBA head)
    (vs : TupleValBA tail) :
    putBA (.tuple head tail) (v, vs) =
      putParts (partsOfTupleBA (head :: tail) (v, vs)) := by
  rw [putBA]
  simp [partsOfTupleBA]

/-! ### sizes

Three sizes of the builder's leaves, for the size tree's proof. -/

private theorem size_append (a b : Builder) : (a ++ b).size = a.size + b.size := rfl

private theorem size_putUint (n : Nat) : (putUint n).size = 32 := by
  rw [Builder.size_eq_length_toList, toList_putUint, length_encodeUint]

private theorem size_putBytesNBA (bs : ByteArray) :
    (putBytesNBA bs).size = bs.size + (32 - bs.size) := by
  rw [Builder.size_eq_length_toList, toList_putBytesNBA]
  simp [encodeBytesN]

/-! ### static sizes

A static value's size is fixed by its type, so the static arm sizes its
buffer from `staticSize` and skips the size pass, and the size tree sizes a
static array from its length alone.  It is `Ty.headSize` except at `bytesN m`
with `m > 32`, where the payload is `m` bytes rather than one word — using
`headSize` there would under-allocate. -/

mutual
/-- Encoded bytes of a static type, from the type alone. -/
def staticSize : Ty → Nat
  | .fixedArray t n _ => n * staticSize t
  | .tuple head tail => staticSize head + staticSizeSum tail
  -- `bytesN` is its payload plus right padding to the word, i.e. 32 for every
  -- legal width; saying so keeps the fused array arms' proof arithmetic-free
  | .uint _ | .int _ | .bool | .address | .bytesN _
  | .bytes | .string | .array _ => 32
termination_by t => sizeOf t

/-- Encoded bytes of a static component list. -/
def staticSizeSum : List Ty → Nat
  | [] => 0
  | t :: ts => staticSize t + staticSizeSum ts
termination_by ts => sizeOf ts
end

/-! ### the size tree

Sizing a subtree per head slot would re-walk it once per ancestor —
measured 51 → 372 µs/op on `nest 200`.  `sizesOf` instead computes every
dynamic subvalue's size bottom-up in one pass, one node per subvalue, so the
writer reads each offset off the tree in `O(1)`. -/

/-- One node per dynamic subvalue: its total encoded size, and its
children's trees.  Static subtrees carry no children — nothing below them
is offset-addressed. -/
structure SizeT where
  /-- Total encoded bytes of this subvalue. -/
  total : Nat
  /-- One node per dynamic child, in order. -/
  children : List SizeT

/-- Head-plus-tail bytes of a dynamic-element run, off the totals. -/
def sumDyn : List SizeT → Nat
  | [] => 0
  | c :: cs => 32 + c.total + sumDyn cs

/-- Head-plus-tail bytes of a component run, off the totals. -/
def sumTuple : (ts : List Ty) → List SizeT → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | t :: ts, c :: cs => (if t.isStatic then c.total else 32 + c.total) + sumTuple ts cs

mutual
/-- Every dynamic subvalue's size, in one bottom-up pass. -/
def sizesOf : (t : Ty) → ValBA t → SizeT
  | .uint _, _ => .mk 32 []
  | .int _, _ => .mk 32 []
  | .bool, _ => .mk 32 []
  | .address, _ => .mk 32 []
  | .bytesN _, ⟨bs, _⟩ => .mk (bs.size + (32 - bs.size)) []
  | .bytes, ⟨bs, _⟩ => .mk (dynTailSize bs.size) []
  | .string, ⟨s, _⟩ => .mk (dynTailSize s.utf8ByteSize) []
  | .array t, ⟨vs, _⟩ =>
      if t.isStatic then .mk (32 + vs.length * staticSize t) []
      else
        let cs := sizesOfList t vs
        .mk (32 + sumDyn cs) cs
  | .fixedArray t _ _, ⟨vs, _⟩ =>
      if t.isStatic then .mk (vs.length * staticSize t) []
      else
        let cs := sizesOfList t vs
        .mk (sumDyn cs) cs
  | .tuple head tail, (v, vs) =>
      let cs := sizesOf head v :: sizesOfTuple tail vs
      .mk (sumTuple (head :: tail) cs) cs
termination_by t _ => (sizeOf t, 0)

def sizesOfList (t : Ty) : List (ValBA t) → List SizeT
  | [] => []
  | v :: vs => sizesOf t v :: sizesOfList t vs
termination_by vs => (sizeOf t, 1 + vs.length)

def sizesOfTuple : (ts : List Ty) → TupleValBA ts → List SizeT
  | [], _ => []
  | t :: ts, (v, vs) => sizesOf t v :: sizesOfTuple ts vs
termination_by ts _ => (sizeOf ts, 0)
end

mutual
/-- The tree's total is the byte count `putBA` runs to. -/
theorem total_sizesOf : ∀ (t : Ty) (v : ValBA t), (sizesOf t v).total = (putBA t v).size
  | .uint _, ⟨_, _⟩ => by rw [sizesOf, putBA]; exact rfl
  | .int _, ⟨_, _⟩ => by rw [sizesOf, putBA]; exact (size_putUint _).symm
  | .bool, _ => by rw [sizesOf, putBA]; exact (size_putUint _).symm
  | .address, ⟨_, _⟩ => by rw [sizesOf, putBA]; exact (size_putUint _).symm
  | .bytesN _, ⟨bs, _⟩ => by rw [sizesOf, putBA]; exact (size_putBytesNBA bs).symm
  | .bytes, ⟨bs, _⟩ => by rw [sizesOf, putBA]; exact (size_putBytesBA bs).symm
  | .string, ⟨s, _⟩ => by
      rw [sizesOf, putBA]
      show _ = (putBytesBA s.toUTF8).size
      rw [size_putBytesBA, toUTF8_size]
  | .array t, ⟨vs, h⟩ => by
      rw [sizesOf, putBA_array vs h, size_append, size_putUint]
      by_cases hst : t.isStatic
      · rw [if_pos hst, size_parts_static hst vs]
      · rw [if_neg hst]
        have hst' : t.isStatic = false := by simpa using hst
        show 32 + sumDyn (sizesOfList t vs) = 32 + _
        rw [size_parts_dyn t hst' vs]
  | .fixedArray t n hn, ⟨vs, h⟩ => by
      rw [sizesOf, putBA_fixedArray hn vs h]
      by_cases hst : t.isStatic
      · rw [if_pos hst, size_parts_static hst vs]
      · rw [if_neg hst]
        have hst' : t.isStatic = false := by simpa using hst
        show sumDyn (sizesOfList t vs) = _
        rw [size_parts_dyn t hst' vs]
  | .tuple head tail, (v, vs) => by
      rw [sizesOf, putBA_tuple v vs, size_parts_tuple (head :: tail) (v, vs)]
      simp [sizesOfTuple]
termination_by t _ => (tyMeasure t, 0)

private theorem size_parts_dyn : ∀ (t : Ty), t.isStatic = false → ∀ (vs : List (ValBA t)),
    (putParts (vs.map (partOfBA t))).size = sumDyn (sizesOfList t vs)
  | t, hst, vs => by
      rw [putParts, size_append, heads_tails_dyn t hst vs (headSizes (vs.map (partOfBA t)))]
termination_by t _ vs => (tyMeasure t, 2 + vs.length)

private theorem heads_tails_dyn : ∀ (t : Ty), t.isStatic = false →
    ∀ (vs : List (ValBA t)) (acc : Nat),
    (putHeads acc (vs.map (partOfBA t))).size + (putTails (vs.map (partOfBA t))).size
      = sumDyn (sizesOfList t vs)
  | t, hst, [], acc => by simp [putHeads, putTails, sizesOfList, sumDyn]
  | t, hst, v :: vs, acc => by
      rw [sizesOfList, sumDyn, total_sizesOf t v]
      simp only [List.map_cons, partOfBA, hst, putHeads, putTails, size_append, size_putUint]
      have ih := heads_tails_dyn t hst vs (acc + (putBA t v).size)
      omega
termination_by t _ vs _ => (tyMeasure t, 1 + vs.length)

private theorem size_parts_static : ∀ {t : Ty}, t.isStatic = true → ∀ (vs : List (ValBA t)),
    (putParts (vs.map (partOfBA t))).size = vs.length * staticSize t
  | t, hst, vs => by
      rw [putParts, size_append, heads_tails_static hst vs (headSizes (vs.map (partOfBA t)))]
termination_by t _ vs => (tyMeasure t, 2 + vs.length)

private theorem heads_tails_static : ∀ {t : Ty}, t.isStatic = true →
    ∀ (vs : List (ValBA t)) (acc : Nat),
    (putHeads acc (vs.map (partOfBA t))).size + (putTails (vs.map (partOfBA t))).size
      = vs.length * staticSize t
  | t, hst, [], acc => by simp [putHeads, putTails]
  | t, hst, v :: vs, acc => by
      simp only [List.map_cons, partOfBA, hst, putHeads, putTails, size_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      rw [size_static hst v]
      have ih := heads_tails_static hst vs acc
      omega
termination_by t _ vs _ => (tyMeasure t, 1 + vs.length)

private theorem size_parts_tuple : ∀ (ts : List Ty) (vs : TupleValBA ts),
    (putParts (partsOfTupleBA ts vs)).size = sumTuple ts (sizesOfTuple ts vs)
  | ts, vs => by
      rw [putParts, size_append, heads_tails_tuple ts vs (headSizes (partsOfTupleBA ts vs))]
termination_by ts _ => (tyListMeasure ts, 2)

private theorem heads_tails_tuple : ∀ (ts : List Ty) (vs : TupleValBA ts) (acc : Nat),
    (putHeads acc (partsOfTupleBA ts vs)).size + (putTails (partsOfTupleBA ts vs)).size
      = sumTuple ts (sizesOfTuple ts vs)
  | [], _, acc => by rw [partsOfTupleBA, sizesOfTuple, sumTuple]; simp [putHeads, putTails]
  | t :: ts, (v, vs), acc => by
      rw [partsOfTupleBA, sizesOfTuple, sumTuple, total_sizesOf t v]
      by_cases hst : t.isStatic
      · rw [if_pos hst]
        simp only [partOfBA, hst, putHeads, putTails, size_append]
        have ih := heads_tails_tuple ts vs acc
        omega
      · rw [if_neg hst]
        have hst' : t.isStatic = false := by simpa using hst
        simp only [partOfBA, hst', putHeads, putTails, size_append, size_putUint]
        have ih := heads_tails_tuple ts vs (acc + (putBA t v).size)
        omega
termination_by ts _ _ => (tyListMeasure ts, 1)

private theorem size_parts_tupleStatic : ∀ {ts : List Ty}, Ty.allStatic ts = true →
    ∀ vs : TupleValBA ts, (putParts (partsOfTupleBA ts vs)).size = staticSizeSum ts
  | ts, ht, vs => by
      rw [putParts, size_append,
        heads_tails_tupleStatic ht vs (headSizes (partsOfTupleBA ts vs))]
termination_by ts _ _ => (tyListMeasure ts, 2)

private theorem heads_tails_tupleStatic : ∀ {ts : List Ty}, Ty.allStatic ts = true →
    ∀ (vs : TupleValBA ts) (acc : Nat),
    (putHeads acc (partsOfTupleBA ts vs)).size + (putTails (partsOfTupleBA ts vs)).size
      = staticSizeSum ts
  | [], _, _, acc => by rw [partsOfTupleBA, staticSizeSum]; simp [putHeads, putTails]
  | t :: ts, ht, (v, vs), acc => by
      obtain ⟨h1, h2⟩ : Ty.isStatic t = true ∧ Ty.allStatic ts = true := by
        simpa [Ty.allStatic] using ht
      rw [partsOfTupleBA, staticSizeSum]
      simp only [partOfBA, h1, putHeads, putTails, size_append]
      rw [size_static h1 v]
      have ih := heads_tails_tupleStatic h2 vs acc
      omega
termination_by ts _ _ _ => (tyListMeasure ts, 1)

/-- A static value's size is its type's. -/
private theorem size_static : ∀ {t : Ty}, t.isStatic = true → ∀ v : ValBA t,
    (putBA t v).size = staticSize t
  | .uint _, _, ⟨_, _⟩ => by rw [putBA, staticSize]; exact rfl
  | .int _, _, ⟨_, _⟩ => by rw [putBA, staticSize]; exact size_putUint _
  | .bool, _, _ => by rw [putBA, staticSize]; exact size_putUint _
  | .address, _, ⟨_, _⟩ => by rw [putBA, staticSize]; exact size_putUint _
  | .bytesN m, _, ⟨bs, hbs⟩ => by
      rw [putBA, staticSize, size_putBytesNBA, hbs]
      have : m.bytes ≤ 32 := by unfold Width.bytes; omega
      omega
  | .fixedArray t n hn, ht, ⟨vs, hvs⟩ => by
      rw [putBA_fixedArray hn vs hvs, staticSize, size_parts_static (t := t) ht vs, hvs]
  | .tuple head tail, ht, (v, vs) => by
      have ht' : Ty.allStatic (head :: tail) = true := by
        simpa [Ty.isStatic, Ty.allStatic] using ht
      rw [putBA_tuple v vs, staticSize, size_parts_tupleStatic (ts := head :: tail) ht' (v, vs)]
      simp [staticSizeSum]
  | .bytes, ht, _ => Bool.noConfusion ht
  | .string, ht, _ => Bool.noConfusion ht
  | .array _, ht, _ => Bool.noConfusion ht
termination_by t _ _ => (tyMeasure t, 0)

end

/-! ### the general writer

`emitAny` appends any value at all, offsets read off the size tree: statics
through `emitVal`, dynamic leaves as one payload, compounds heads-then-tails.
With it the builder never runs at runtime — it stays the specification every
lemma here is stated against. -/

/-- Write the offset words of a dynamic-element run — totals only, no
values. -/
def emitOffsets (acc : ByteArray) (off : Nat) : List SizeT → ByteArray
  | [] => acc
  | c :: cs => emitOffsets (emitUintWord acc off) (off + c.total) cs

/-- Write a tuple's head section: static components by value, dynamic ones
as offset words stepping by their totals. -/
def emitTupleHeads (acc : ByteArray) (off : Nat) :
    (ts : List Ty) → TupleValBA ts → List SizeT → ByteArray
  | [], _, _ => acc
  | _ :: _, _, [] => acc
  | t :: ts, (v, vs), c :: cs =>
      if t.isStatic then emitTupleHeads (emitVal acc t v) off ts vs cs
      else emitTupleHeads (emitUintWord acc off) (off + c.total) ts vs cs

/-- A tuple's head-section size, off the totals. -/
def tupleBase : (ts : List Ty) → List SizeT → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | t :: ts, c :: cs => (if t.isStatic then c.total else 32) + tupleBase ts cs

mutual
/-- Append any value's encoding, offsets off the size tree. -/
def emitAny (acc : ByteArray) : (t : Ty) → ValBA t → SizeT → ByteArray
  | .bytes, v, _ => emitPayload acc v.val
  | .string, v, _ => emitPayload acc v.val.toUTF8
  | .array t, v, st =>
      if t.isStatic then emitVals (emitUintWord acc v.val.length) t v.val
      else
        emitAnyTails t
          (emitOffsets (emitUintWord acc v.val.length) (32 * v.val.length) st.children)
          v.val st.children
  | .fixedArray t _ _, v, st =>
      if t.isStatic then emitVals acc t v.val
      else emitAnyTails t (emitOffsets acc (32 * v.val.length) st.children) v.val st.children
  | .tuple head tail, (v, vs), st =>
      emitAnyTupleTails
        (emitTupleHeads acc (tupleBase (head :: tail) st.children) (head :: tail) (v, vs) st.children)
        (head :: tail) (v, vs) st.children
  | .uint m, v, _ => emitVal acc (.uint m) v
  | .int m, v, _ => emitVal acc (.int m) v
  | .bool, v, _ => emitVal acc .bool v
  | .address, v, _ => emitVal acc .address v
  | .bytesN m, v, _ => emitVal acc (.bytesN m) v
termination_by t _ _ => (tyMeasure t, 0)

/-- Append the tails of a dynamic-element run. -/
def emitAnyTails (t : Ty) (acc : ByteArray) : List (ValBA t) → List SizeT → ByteArray
  | [], _ => acc
  | _ :: _, [] => acc
  | v :: vs, c :: cs => emitAnyTails t (emitAny acc t v c) vs cs
termination_by vs _ => (tyMeasure t, 1 + vs.length)

/-- Append a tuple's tail section: the dynamic components' encodings. -/
def emitAnyTupleTails (acc : ByteArray) : (ts : List Ty) → TupleValBA ts → List SizeT → ByteArray
  | [], _, _ => acc
  | _ :: _, _, [] => acc
  | t :: ts, (v, vs), c :: cs =>
      if t.isStatic then emitAnyTupleTails acc ts vs cs
      else emitAnyTupleTails (emitAny acc t v c) ts vs cs
termination_by ts _ _ => (tyListMeasure ts, 1)
end

/-- Size pass, then one write pass: the whole encoding in two walks. -/
def emitAnyRun (t : Ty) (v : ValBA t) : ByteArray :=
  let st := sizesOf t v
  emitAny (ByteArray.emptyWithCapacity st.total) t v st

private theorem data_toList_emitOffsets (t : Ty) (hst : t.isStatic = false) :
    ∀ (vs : List (ValBA t)) (acc : ByteArray) (off : Nat),
      (emitOffsets acc off (sizesOfList t vs)).data.toList
        = acc.data.toList ++ (putHeads off (vs.map (partOfBA t))).toList := by
  intro vs
  induction vs with
  | nil => intro acc off; rw [sizesOfList]; simp [emitOffsets, putHeads]
  | cons v vs ih =>
      intro acc off
      rw [sizesOfList, emitOffsets, ih, data_toList_emitUintWord, total_sizesOf t v]
      simp only [List.map_cons, partOfBA, hst, putHeads, Builder.toList_append,
        toList_putUint, List.append_assoc]

private theorem data_toList_emitTupleHeads :
    ∀ {ts : List Ty} (vs : TupleValBA ts) (acc : ByteArray) (off : Nat),
      (emitTupleHeads acc off ts vs (sizesOfTuple ts vs)).data.toList
        = acc.data.toList ++ (putHeads off (partsOfTupleBA ts vs)).toList
  | [], _, acc, off => by rw [sizesOfTuple]; simp [emitTupleHeads, partsOfTupleBA, putHeads]
  | t :: ts, (v, vs), acc, off => by
      rw [sizesOfTuple, emitTupleHeads]
      by_cases hst : t.isStatic
      · rw [if_pos hst, data_toList_emitTupleHeads vs, data_toList_emitVal hst]
        simp only [partsOfTupleBA, partOfBA, hst, putHeads, Builder.toList_append,
          List.append_assoc]
      · have hst' : t.isStatic = false := by simpa using hst
        rw [if_neg hst, data_toList_emitTupleHeads vs, data_toList_emitUintWord,
          total_sizesOf t v]
        simp only [partsOfTupleBA, partOfBA, hst', putHeads, Builder.toList_append,
          toList_putUint, List.append_assoc]

private theorem tupleBase_eq : ∀ (ts : List Ty) (vs : TupleValBA ts),
    tupleBase ts (sizesOfTuple ts vs) = headSizes (partsOfTupleBA ts vs)
  | [], _ => by rw [sizesOfTuple, tupleBase, partsOfTupleBA]; rfl
  | t :: ts, (v, vs) => by
      rw [sizesOfTuple, tupleBase, partsOfTupleBA]
      by_cases hst : t.isStatic
      · rw [if_pos hst, total_sizesOf t v, tupleBase_eq ts vs]
        simp only [partOfBA, hst, headSizes, Part.headSize]
      · rw [if_neg hst, tupleBase_eq ts vs]
        have hst' : t.isStatic = false := by simpa using hst
        simp only [partOfBA, hst', headSizes, Part.headSize]

mutual
theorem data_toList_emitAny : ∀ {t : Ty} (acc : ByteArray) (v : ValBA t),
    (emitAny acc t v (sizesOf t v)).data.toList = acc.data.toList ++ (putBA t v).toList
  | .uint _, acc, v => by rw [emitAny]; exact data_toList_emitVal rfl acc v
  | .int _, acc, v => by rw [emitAny]; exact data_toList_emitVal rfl acc v
  | .bool, acc, v => by rw [emitAny]; exact data_toList_emitVal rfl acc v
  | .address, acc, v => by rw [emitAny]; exact data_toList_emitVal rfl acc v
  | .bytesN _, acc, v => by rw [emitAny]; exact data_toList_emitVal rfl acc v
  | .bytes, acc, ⟨bs, h⟩ => by
      rw [emitAny, data_toList_emitPayload, toList_putBA_bytes ⟨bs, h⟩]
  | .string, acc, ⟨s, h⟩ => by
      rw [emitAny, data_toList_emitPayload, toList_putBA_string ⟨s, h⟩]
  | .array t, acc, ⟨vs, h⟩ => by
      rw [emitAny]
      by_cases hst : t.isStatic
      · rw [if_pos hst, data_toList_emitVals hst, data_toList_emitUintWord]
        rw [putBA_array vs h, Builder.toList_append, toList_putUint, toList_putParts_static hst,
          List.append_assoc]
      · have hst' : t.isStatic = false := by simpa using hst
        rw [if_neg hst]
        have hch : (sizesOf (.array t) ⟨vs, h⟩).children = sizesOfList t vs := by
          rw [sizesOf, if_neg hst]
        rw [hch, data_toList_emitAnyTails t hst', data_toList_emitOffsets t hst',
          data_toList_emitUintWord]
        rw [putBA_array vs h, Builder.toList_append, toList_putUint, putParts, Builder.toList_append,
          headSizes_dynamic hst']
        simp only [List.append_assoc]
  | .fixedArray t n hn, acc, ⟨vs, h⟩ => by
      rw [emitAny]
      by_cases hst : t.isStatic
      · rw [if_pos hst, data_toList_emitVals hst]
        rw [putBA_fixedArray hn vs h, toList_putParts_static hst]
      · have hst' : t.isStatic = false := by simpa using hst
        rw [if_neg hst]
        have hch : (sizesOf (.fixedArray t n hn) ⟨vs, h⟩).children = sizesOfList t vs := by
          rw [sizesOf, if_neg hst]
        rw [hch, data_toList_emitAnyTails t hst', data_toList_emitOffsets t hst']
        rw [putBA_fixedArray hn vs h, putParts, Builder.toList_append, headSizes_dynamic hst']
        simp only [List.append_assoc]
  | .tuple head tail, acc, (v, vs) => by
      rw [emitAny]
      have hch : (sizesOf (.tuple head tail) (v, vs)).children = sizesOfTuple (head :: tail) (v, vs) := by
        rw [sizesOf]
        simp [sizesOfTuple]
      rw [hch, data_toList_emitAnyTupleTails, data_toList_emitTupleHeads,
        tupleBase_eq]
      rw [putBA_tuple v vs, putParts, Builder.toList_append]
      simp only [List.append_assoc]
termination_by t _ _ => (tyMeasure t, 0)

theorem data_toList_emitAnyTails :
    ∀ (t : Ty), t.isStatic = false → ∀ (acc : ByteArray) (vs : List (ValBA t)),
      (emitAnyTails t acc vs (sizesOfList t vs)).data.toList
        = acc.data.toList ++ (putTails (vs.map (partOfBA t))).toList
  | t, hst, acc, [] => by rw [sizesOfList]; simp [emitAnyTails, putTails]
  | t, hst, acc, v :: vs => by
      rw [sizesOfList, emitAnyTails, data_toList_emitAnyTails t hst _ vs,
        data_toList_emitAny acc v]
      simp only [List.map_cons, partOfBA, hst, putTails, Builder.toList_append,
        List.append_assoc]
termination_by t _ _ vs => (tyMeasure t, 1 + vs.length)

theorem data_toList_emitAnyTupleTails :
    ∀ {ts : List Ty} (acc : ByteArray) (vs : TupleValBA ts),
      (emitAnyTupleTails acc ts vs (sizesOfTuple ts vs)).data.toList
        = acc.data.toList ++ (putTails (partsOfTupleBA ts vs)).toList
  | [], acc, _ => by rw [sizesOfTuple]; simp [emitAnyTupleTails, partsOfTupleBA, putTails]
  | t :: ts, acc, (v, vs) => by
      rw [sizesOfTuple, emitAnyTupleTails]
      by_cases hst : t.isStatic
      · rw [if_pos hst, data_toList_emitAnyTupleTails acc vs]
        simp only [partsOfTupleBA, partOfBA, hst, putTails]
      · have hst' : t.isStatic = false := by simpa using hst
        rw [if_neg hst, data_toList_emitAnyTupleTails _ vs, data_toList_emitAny acc v]
        simp only [partsOfTupleBA, partOfBA, hst', putTails, Builder.toList_append,
          List.append_assoc]
termination_by ts _ _ => (tyListMeasure ts, 1)
end

/-- `encode` with the static, `bytes[]` and `string[]` arms fused and
everything else through the size tree (the swap the compiler acts on; every
theorem stays stated over `encode`). -/
def encodeFast (t : Ty) (v : ValBA t) : ByteArray :=
  match t, v with
  | .array .bytes, v =>
      emitDynTails (fun u : ValBA .bytes => u.val)
        (emitDynHeads (fun u : ValBA .bytes => u.val.size)
          (emitUintWord
            (ByteArray.emptyWithCapacity
              (v.val.foldl (fun s u => s + 32 + dynTailSize u.val.size) 32)) v.val.length)
          (32 * v.val.length) v.val)
        v.val
  | .array .string, v =>
      emitDynTails (fun u : ValBA .string => u.val.toUTF8)
        (emitDynHeads (fun u : ValBA .string => u.val.utf8ByteSize)
          (emitUintWord
            (ByteArray.emptyWithCapacity
              (v.val.foldl (fun s u => s + 32 + dynTailSize u.val.utf8ByteSize) 32))
            v.val.length)
          (32 * v.val.length) v.val)
        v.val
  -- static elements: the total is known without a size tree, and the element
  -- loop is fused so the per-element `Ty` match disappears
  | .array (.uint m), v =>
      emitValsWith (emitPrim (.uint m)) (staticElemsHead v.val.length) v.val
  | .array (.int m), v =>
      emitValsWith (emitPrim (.int m)) (staticElemsHead v.val.length) v.val
  | .array .bool, v =>
      emitValsWith (emitPrim .bool) (staticElemsHead v.val.length) v.val
  | .array (.bytesN m), v =>
      emitValsWith (emitPrim (.bytesN m)) (staticElemsHead v.val.length) v.val
  | t, v =>
      if t.isStatic then emitVal (ByteArray.emptyWithCapacity (staticSize t)) t v
      else emitAnyRun t v

/-- A static value's whole encoding is its head, so it streams through
`emitVal` — a struct of words costs no `SizeT` per component. -/
private theorem encode_static_arm {t : Ty} (v : ValBA t) (ht : t.isStatic = true) :
    encode t v = emitVal (ByteArray.emptyWithCapacity (staticSize t)) t v := by
  apply ByteArray.data_inj
  rw [← Array.toList_inj]
  rw [encode, Builder.data_toList_run, data_toList_emitVal ht, toList_emptyWithCapacity,
    List.nil_append]

/-- Any value at all: `encode` is the size pass plus the one write pass. -/
private theorem encode_emitAny (t : Ty) (v : ValBA t) :
    encode t v = emitAnyRun t v := by
  apply ByteArray.data_inj
  rw [← Array.toList_inj, encode, Builder.data_toList_run]
  show _ = (emitAny (ByteArray.emptyWithCapacity (sizesOf t v).total) t v
    (sizesOf t v)).data.toList
  rw [data_toList_emitAny, toList_emptyWithCapacity, List.nil_append]

/-- The catch-all arm, at any type. -/
private theorem encode_nonarray_arm (t : Ty) (v : ValBA t) :
    encode t v
      = if t.isStatic then emitVal (ByteArray.emptyWithCapacity (staticSize t)) t v
        else emitAnyRun t v := by
  by_cases ht : t.isStatic
  · rw [if_pos ht]
    exact encode_static_arm v ht
  · rw [if_neg ht]
    exact encode_emitAny t v

/-- The streaming array arm, at either payload type. -/
private theorem encode_dyn_array_arm {t : Ty} (hd : t.isStatic = false)
    {sizeF : ValBA t → Nat} {payloadF : ValBA t → ByteArray}
    (hsize : ∀ v : ValBA t, (putBA t v).size = dynTailSize (sizeF v))
    (hput : ∀ v : ValBA t, (putBA t v).toList = encodeBytes (payloadF v).data.toList)
    (vs : List (ValBA t)) (h : vs.length < 2 ^ 64) (cap : Nat) :
    encode (.array t) ⟨vs, h⟩
      = emitDynTails payloadF
          (emitDynHeads sizeF (emitUintWord (ByteArray.emptyWithCapacity cap) vs.length)
            (32 * vs.length) vs) vs := by
  apply ByteArray.data_inj
  rw [← Array.toList_inj, encode, Builder.data_toList_run]
  rw [putBA_array vs h, Builder.toList_append, toList_putUint, putParts, Builder.toList_append,
    headSizes_dynamic hd, data_toList_emitDynTails hd hput,
    data_toList_emitDynHeads hd hsize, data_toList_emitUintWord,
    toList_emptyWithCapacity, List.nil_append]
  simp only [List.append_assoc]

/-- A static-element array needs no size tree: its total is the length word plus
`n` element slots, and the element run is `emitVals` at the element type. -/
private theorem encode_static_elem_array {t : Ty} (hst : t.isStatic = true)
    (v : ValBA (.array t)) :
    encode (.array t) v
      = emitVals (emitUintWord
          (ByteArray.emptyWithCapacity (32 + v.val.length * staticSize t)) v.val.length)
          t v.val := by
  obtain ⟨vs, hvs⟩ := v
  rw [encode_nonarray_arm, if_neg (by simp [Ty.isStatic]), emitAnyRun, sizesOf, if_pos hst,
    emitAny, if_pos hst]

/-- Each fused arm, given that the element type is static and occupies one
word, and that its specialized step is `emitVal` there. -/
private theorem encode_fused_arm {t : Ty} (write : ByteArray → ValBA t → ByteArray)
    (hst : t.isStatic = true) (hsz : staticSize t = 32)
    (hwrite : ∀ acc v, write acc v = emitVal acc t v) (v : ValBA (.array t)) :
    encode (.array t) v
      = emitValsWith write (staticElemsHead v.val.length) v.val := by
  rw [encode_static_elem_array hst v]
  exact (emitVals_eq_with hwrite _ _).trans
    (by rw [hsz, staticElemsHead, Nat.mul_comm])

@[csimp] theorem encode_eq_fast : @encode = @encodeFast := by
  funext t v
  match t, v with
  | .array .bytes, ⟨vs, h⟩ =>
      exact encode_dyn_array_arm rfl size_putBA_bytes toList_putBA_bytes vs h _
  | .array .string, ⟨vs, h⟩ =>
      exact encode_dyn_array_arm rfl size_putBA_string toList_putBA_string vs h _
  | .array (.uint m), v =>
      exact encode_fused_arm (emitPrim (.uint m)) rfl (by simp [staticSize]) (by simp [emitVal]) v
  | .array (.int m), v =>
      exact encode_fused_arm (emitPrim (.int m)) rfl (by simp [staticSize]) (by simp [emitVal]) v
  | .array .bool, v =>
      exact encode_fused_arm (emitPrim .bool) rfl (by simp [staticSize]) (by simp [emitVal]) v
  | .array (.bytesN m), v =>
      exact encode_fused_arm (emitPrim (.bytesN m)) rfl (by simp [staticSize]) (by simp [emitVal]) v
  | .uint _, v | .int _, v | .bool, v | .address, v | .bytesN _, v | .bytes, v | .string, v
  | .fixedArray _ _ _, v | .tuple _ _, v
  | .array .address, v | .array (.array _), v | .array (.fixedArray _ _ _), v
  | .array (.tuple _ _), v =>
      exact encode_nonarray_arm _ v
