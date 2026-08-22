import EvmAbi.Spec
import EvmAbi.Codec.ByteArray
import EvmAbi.ValBA

/-!
# EvmAbi.Codec

The runtime codec users run: `encode` (`ValBA` values into a `ByteArray`),
`decode` / `decodeStrict` (`ByteArray` into `ValBA` values), and
`IsCanonical`.  The list-based specification codec lives in
`EvmAbi.Spec`; every runtime definition here is paired with an agreement
lemma against it, so nothing is reproved.

The capstones at the end — `decodeStrict_encode`, `encode_of_decodeStrict`,
`decodeStrict_eq_some_iff`, `isCanonical_iff` — are the `Spec` capstones
stated of these names.  Agreement alone does not give them: it says what a
runtime answer *denotes*, while they are about the runtime value itself, so
the conclusion comes back up through `ValBA.toList_injective`.
-/

namespace EvmAbi.Codec

open Ty
open Binary
open Builder
open EvmAbi.Codec.ByteArray

/-! ## the runtime encoder -/

/-- Write dynamic `bytes` from a packed payload: the length word (its size
is cached — no list walk), the payload as a `chunk`, and the padding as a
`zeros` run. -/
def putBytesBA (bs : ByteArray) : Builder :=
  Builder.appendZeros (putUint bs.size ++ Builder.chunk bs) ((32 - bs.size % 32) % 32)

@[simp] theorem toList_putBytesBA (bs : ByteArray) :
    (putBytesBA bs).toList = encodeBytes bs.data.toList := by
  simp [putBytesBA, encodeBytes, pad32, List.append_assoc]

/-- Write fixed-size `bytesN` from a packed payload. -/
def putBytesNBA (bs : ByteArray) : Builder :=
  Builder.appendZeros (Builder.chunk bs) (32 - bs.size)

@[simp] theorem toList_putBytesNBA (bs : ByteArray) :
    (putBytesNBA bs).toList = encodeBytesN bs.data.toList := by
  simp [putBytesNBA, encodeBytesN]

mutual
/-- ABI encoder over packed values: same layout as `Spec.put`, `chunk`
leaves for the payloads. -/
def putBA : (t : Ty) → ValBA t → Builder
  | .uint _, ⟨w, _⟩ => putWord w
  | .int _, ⟨i, _⟩ => putInt i
  | .bool, b => putBool b
  | .address, ⟨n, _⟩ => putAddress n
  | .bytesN _, ⟨bs, _⟩ => putBytesNBA bs
  | .bytes, ⟨bs, _⟩ => putBytesBA bs
  | .string, ⟨s, _⟩ => putString s
  | .array t, ⟨vs, _⟩ => putUint vs.length ++ putParts (vs.map (partOfBA t))
  | .fixedArray t _, ⟨vs, _⟩ => putParts (vs.map (partOfBA t))
  | .tuple ts, vs => putParts (partsOfTupleBA ts vs)
termination_by t => (sizeOf t, 0)

/-- A packed value seen as a head/tail part. -/
def partOfBA (t : Ty) (v : ValBA t) : Part :=
  match t.isStatic with
  | true => ⟨putBA t v, ∅, false⟩
  | false => ⟨∅, putBA t v, true⟩
termination_by (sizeOf t, 1)

/-- A packed tuple value seen as a list of parts. -/
def partsOfTupleBA : (ts : List Ty) → TupleValBA ts → List Part
  | [], _ => []
  | t :: ts, (v, vs) => partOfBA t v :: partsOfTupleBA ts vs
termination_by ts => (sizeOf ts, 2)
end

/-! ## the runtime encoder agrees with the spec encoder -/

/-- Pointwise equivalence of two part lists. -/
def PartsEquivalent : List Part → List Part → Prop
  | [], [] => True
  | p :: ps, q :: qs => Part.Equiv p q ∧ PartsEquivalent ps qs
  | _, _ => False

/-- Equivalent part lists have equal head sections. -/
theorem headSizes_eq_of_equiv : ∀ {ps ps' : List Part},
    PartsEquivalent ps ps' → headSizes ps = headSizes ps'
  | [], [], _ => rfl
  | p :: ps, q :: qs, h => by
      obtain ⟨hd, htl⟩ := h
      have hh : Part.headSize p = Part.headSize q := Part.headSize_eq_of_equiv hd
      simp [headSizes, hh, headSizes_eq_of_equiv htl]

/-- Equivalent part lists have equal tail sections. -/
theorem tailSizes_eq_of_equiv : ∀ {ps ps' : List Part},
    PartsEquivalent ps ps' → tailSizes ps = tailSizes ps'
  | [], [], _ => rfl
  | p :: ps, q :: qs, h => by
      obtain ⟨hd, htl⟩ := h
      have hh : Part.tailSize p = Part.tailSize q := Part.tailSize_eq_of_equiv hd
      simp [tailSizes, hh, tailSizes_eq_of_equiv htl]

/-- Equivalent part lists have equal head encodings. -/
theorem encodeHeads_eq_of_equiv (acc : Nat) : ∀ {ps ps' : List Part},
    PartsEquivalent ps ps' → encodeHeads acc ps = encodeHeads acc ps'
  | [], [], _ => rfl
  | p :: ps, q :: qs, h => by
      rcases h with ⟨hd, htl⟩
      rcases hd with ⟨hdyn, hhead, htail, hs1, hs2⟩
      cases p with
      | mk ph pt pd =>
        cases q with
        | mk qh qt qd =>
          cases pd with
          | false =>
            cases qd with
            | false =>
                rw [encodeHeads_cons_static, encodeHeads_cons_static]
                rw [hhead]
                rw [encodeHeads_eq_of_equiv acc htl]
            | true => exact False.elim (Bool.noConfusion hdyn)
          | true =>
            cases qd with
            | false => exact False.elim (Bool.noConfusion hdyn)
            | true =>
                rw [encodeHeads_cons_dynamic, encodeHeads_cons_dynamic]
                have hlen : pt.toList.length = qt.toList.length := congrArg List.length htail
                rw [hlen]
                rw [encodeHeads_eq_of_equiv (acc + qt.toList.length) htl]

/-- Equivalent part lists have equal tail encodings. -/
theorem encodeTails_eq_of_equiv : ∀ {ps ps' : List Part},
    PartsEquivalent ps ps' → encodeTails ps = encodeTails ps'
  | [], [], _ => rfl
  | p :: ps, q :: qs, h => by
      rcases h with ⟨hd, htl⟩
      rcases hd with ⟨hdyn, hhead, htail, hs1, hs2⟩
      cases p with
      | mk ph pt pd =>
        cases q with
        | mk qh qt qd =>
          cases pd with
          | false =>
            cases qd with
            | false =>
                rw [encodeTails_cons_static, encodeTails_cons_static]
                exact encodeTails_eq_of_equiv htl
            | true => exact False.elim (Bool.noConfusion hdyn)
          | true =>
            cases qd with
            | false => exact False.elim (Bool.noConfusion hdyn)
            | true =>
                rw [encodeTails_cons_dynamic, encodeTails_cons_dynamic]
                rw [htail]
                rw [encodeTails_eq_of_equiv htl]

/-- Equivalent part lists have equal full encodings. -/
theorem encodeParts_eq_of_equiv : ∀ {ps ps' : List Part},
    PartsEquivalent ps ps' → encodeParts ps = encodeParts ps'
  | [], [], _ => rfl
  | p :: ps, q :: qs, h => by
      rcases h with ⟨hd, htl⟩
      rcases hd with ⟨hdyn, hhead, htail, hs1, hs2⟩
      cases p with
      | mk ph pt pd =>
        cases q with
        | mk qh qt qd =>
          cases pd with
          | false =>
            cases qd with
            | false =>
                rw [encodeParts_unfold, encodeParts_unfold]
                rw [encodeHeads_cons_static, encodeHeads_cons_static]
                rw [encodeTails_cons_static, encodeTails_cons_static]
                have hh : Part.headSize (Part.mk ph pt false) =
                    Part.headSize (Part.mk qh qt false) := by
                  change ph.size = qh.size
                  exact hs1
                have hhs : headSizes (Part.mk ph pt false :: ps) =
                    headSizes (Part.mk qh qt false :: qs) := by
                  simp [headSizes, hh, headSizes_eq_of_equiv htl]
                rw [hhs, hhead]
                rw [encodeHeads_eq_of_equiv _ htl, encodeTails_eq_of_equiv htl]
            | true => exact False.elim (Bool.noConfusion hdyn)
          | true =>
            cases qd with
            | false => exact False.elim (Bool.noConfusion hdyn)
            | true =>
                rw [encodeParts_unfold, encodeParts_unfold]
                rw [encodeHeads_cons_dynamic, encodeHeads_cons_dynamic]
                rw [encodeTails_cons_dynamic, encodeTails_cons_dynamic]
                have hhs : headSizes (Part.mk ph pt true :: ps) =
                    headSizes (Part.mk qh qt true :: qs) := by
                  simp [headSizes, Part.headSize, headSizes_eq_of_equiv htl]
                have hlen : pt.toList.length = qt.toList.length := congrArg List.length htail
                rw [hhs, hlen, htail]
                rw [encodeHeads_eq_of_equiv _ htl, encodeTails_eq_of_equiv htl]

/-- The runtime part of a value denotes the spec part of its denotation,
given the runtime encoder agrees with the spec encoder on that value. -/
theorem partOfBA_toList (t : Ty) (v : ValBA t)
    (h : (putBA t v).toList = Spec.encode t (ValBA.toList t v)) :
    Part.Equiv (partOfBA t v) (Spec.partOf t (ValBA.toList t v)) := by
  cases hs : t.isStatic
  · have hba : partOfBA t v = ⟨∅, putBA t v, true⟩ := by simp [partOfBA, hs]
    have hsp : Spec.partOf t (ValBA.toList t v) =
        ⟨∅, Spec.put t (ValBA.toList t v), true⟩ := by
      rw [Spec.partOf_dynamic t (ValBA.toList t v) hs]
    rw [hba, hsp]
    simp [Part.Equiv, h, Builder.size_eq_length_toList, Spec.encode]
  · have hba : partOfBA t v = ⟨putBA t v, ∅, false⟩ := by simp [partOfBA, hs]
    have hsp : Spec.partOf t (ValBA.toList t v) =
        ⟨Spec.put t (ValBA.toList t v), ∅, false⟩ := by
      rw [Spec.partOf_static t (ValBA.toList t v) hs]
    rw [hba, hsp]
    simp [Part.Equiv, h, Builder.size_eq_length_toList, Spec.encode]

mutual
/-- The runtime encoder denotes the spec encoder of the same value. -/
theorem toList_putBA (t : Ty) (v : ValBA t) :
    (putBA t v).toList = Spec.encode t (ValBA.toList t v) := by
  cases t with
  | uint m =>
      obtain ⟨w, hw⟩ := v
      rw [putBA.eq_1, ValBA.toList.eq_1, Spec.encode, Spec.put.eq_1,
        toList_putWord, toList_putUint, encodeUint, Binary.UInt256.ofNat_toNat]
  | int m =>
      obtain ⟨i, hi⟩ := v
      rw [putBA.eq_2, ValBA.toList.eq_2, Spec.encode, Spec.put.eq_2]
  | bool =>
      rw [putBA.eq_3, ValBA.toList.eq_3, Spec.encode, Spec.put.eq_3]
  | address =>
      obtain ⟨n, hn⟩ := v
      rw [putBA.eq_4, ValBA.toList.eq_4, Spec.encode, Spec.put.eq_4]
  | bytesN m =>
      obtain ⟨bs, hbs⟩ := v
      rw [putBA.eq_5, ValBA.toList.eq_5, Spec.encode, Spec.put.eq_5]
      rw [toList_putBytesNBA, toList_putBytesN]
  | bytes =>
      obtain ⟨bs, hbs⟩ := v
      rw [putBA.eq_6, ValBA.toList.eq_6, Spec.encode, Spec.put.eq_6]
      rw [toList_putBytesBA, toList_putBytes]
  | string =>
      obtain ⟨s, hs⟩ := v
      rw [putBA.eq_7, ValBA.toList.eq_7, Spec.encode, Spec.put.eq_7]
  | array t =>
      obtain ⟨vs, hvs⟩ := v
      rw [putBA.eq_8, ValBA.toList.eq_8, Spec.encode, Spec.put.eq_8]
      rw [List.length_map]
      simp only [Builder.toList_append, toList_putUint]
      change encodeUint vs.length ++ encodeParts (vs.map (partOfBA t)) =
        encodeUint vs.length ++
          encodeParts ((vs.map (ValBA.toList t)).map (Spec.partOf t))
      exact congrArg (fun l => encodeUint vs.length ++ l)
        (encodeParts_eq_of_equiv (ps := vs.map (partOfBA t))
          (ps' := (vs.map (ValBA.toList t)).map (Spec.partOf t)) (by
            clear hvs
            induction vs with
            | nil => trivial
            | cons v vs ih =>
                unfold PartsEquivalent
                constructor
                · exact partOfBA_toList t v (toList_putBA t v)
                · exact ih))
  | fixedArray t n =>
      obtain ⟨vs, hvs⟩ := v
      rw [putBA.eq_9, ValBA.toList.eq_9, Spec.encode, Spec.put.eq_9]
      change encodeParts (vs.map (partOfBA t)) =
        encodeParts ((vs.map (ValBA.toList t)).map (Spec.partOf t))
      exact encodeParts_eq_of_equiv (ps := vs.map (partOfBA t))
        (ps' := (vs.map (ValBA.toList t)).map (Spec.partOf t)) (by
          clear hvs
          induction vs with
          | nil => trivial
          | cons v vs ih =>
              unfold PartsEquivalent
              constructor
              · exact partOfBA_toList t v (toList_putBA t v)
              · exact ih)
  | tuple ts =>
      rw [putBA.eq_10, ValBA.toList.eq_10, Spec.encode, Spec.put.eq_10]
      change encodeParts (partsOfTupleBA ts v) =
        encodeParts (Spec.partsOfTuple ts (TupleValBA.toList ts v))
      exact encodeParts_eq_of_equiv (partsOfTupleBA_equiv ts v)
termination_by sizeOf t

/-- The runtime tuple parts denote the spec tuple parts. -/
theorem partsOfTupleBA_equiv : ∀ (ts : List Ty) (vs : TupleValBA ts),
    PartsEquivalent (partsOfTupleBA ts vs) (Spec.partsOfTuple ts (TupleValBA.toList ts vs))
  | [], vs => by cases vs; rw [partsOfTupleBA.eq_1, Spec.partsOfTuple.eq_1]; trivial
  | t :: ts, (v, vs) => by
      rw [partsOfTupleBA.eq_2, Spec.partsOfTuple.eq_2, TupleValBA.toList_cons]
      constructor
      · exact partOfBA_toList t v (toList_putBA t v)
      · exact partsOfTupleBA_equiv ts vs
termination_by ts => sizeOf ts
end

/-- **Runtime ABI encoder**: the efficient path users run — `ValBA`
values, `ByteArray` output, one builder pass. -/
def encode (t : Ty) (v : ValBA t) : ByteArray := (putBA t v).run

/-- The runtime encoder denotes the spec encoder of the same value. -/
@[simp] theorem data_toList_encode (t : Ty) (v : ValBA t) :
    (encode t v).data.toList = Spec.encode t (ValBA.toList t v) := by
  rw [encode, Builder.data_toList_run]
  exact toList_putBA t v

/-- …equivalently, the runtime encoder is the spec encoding packed into a
`ByteArray`. -/
theorem encode_eq (t : Ty) (v : ValBA t) :
    encode t v = (Spec.encode t (ValBA.toList t v)).toByteArray := by
  rw [encode, Builder.run_eq_toByteArray]
  rw [toList_putBA t v]

@[simp] theorem size_encode (t : Ty) (v : ValBA t) :
    (encode t v).size = (Spec.encode t (ValBA.toList t v)).length := by
  rw [encode, Builder.size_run, Builder.size_eq_length_toList]
  rw [toList_putBA t v]

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
def tupleEncodings : (ts : List Ty) → TupleValBA ts → List UInt8
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

mutual
/-- Write one static value straight into the accumulator: words by their
limbs, `bytesN` payloads by one append and one padding copy (skipped when
the payload fills its word, which is every element of a `bytes32[]`), and
static compounds by concatenation.  Dynamic types return `acc` untouched —
`data_toList_emitVal` is guarded by `isStatic`, and the fused arm never
reaches them. -/
def emitVal (acc : ByteArray) : (t : Ty) → ValBA t → ByteArray
  | .uint _, ⟨w, _⟩ => Chunks.emitWord acc w
  | .int _, ⟨i, _⟩ =>
      emitUintWord acc (if 0 ≤ i then i.toNat else 2 ^ 256 - (-i).toNat)
  | .bool, b => emitUintWord acc (if b then 1 else 0)
  | .address, ⟨n, _⟩ => emitUintWord acc n
  | .bytesN _, ⟨bs, _⟩ =>
      if bs.size == 32 then acc ++ bs else Chunks.pushZeros32 (acc ++ bs) (32 - bs.size)
  | .fixedArray t _, ⟨vs, _⟩ => emitVals acc t vs
  | .tuple ts, vs => emitTupleVals acc ts vs
  | .bytes, _ => acc
  | .string, _ => acc
  | .array _, _ => acc
termination_by t _ => (sizeOf t, 0)

/-- `emitVal` each element in order. -/
def emitVals (acc : ByteArray) (t : Ty) : List (ValBA t) → ByteArray
  | [] => acc
  | v :: vs => emitVals (emitVal acc t v) t vs
termination_by vs => (sizeOf t, 1 + vs.length)

/-- `emitVal` each component in order. -/
def emitTupleVals (acc : ByteArray) : (ts : List Ty) → TupleValBA ts → ByteArray
  | [], _ => acc
  | t :: ts, (v, vs) => emitTupleVals (emitVal acc t v) ts vs
termination_by ts _ => (sizeOf ts, 0)
end

mutual
theorem data_toList_emitVal :
    ∀ {t : Ty}, t.isStatic = true → ∀ (acc : ByteArray) (v : ValBA t),
      (emitVal acc t v).data.toList = acc.data.toList ++ (putBA t v).toList
  | .uint _, ht, acc, ⟨w, hw⟩ => by
      rw [emitVal, Chunks.data_toList_emitWord, putBA, toList_putWord]
  | .int _, ht, acc, ⟨i, hi⟩ => by
      rw [emitVal, data_toList_emitUintWord, putBA]
      simp only [toList_putInt, encodeInt]
  | .bool, ht, acc, b => by
      rw [emitVal, data_toList_emitUintWord, putBA]
      simp only [toList_putBool, encodeBool]
  | .address, ht, acc, ⟨n, hn⟩ => by
      rw [emitVal, data_toList_emitUintWord, putBA]
      simp only [toList_putAddress, encodeAddress]
  | .bytesN _, ht, acc, ⟨bs, hbs⟩ => by
      rw [emitVal, putBA, toList_putBytesNBA]
      split
      · next hbeq =>
          have h32 : bs.size = 32 := by simpa using hbeq
          simp [encodeBytesN, h32]
      · next _ =>
          rw [Chunks.data_toList_pushZeros32 _ (by omega)]
          simp [encodeBytesN, List.append_assoc]
  | .fixedArray t _, ht, acc, ⟨vs, hvs⟩ => by
      have ht' : t.isStatic = true := ht
      rw [emitVal, putBA, toList_putParts_static ht', data_toList_emitVals ht']
  | .tuple ts, ht, acc, vs => by
      have ht' : Ty.allStatic ts = true := ht
      rw [emitVal, putBA, toList_putParts_tupleStatic ht', data_toList_emitTupleVals ht']
  | .bytes, ht, _, _ => Bool.noConfusion ht
  | .string, ht, _, _ => Bool.noConfusion ht
  | .array _, ht, _, _ => Bool.noConfusion ht
termination_by t => (sizeOf t, 0)

theorem data_toList_emitVals {t : Ty} (ht : t.isStatic = true) (acc : ByteArray) :
    ∀ (vs : List (ValBA t)),
      (emitVals acc t vs).data.toList
        = acc.data.toList ++ (vs.map fun v => (putBA t v).toList).flatten
  | [] => by simp [emitVals]
  | v :: vs => by
      rw [emitVals, data_toList_emitVals ht (emitVal acc t v) vs,
        data_toList_emitVal ht acc v, List.map_cons, List.flatten_cons, List.append_assoc]
termination_by vs => (sizeOf t, 1 + vs.length)

theorem data_toList_emitTupleVals :
    ∀ {ts : List Ty}, Ty.allStatic ts = true → ∀ (acc : ByteArray) (vs : TupleValBA ts),
      (emitTupleVals acc ts vs).data.toList = acc.data.toList ++ tupleEncodings ts vs
  | [], _, acc, _ => by simp [emitTupleVals, tupleEncodings]
  | t :: ts, ht, acc, (v, vs) => by
      obtain ⟨ht1, ht2⟩ : Ty.isStatic t = true ∧ Ty.allStatic ts = true := by
        simpa [Ty.allStatic] using ht
      rw [emitTupleVals, data_toList_emitTupleVals ht2 (emitVal acc t v) vs,
        data_toList_emitVal ht1 acc v, tupleEncodings, List.append_assoc]
termination_by ts => (sizeOf ts, 0)
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

/-! ### sizes

`sizeBA t v` is the byte count `putBA t v` runs to — the builder's
cached-size arithmetic replayed over the value, exact whether or not the
type is `Valid`. -/

private theorem size_append (a b : Builder) : (a ++ b).size = a.size + b.size := rfl

private theorem size_putUint (n : Nat) : (putUint n).size = 32 := by
  rw [Builder.size_eq_length_toList, toList_putUint, length_encodeUint]

private theorem size_putBytesNBA (bs : ByteArray) :
    (putBytesNBA bs).size = bs.size + (32 - bs.size) := by
  rw [Builder.size_eq_length_toList, toList_putBytesNBA]
  simp [encodeBytesN]

mutual
/-- The byte count `putBA t v` runs to. -/
def sizeBA : (t : Ty) → ValBA t → Nat
  | .uint _, _ => 32
  | .int _, _ => 32
  | .bool, _ => 32
  | .address, _ => 32
  | .bytesN _, ⟨bs, _⟩ => bs.size + (32 - bs.size)
  | .bytes, ⟨bs, _⟩ => dynTailSize bs.size
  | .string, ⟨s, _⟩ => dynTailSize s.utf8ByteSize
  | .array t, ⟨vs, _⟩ => 32 + sizeElems t vs
  | .fixedArray t _, ⟨vs, _⟩ => sizeElems t vs
  | .tuple ts, vs => sizeTuple ts vs
termination_by t _ => (sizeOf t, 0)

/-- Head plus tail bytes of an element run. -/
def sizeElems (t : Ty) : List (ValBA t) → Nat
  | [] => 0
  | v :: vs => (if t.isStatic then sizeBA t v else 32 + sizeBA t v) + sizeElems t vs
termination_by vs => (sizeOf t, 1 + vs.length)

/-- Head plus tail bytes of a component run. -/
def sizeTuple : (ts : List Ty) → TupleValBA ts → Nat
  | [], _ => 0
  | t :: ts, (v, vs) =>
      (if t.isStatic then sizeBA t v else 32 + sizeBA t v) + sizeTuple ts vs
termination_by ts _ => (sizeOf ts, 0)
end

mutual
theorem sizeBA_eq : ∀ (t : Ty) (v : ValBA t), sizeBA t v = (putBA t v).size
  | .uint _, ⟨w, _⟩ => by rw [sizeBA, putBA]; exact rfl
  | .int _, ⟨i, _⟩ => by rw [sizeBA, putBA]; exact (size_putUint _).symm
  | .bool, b => by rw [sizeBA, putBA]; exact (size_putUint _).symm
  | .address, ⟨n, _⟩ => by rw [sizeBA, putBA]; exact (size_putUint _).symm
  | .bytesN _, ⟨bs, _⟩ => by rw [sizeBA, putBA]; exact (size_putBytesNBA bs).symm
  | .bytes, ⟨bs, _⟩ => by rw [sizeBA, putBA]; exact (size_putBytesBA bs).symm
  | .string, ⟨s, _⟩ => by
      rw [sizeBA, putBA]
      show _ = (putBytesBA s.toUTF8).size
      rw [size_putBytesBA, toUTF8_size]
  | .array t, ⟨vs, _⟩ => by
      rw [sizeBA, putBA, size_append, size_putUint, size_parts_elems t vs]
  | .fixedArray t _, ⟨vs, _⟩ => by
      rw [sizeBA, putBA, size_parts_elems t vs]
  | .tuple ts, vs => by
      rw [sizeBA, putBA, size_parts_tuple ts vs]
termination_by t _ => (sizeOf t, 0)

theorem size_parts_elems : ∀ (t : Ty) (vs : List (ValBA t)),
    (putParts (vs.map (partOfBA t))).size = sizeElems t vs
  | t, vs => by
      rw [putParts, size_append, heads_tails_elems t vs (headSizes (vs.map (partOfBA t)))]
termination_by t vs => (sizeOf t, 2 + vs.length)

theorem heads_tails_elems : ∀ (t : Ty) (vs : List (ValBA t)) (acc : Nat),
    (putHeads acc (vs.map (partOfBA t))).size + (putTails (vs.map (partOfBA t))).size
      = sizeElems t vs
  | t, [], acc => by simp [putHeads, putTails, sizeElems]
  | t, v :: vs, acc => by
      rw [sizeElems]
      by_cases hst : t.isStatic
      · rw [if_pos hst]
        simp only [List.map_cons, partOfBA, hst, putHeads, putTails, size_append]
        rw [← sizeBA_eq t v, ← heads_tails_elems t vs acc]
        omega
      · rw [if_neg hst]
        have hst' : t.isStatic = false := by simpa using hst
        simp only [List.map_cons, partOfBA, hst', putHeads, putTails, size_append,
          size_putUint]
        rw [← sizeBA_eq t v, ← heads_tails_elems t vs (acc + (putBA t v).size)]
        rw [sizeBA_eq t v]
        omega
termination_by t vs _ => (sizeOf t, 1 + vs.length)

theorem size_parts_tuple : ∀ (ts : List Ty) (vs : TupleValBA ts),
    (putParts (partsOfTupleBA ts vs)).size = sizeTuple ts vs
  | ts, vs => by
      rw [putParts, size_append, heads_tails_tuple ts vs (headSizes (partsOfTupleBA ts vs))]
termination_by ts _ => (sizeOf ts, 2)

theorem heads_tails_tuple : ∀ (ts : List Ty) (vs : TupleValBA ts) (acc : Nat),
    (putHeads acc (partsOfTupleBA ts vs)).size + (putTails (partsOfTupleBA ts vs)).size
      = sizeTuple ts vs
  | [], _, acc => by rw [partsOfTupleBA, sizeTuple]; simp [putHeads, putTails]
  | t :: ts, (v, vs), acc => by
      rw [partsOfTupleBA, sizeTuple]
      by_cases hst : t.isStatic
      · rw [if_pos hst]
        simp only [partOfBA, hst, putHeads, putTails, size_append]
        rw [← sizeBA_eq t v, ← heads_tails_tuple ts vs acc]
        omega
      · rw [if_neg hst]
        have hst' : t.isStatic = false := by simpa using hst
        simp only [partOfBA, hst', putHeads, putTails, size_append, size_putUint]
        rw [← sizeBA_eq t v, ← heads_tails_tuple ts vs (acc + (putBA t v).size)]
        rw [sizeBA_eq t v]
        omega
termination_by ts _ _ => (sizeOf ts, 1)
end

/-! ### static sizes

A static value's size is fixed by its type, so the arms that write one size
their buffer from `staticSize` and skip the size pass entirely.  It is
`Ty.headSize` except at `bytesN m` with `m > 32`, where the payload is `m`
bytes rather than one word — using `headSize` there would under-allocate. -/

mutual
/-- Encoded bytes of a static type, from the type alone. -/
def staticSize : Ty → Nat
  | .bytesN m => m + (32 - m)
  | .fixedArray t n => n * staticSize t
  | .tuple ts => staticSizeSum ts
  | .uint _ | .int _ | .bool | .address | .bytes | .string | .array _ => 32
termination_by t => sizeOf t

/-- Encoded bytes of a static component list. -/
def staticSizeSum : List Ty → Nat
  | [] => 0
  | t :: ts => staticSize t + staticSizeSum ts
termination_by ts => sizeOf ts
end

mutual
theorem sizeBA_static : ∀ {t : Ty}, t.isStatic = true → ∀ v : ValBA t,
    sizeBA t v = staticSize t
  | .uint _, _, ⟨_, _⟩ => by rw [sizeBA, staticSize]
  | .int _, _, ⟨_, _⟩ => by rw [sizeBA, staticSize]
  | .bool, _, _ => by rw [sizeBA, staticSize]
  | .address, _, ⟨_, _⟩ => by rw [sizeBA, staticSize]
  | .bytesN m, _, ⟨bs, hbs⟩ => by rw [sizeBA, staticSize, hbs]
  | .fixedArray t n, ht, ⟨vs, hvs⟩ => by
      rw [sizeBA, staticSize, sizeElems_static (t := t) ht vs, hvs]
  | .tuple ts, ht, vs => by rw [sizeBA, staticSize, sizeTuple_static (ts := ts) ht vs]
  | .bytes, ht, _ => Bool.noConfusion ht
  | .string, ht, _ => Bool.noConfusion ht
  | .array _, ht, _ => Bool.noConfusion ht
termination_by t _ _ => (sizeOf t, 0)

theorem sizeElems_static : ∀ {t : Ty}, t.isStatic = true → ∀ vs : List (ValBA t),
    sizeElems t vs = vs.length * staticSize t
  | t, ht, [] => by rw [sizeElems]; simp
  | t, ht, v :: vs => by
      rw [sizeElems, if_pos ht, sizeBA_static ht v, sizeElems_static ht vs]
      simp [Nat.succ_mul, Nat.add_comm]
termination_by t _ vs => (sizeOf t, 1 + vs.length)

theorem sizeTuple_static : ∀ {ts : List Ty}, Ty.allStatic ts = true →
    ∀ vs : TupleValBA ts, sizeTuple ts vs = staticSizeSum ts
  | [], _, _ => by rw [sizeTuple, staticSizeSum]
  | t :: ts, ht, (v, vs) => by
      obtain ⟨h1, h2⟩ : Ty.isStatic t = true ∧ Ty.allStatic ts = true := by
        simpa [Ty.allStatic] using ht
      rw [sizeTuple, if_pos h1, sizeBA_static h1 v, sizeTuple_static h2 vs, staticSizeSum]
termination_by ts _ _ => (sizeOf ts, 1)
end

/-! ### the size tree

Calling `sizeBA` per head slot would re-walk each subtree once per ancestor
— measured 51 → 372 µs/op on `nest 200`.  `sizesOf` instead computes every
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
      if t.isStatic then .mk (32 + sizeElems t vs) []
      else
        let cs := sizesOfList t vs
        .mk (32 + sumDyn cs) cs
  | .fixedArray t _, ⟨vs, _⟩ =>
      if t.isStatic then .mk (sizeElems t vs) []
      else
        let cs := sizesOfList t vs
        .mk (sumDyn cs) cs
  | .tuple ts, vs =>
      let cs := sizesOfTuple ts vs
      .mk (sumTuple ts cs) cs
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
theorem total_sizesOf : ∀ (t : Ty) (v : ValBA t), (sizesOf t v).total = sizeBA t v
  | .uint _, ⟨_, _⟩ => by rw [sizesOf, sizeBA]
  | .int _, ⟨_, _⟩ => by rw [sizesOf, sizeBA]
  | .bool, _ => by rw [sizesOf, sizeBA]
  | .address, ⟨_, _⟩ => by rw [sizesOf, sizeBA]
  | .bytesN _, ⟨_, _⟩ => by rw [sizesOf, sizeBA]
  | .bytes, ⟨_, _⟩ => by rw [sizesOf, sizeBA]
  | .string, ⟨_, _⟩ => by rw [sizesOf, sizeBA]
  | .array t, ⟨vs, h⟩ => by
      rw [sizesOf, sizeBA]
      by_cases hst : t.isStatic
      · rw [if_pos hst]
      · rw [if_neg hst]
        have hst' : t.isStatic = false := by simpa using hst
        show 32 + sumDyn (sizesOfList t vs) = 32 + sizeElems t vs
        rw [sumDyn_sizesOfList t hst' vs]
  | .fixedArray t _, ⟨vs, h⟩ => by
      rw [sizesOf, sizeBA]
      by_cases hst : t.isStatic
      · rw [if_pos hst]
      · rw [if_neg hst]
        have hst' : t.isStatic = false := by simpa using hst
        show sumDyn (sizesOfList t vs) = sizeElems t vs
        rw [sumDyn_sizesOfList t hst' vs]
  | .tuple ts, vs => by
      rw [sizesOf, sizeBA]
      show sumTuple ts (sizesOfTuple ts vs) = sizeTuple ts vs
      rw [sumTuple_sizesOfTuple ts vs]
termination_by t _ => (sizeOf t, 0)

theorem sumDyn_sizesOfList : ∀ (t : Ty), t.isStatic = false → ∀ (vs : List (ValBA t)),
    sumDyn (sizesOfList t vs) = sizeElems t vs
  | t, hst, [] => by rw [sizesOfList, sizeElems]; rfl
  | t, hst, v :: vs => by
      rw [sizesOfList, sizeElems, if_neg (by simp [hst] : ¬t.isStatic = true), sumDyn,
        total_sizesOf t v, sumDyn_sizesOfList t hst vs]
termination_by t _ vs => (sizeOf t, 1 + vs.length)

theorem sumTuple_sizesOfTuple : ∀ (ts : List Ty) (vs : TupleValBA ts),
    sumTuple ts (sizesOfTuple ts vs) = sizeTuple ts vs
  | [], _ => by rw [sizesOfTuple, sizeTuple]; rfl
  | t :: ts, (v, vs) => by
      rw [sizesOfTuple, sizeTuple, sumTuple, total_sizesOf t v,
        sumTuple_sizesOfTuple ts vs]
termination_by ts _ => (sizeOf ts, 1)
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
  | .fixedArray t _, v, st =>
      if t.isStatic then emitVals acc t v.val
      else emitAnyTails t (emitOffsets acc (32 * v.val.length) st.children) v.val st.children
  | .tuple ts, vs, st =>
      emitAnyTupleTails
        (emitTupleHeads acc (tupleBase ts st.children) ts vs st.children) ts vs st.children
  | .uint m, v, _ => emitVal acc (.uint m) v
  | .int m, v, _ => emitVal acc (.int m) v
  | .bool, v, _ => emitVal acc .bool v
  | .address, v, _ => emitVal acc .address v
  | .bytesN m, v, _ => emitVal acc (.bytesN m) v
termination_by t _ _ => (sizeOf t, 0)

/-- Append the tails of a dynamic-element run. -/
def emitAnyTails (t : Ty) (acc : ByteArray) : List (ValBA t) → List SizeT → ByteArray
  | [], _ => acc
  | _ :: _, [] => acc
  | v :: vs, c :: cs => emitAnyTails t (emitAny acc t v c) vs cs
termination_by vs _ => (sizeOf t, 1 + vs.length)

/-- Append a tuple's tail section: the dynamic components' encodings. -/
def emitAnyTupleTails (acc : ByteArray) : (ts : List Ty) → TupleValBA ts → List SizeT → ByteArray
  | [], _, _ => acc
  | _ :: _, _, [] => acc
  | t :: ts, (v, vs), c :: cs =>
      if t.isStatic then emitAnyTupleTails acc ts vs cs
      else emitAnyTupleTails (emitAny acc t v c) ts vs cs
termination_by ts _ _ => (sizeOf ts, 0)
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
      rw [sizesOfList, emitOffsets, ih, data_toList_emitUintWord, total_sizesOf t v,
        sizeBA_eq t v]
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
          total_sizesOf t v, sizeBA_eq t v]
        simp only [partsOfTupleBA, partOfBA, hst', putHeads, Builder.toList_append,
          toList_putUint, List.append_assoc]

private theorem tupleBase_eq : ∀ (ts : List Ty) (vs : TupleValBA ts),
    tupleBase ts (sizesOfTuple ts vs) = headSizes (partsOfTupleBA ts vs)
  | [], _ => by rw [sizesOfTuple, tupleBase, partsOfTupleBA]; rfl
  | t :: ts, (v, vs) => by
      rw [sizesOfTuple, tupleBase, partsOfTupleBA]
      by_cases hst : t.isStatic
      · rw [if_pos hst, total_sizesOf t v, sizeBA_eq t v, tupleBase_eq ts vs]
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
        have hput : putBA (.array t) ⟨vs, h⟩
            = putUint vs.length ++ putParts (vs.map (partOfBA t)) := by rw [putBA]
        rw [hput, Builder.toList_append, toList_putUint, toList_putParts_static hst,
          List.append_assoc]
      · have hst' : t.isStatic = false := by simpa using hst
        rw [if_neg hst]
        have hch : (sizesOf (.array t) ⟨vs, h⟩).children = sizesOfList t vs := by
          rw [sizesOf, if_neg hst]
        rw [hch, data_toList_emitAnyTails t hst', data_toList_emitOffsets t hst',
          data_toList_emitUintWord]
        have hput : putBA (.array t) ⟨vs, h⟩
            = putUint vs.length ++ putParts (vs.map (partOfBA t)) := by rw [putBA]
        rw [hput, Builder.toList_append, toList_putUint, putParts, Builder.toList_append,
          headSizes_dynamic hst']
        simp only [List.append_assoc]
  | .fixedArray t n, acc, ⟨vs, h⟩ => by
      rw [emitAny]
      by_cases hst : t.isStatic
      · rw [if_pos hst, data_toList_emitVals hst]
        have hput : putBA (.fixedArray t n) ⟨vs, h⟩
            = putParts (vs.map (partOfBA t)) := by rw [putBA]
        rw [hput, toList_putParts_static hst]
      · have hst' : t.isStatic = false := by simpa using hst
        rw [if_neg hst]
        have hch : (sizesOf (.fixedArray t n) ⟨vs, h⟩).children = sizesOfList t vs := by
          rw [sizesOf, if_neg hst]
        rw [hch, data_toList_emitAnyTails t hst', data_toList_emitOffsets t hst']
        have hput : putBA (.fixedArray t n) ⟨vs, h⟩
            = putParts (vs.map (partOfBA t)) := by rw [putBA]
        rw [hput, putParts, Builder.toList_append, headSizes_dynamic hst']
        simp only [List.append_assoc]
  | .tuple ts, acc, vs => by
      rw [emitAny]
      have hch : (sizesOf (.tuple ts) vs).children = sizesOfTuple ts vs := by
        rw [sizesOf]
      rw [hch, data_toList_emitAnyTupleTails, data_toList_emitTupleHeads,
        tupleBase_eq]
      have hput : putBA (.tuple ts) vs = putParts (partsOfTupleBA ts vs) := by rw [putBA]
      rw [hput, putParts, Builder.toList_append]
      simp only [List.append_assoc]
termination_by t _ _ => (sizeOf t, 0)

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
termination_by t _ _ vs => (sizeOf t, 1 + vs.length)

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
termination_by ts _ _ => (sizeOf ts, 1)
end

/-- `encode` with the static-element, `bytes[]` and `string[]` array arms
fused (the swap the compiler acts on; every theorem stays stated over
`encode`). -/
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
  | .array t, v =>
      if t.isStatic then
        emitVals (emitUintWord
          (ByteArray.emptyWithCapacity (32 + staticSize t * v.val.length)) v.val.length) t v.val
      else emitAnyRun (.array t) v
  | .bytes, v => emitPayload (ByteArray.emptyWithCapacity (dynTailSize v.val.size)) v.val
  | .string, v =>
      emitPayload (ByteArray.emptyWithCapacity (dynTailSize v.val.utf8ByteSize)) v.val.toUTF8
  | t, v =>
      if t.isStatic then emitVal (ByteArray.emptyWithCapacity (staticSize t)) t v
      else emitAnyRun t v

/-- A static value's whole encoding is its head, so it streams through
`emitVal` — a struct of words costs no `Part` per component. -/
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

/-- The catch-all arm agrees with `encode`, at any type. -/
private theorem encode_nonarray_arm (t : Ty) (v : ValBA t) :
    encode t v
      = if t.isStatic then emitVal (ByteArray.emptyWithCapacity (staticSize t)) t v
        else emitAnyRun t v := by
  by_cases ht : t.isStatic
  · rw [if_pos ht]
    exact encode_static_arm v ht
  · rw [if_neg ht]
    exact encode_emitAny t v

/-- The static-element arm agrees with `encode`, at any element type. -/
private theorem encode_array_static_arm (te : Ty) (vs : List (ValBA te))
    (h : vs.length < 2 ^ 64) :
    encode (.array te) ⟨vs, h⟩
      = if te.isStatic then
          emitVals (emitUintWord
            (ByteArray.emptyWithCapacity (32 + staticSize te * vs.length)) vs.length) te vs
        else emitAnyRun (.array te) ⟨vs, h⟩ := by
  by_cases ht : te.isStatic
  · rw [if_pos ht]
    apply ByteArray.data_inj
    rw [← Array.toList_inj]
    rw [encode, Builder.data_toList_run]
    have hput : putBA (.array te) ⟨vs, h⟩
        = putUint vs.length ++ putParts (vs.map (partOfBA te)) := by
      rw [putBA]
    rw [hput, Builder.toList_append, toList_putUint, toList_putParts_static ht]
    rw [data_toList_emitVals ht, data_toList_emitUintWord, toList_emptyWithCapacity,
      List.nil_append]
  · rw [if_neg ht]
    exact encode_emitAny _ _

@[csimp] theorem encode_eq_fast : @encode = @encodeFast := by
  funext t v
  match t, v with
  | .uint _, v | .int _, v | .bool, v | .address, v | .bytesN _, v
  | .fixedArray _ _, v | .tuple _, v =>
      exact encode_nonarray_arm _ v
  | .bytes, ⟨bs, h⟩ =>
      apply ByteArray.data_inj
      rw [← Array.toList_inj]
      show (encode .bytes ⟨bs, h⟩).data.toList
        = (emitPayload (ByteArray.emptyWithCapacity (dynTailSize bs.size)) bs).data.toList
      rw [encode, Builder.data_toList_run, data_toList_emitPayload, toList_emptyWithCapacity,
        List.nil_append]
      exact toList_putBA_bytes ⟨bs, h⟩
  | .string, ⟨s, h⟩ =>
      apply ByteArray.data_inj
      rw [← Array.toList_inj]
      show (encode .string ⟨s, h⟩).data.toList
        = (emitPayload (ByteArray.emptyWithCapacity (dynTailSize s.utf8ByteSize))
            s.toUTF8).data.toList
      rw [encode, Builder.data_toList_run, data_toList_emitPayload, toList_emptyWithCapacity,
        List.nil_append]
      exact toList_putBA_string ⟨s, h⟩
  | .array (.uint _), ⟨vs, h⟩ | .array (.int _), ⟨vs, h⟩ | .array .bool, ⟨vs, h⟩
  | .array .address, ⟨vs, h⟩ | .array (.bytesN _), ⟨vs, h⟩
  | .array (.array _), ⟨vs, h⟩ | .array (.fixedArray _ _), ⟨vs, h⟩
  | .array (.tuple _), ⟨vs, h⟩ =>
      exact encode_array_static_arm _ vs h
  | .array .bytes, ⟨vs, h⟩ =>
      apply ByteArray.data_inj
      rw [← Array.toList_inj]
      show (encode (.array .bytes) ⟨vs, h⟩).data.toList
        = (emitDynTails (fun u : ValBA .bytes => u.val)
            (emitDynHeads (fun u : ValBA .bytes => u.val.size)
              (emitUintWord
                (ByteArray.emptyWithCapacity
                  (vs.foldl (fun s u => s + 32 + dynTailSize u.val.size) 32)) vs.length)
              (32 * vs.length) vs)
            vs).data.toList
      rw [encode, Builder.data_toList_run]
      have hput : putBA (.array .bytes) ⟨vs, h⟩
          = putUint vs.length ++ putParts (vs.map (partOfBA .bytes)) := by
        rw [putBA]
      rw [hput, Builder.toList_append, toList_putUint, putParts, Builder.toList_append,
        headSizes_dynamic rfl]
      rw [data_toList_emitDynTails rfl toList_putBA_bytes,
        data_toList_emitDynHeads rfl size_putBA_bytes, data_toList_emitUintWord,
        toList_emptyWithCapacity, List.nil_append]
      simp only [List.append_assoc]
  | .array .string, ⟨vs, h⟩ =>
      apply ByteArray.data_inj
      rw [← Array.toList_inj]
      show (encode (.array .string) ⟨vs, h⟩).data.toList
        = (emitDynTails (fun u : ValBA .string => u.val.toUTF8)
            (emitDynHeads (fun u : ValBA .string => u.val.utf8ByteSize)
              (emitUintWord
                (ByteArray.emptyWithCapacity
                  (vs.foldl (fun s u => s + 32 + dynTailSize u.val.utf8ByteSize) 32))
                vs.length)
              (32 * vs.length) vs)
            vs).data.toList
      rw [encode, Builder.data_toList_run]
      have hput : putBA (.array .string) ⟨vs, h⟩
          = putUint vs.length ++ putParts (vs.map (partOfBA .string)) := by
        rw [putBA]
      rw [hput, Builder.toList_append, toList_putUint, putParts, Builder.toList_append,
        headSizes_dynamic rfl]
      rw [data_toList_emitDynTails rfl toList_putBA_string,
        data_toList_emitDynHeads rfl size_putBA_string, data_toList_emitUintWord,
        toList_emptyWithCapacity, List.nil_append]
      simp only [List.append_assoc]

/-! ## the runtime decoder -/

/-- **Runtime prefix decoder**: the efficient path users run — one shared
`ByteArray`, `ValBA` values, offset cursors.  Returns the value and the
bytes consumed. -/
def decode (t : Ty) (ba : ByteArray) : Option (ValBA t × Nat) := decodeBAVal t ba 0

/-- **Runtime strict decoder**: canonical layout, consumed exactly, packed
values. -/
def decodeStrict (t : Ty) (ba : ByteArray) : Option (ValBA t) := decodeStrictBAVal t ba

/-- A buffer is a canonical runtime encoding of type `t`. -/
def IsCanonical (t : Ty) (ba : ByteArray) : Prop :=
  (decodeStrict t ba).isSome = true

instance (t : Ty) (ba : ByteArray) : Decidable (IsCanonical t ba) := by
  unfold IsCanonical
  infer_instance

/-! ## capstones

The `Spec` capstones on the runtime names, each a rewrite over its `…BA`
counterpart through `encode_eq_encodeByteArray`.  The decoder side also needs
`ValBA.toList_injective`. -/

/-- The runtime encoder is the spec's `ByteArray` encoder at the denotation —
the bridge every capstone below goes through. -/
theorem encode_eq_encodeByteArray (t : Ty) (v : ValBA t) :
    encode t v = Spec.encodeByteArray t (ValBA.toList t v) := by
  rw [encode_eq, Spec.encodeByteArray_eq]

/-- Pull a conclusion back through an injective denotation. -/
private theorem eq_some_of_map_eq {α β : Type} {f : α → β} {o : Option α} {v : α}
    (hf : ∀ {a b : α}, f a = f b → a = b) (h : o.map f = some (f v)) : o = some v := by
  cases o with
  | none => simp at h
  | some a =>
      rw [Option.map_some, Option.some.injEq] at h
      rw [hf h]

/-- **Runtime roundtrip** (capstone): what `encode` writes, `decodeStrict`
reads back — as the very same `ValBA` value, not merely one with the same
denotation. -/
theorem decodeStrict_encode (t : Ty) (hv : t.Valid) (v : ValBA t)
    (hb : (encode t v).size < 2 ^ 256) :
    decodeStrict t (encode t v) = some v := by
  refine eq_some_of_map_eq (fun {_ _} hab => ValBA.toList_injective t hab) ?_
  rw [decodeStrict, decodeStrictBAVal_eq t hv, encode_eq_encodeByteArray]
  exact decodeStrictBA_encodeByteArray t hv _ (by rwa [← encode_eq_encodeByteArray])

/-- **Runtime uniqueness** (capstone): a strictly decodable buffer *is* the
encoding of its decoded value. -/
theorem encode_of_decodeStrict (t : Ty) (hv : t.Valid) (ba : ByteArray) (v : ValBA t)
    (h : decodeStrict t ba = some v) : encode t v = ba := by
  rw [encode_eq_encodeByteArray]
  refine encodeByteArray_of_decodeStrictBA t hv ba _ ?_
  rw [← decodeStrictBAVal_eq t hv, ← decodeStrict, h, Option.map_some]

/-- **Runtime strict-decoder characterization** (capstone). -/
theorem decodeStrict_eq_some_iff (t : Ty) (hv : t.Valid) (ba : ByteArray)
    (v : ValBA t) (hb : ba.size < 2 ^ 256) :
    decodeStrict t ba = some v ↔ encode t v = ba := by
  constructor
  · exact encode_of_decodeStrict t hv ba v
  · intro he
    rw [← he]
    exact decodeStrict_encode t hv v (by rw [he]; exact hb)

/-- **Runtime image characterization** (capstone): the canonical buffers are
exactly the image of `encode`. -/
theorem isCanonical_iff (t : Ty) (hv : t.Valid) (ba : ByteArray)
    (hb : ba.size < 2 ^ 256) :
    IsCanonical t ba ↔ ∃ v : ValBA t, encode t v = ba := by
  constructor
  · intro hc
    obtain ⟨v, hvv⟩ := Option.isSome_iff_exists.mp hc
    exact ⟨v, encode_of_decodeStrict t hv ba v hvv⟩
  · rintro ⟨v, he⟩
    have hr := decodeStrict_encode t hv v (by rw [he]; exact hb)
    rw [he] at hr
    rw [IsCanonical, hr]
    rfl

end EvmAbi.Codec
