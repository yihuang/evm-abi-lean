import EvmAbi.Codec
import EvmAbi.Codec.ByteArray
import EvmAbi.ValBA

/-!
# EvmAbi.Codec.Runtime

The runtime codec users run: `encode` (`ValBA` values into a `ByteArray`),
`decode` / `decodeStrict` (`ByteArray` into `ValBA` values), and
`IsCanonical`.  The list-based specification codec lives in
`EvmAbi.Spec`; every runtime definition here is paired with an agreement
lemma against it, so nothing is reproved.
-/

namespace EvmAbi

open Ty
open Binary
open Builder

/-! ## the runtime encoder -/

/-- Write dynamic `bytes` from a packed payload: the length word (its size
is cached — no list walk), the payload as a `chunk`, and the padding as a
`zeros` run. -/
def putBytesBA (bs : ByteArray) : Builder :=
  putUint bs.size ++ Builder.chunk bs ++ Builder.zeros ((32 - bs.size % 32) % 32)

@[simp] theorem toList_putBytesBA (bs : ByteArray) :
    (putBytesBA bs).toList = encodeBytes bs.data.toList := by
  simp [putBytesBA, encodeBytes, pad32, List.append_assoc]

/-- Write fixed-size `bytesN` from a packed payload. -/
def putBytesNBA (bs : ByteArray) : Builder :=
  Builder.chunk bs ++ Builder.zeros (32 - bs.size)

@[simp] theorem toList_putBytesNBA (bs : ByteArray) :
    (putBytesNBA bs).toList = encodeBytesN bs.data.toList := by
  simp [putBytesNBA, encodeBytesN]

mutual
/-- ABI encoder over packed values: same layout as `Spec.put`, `chunk`
leaves for the payloads. -/
def putBA : (t : Ty) → ValBA t → Builder
  | .uint _, ⟨n, _⟩ => putUint n
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

namespace Part

/-- Two parts are equivalent when they denote the same bytes and occupy
the same cached sizes. -/
def Equiv (p q : Part) : Prop :=
  p.isDyn = q.isDyn ∧
    p.head.toList = q.head.toList ∧
    p.tail.toList = q.tail.toList ∧
    p.head.size = q.head.size ∧
    p.tail.size = q.tail.size

/-- Equivalent parts have equal head sizes. -/
theorem headSize_eq_of_equiv {p q : Part} (h : Equiv p q) : headSize p = headSize q := by
  rcases h with ⟨hdyn, hhead, htail, hs1, hs2⟩
  cases p with
  | mk ph pt pd =>
    cases q with
    | mk qh qt qd =>
      cases pd with
      | false =>
        cases qd with
        | false =>
            change ph.size = qh.size
            exact hs1
        | true => exact False.elim (Bool.noConfusion hdyn)
      | true =>
        cases qd with
        | false => exact False.elim (Bool.noConfusion hdyn)
        | true => simp [headSize]

/-- Equivalent parts have equal tail sizes. -/
theorem tailSize_eq_of_equiv {p q : Part} (h : Equiv p q) : tailSize p = tailSize q := by
  rcases h with ⟨hdyn, hhead, htail, hs1, hs2⟩
  cases p with
  | mk ph pt pd =>
    cases q with
    | mk qh qt qd =>
      cases pd with
      | false =>
        cases qd with
        | false => simp [tailSize]
        | true => exact False.elim (Bool.noConfusion hdyn)
      | true =>
        cases qd with
        | false => exact False.elim (Bool.noConfusion hdyn)
        | true =>
            change pt.size = qt.size
            exact hs2

end Part

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
      obtain ⟨n, hn⟩ := v
      rw [putBA.eq_1, ValBA.toList.eq_1, Spec.encode, Spec.put.eq_1]
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

end EvmAbi
