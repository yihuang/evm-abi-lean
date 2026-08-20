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

/-! ## the static-element array fast path

The array arm of `putBA` builds a `Part`, two `Builder`s and an `append`
node per element, and `emit` then walks them all; for a static element
type the layout is plain concatenation (`toList_putParts_static`), so the
fused arm writes the length word and every element straight into the
pre-sized output.  `emitVal` is the one writer for every static type — a
dynamic element cannot stream in one pass, because each head slot holds an
offset that depends on every preceding tail's size.  The `@[csimp]` swap
sits on `encode`, not `putBA`: two builders with different trees are never
equal, but the `ByteArray`s they run to are. -/

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
      Chunks.emitWord acc (UInt256.ofNat (if 0 ≤ i then i.toNat else 2 ^ 256 - (-i).toNat))
  | .bool, b => Chunks.emitWord acc (UInt256.ofNat (if b then 1 else 0))
  | .address, ⟨n, _⟩ => Chunks.emitWord acc (UInt256.ofNat n)
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
      rw [emitVal, Chunks.data_toList_emitWord, putBA]
      simp only [toList_putInt, encodeInt, encodeUint]
  | .bool, ht, acc, b => by
      rw [emitVal, Chunks.data_toList_emitWord, putBA]
      simp only [toList_putBool, encodeBool, encodeUint]
  | .address, ht, acc, ⟨n, hn⟩ => by
      rw [emitVal, Chunks.data_toList_emitWord, putBA]
      simp only [toList_putAddress, encodeAddress, encodeUint]
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

/-- `encode` with the static-element array arm fused (the swap the compiler
acts on; every theorem stays stated over `encode`). -/
def encodeFast (t : Ty) (v : ValBA t) : ByteArray :=
  match t, v with
  | .array t, v =>
      if t.isStatic then
        emitVals (pushLimb (UInt64.ofNat v.val.length)
          (Chunks.pushZeros32
            (ByteArray.emptyWithCapacity (32 + t.headSize * v.val.length)) 24)) t v.val
      else encode (.array t) v
  | t, v => encode t v

@[csimp] theorem encode_eq_fast : @encode = @encodeFast := by
  funext t v
  match t, v with
  | .uint _, _ | .int _, _ | .bool, _ | .address, _ | .bytesN _, _ | .bytes, _
  | .string, _ | .fixedArray _ _, _ | .tuple _, _ => rfl
  | .array te, ⟨vs, h⟩ =>
      show encode (.array te) ⟨vs, h⟩
        = if te.isStatic then
            emitVals (pushLimb (UInt64.ofNat vs.length)
              (Chunks.pushZeros32
                (ByteArray.emptyWithCapacity (32 + te.headSize * vs.length)) 24)) te vs
          else encode (.array te) ⟨vs, h⟩
      by_cases ht : te.isStatic
      · rw [if_pos ht]
        apply ByteArray.data_inj
        rw [← Array.toList_inj]
        rw [encode, Builder.data_toList_run]
        have hput : putBA (.array te) ⟨vs, h⟩
            = putUint vs.length ++ putParts (vs.map (partOfBA te)) := by
          rw [putBA]
        rw [hput, Builder.toList_append, toList_putUint, toList_putParts_static ht]
        rw [data_toList_emitVals ht, pushLimb_eq, Chunks.data_toList_pushZeros32 _ (by omega),
          toList_emptyWithCapacity, List.nil_append, encodeBEU_window (by omega),
          encodeUint_eq, show (32 : Nat) = 8 + 24 from rfl,
          encodeBEU_pad (show vs.length < 256 ^ 8 by omega) 24, List.append_assoc]
      · rw [if_neg ht]

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
