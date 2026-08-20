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

/-! ## the `uint` array fast path

The array arm of `putBA` builds a `Part`, two `Builder`s and an `append`
node per element, and `emit` then walks them all; for an array of `uint`
the layout is plain concatenation, so the walk below writes the length
word and every element straight into the pre-sized output.  The `@[csimp]`
swap sits on `encode`, not `putBA`: two builders with different trees are
never equal, but the `ByteArray`s they run to are. -/

/-- `emitWord` each value in order. -/
def emitWords {m : Nat} (acc : ByteArray) : List (ValBA (.uint m)) → ByteArray
  | [] => acc
  | v :: vs => emitWords (Chunks.emitWord acc v.val) vs

theorem data_toList_emitWords {m : Nat} (acc : ByteArray) (vs : List (ValBA (.uint m))) :
    (emitWords acc vs).data.toList
      = acc.data.toList ++ (vs.map fun v => bytesOfWord v.val).flatten := by
  induction vs generalizing acc with
  | nil => simp [emitWords]
  | cons v vs ih => simp [emitWords, ih, Chunks.data_toList_emitWord]

private theorem toList_putHeads_uint (m : Nat) (vs : List (ValBA (.uint m))) (acc : Nat) :
    (putHeads acc (vs.map (partOfBA (.uint m)))).toList
      = (vs.map fun v => bytesOfWord v.val).flatten := by
  induction vs generalizing acc with
  | nil => rfl
  | cons v vs ih =>
      obtain ⟨w, hw⟩ := v
      simp only [List.map_cons, partOfBA, putBA, Ty.isStatic, putHeads,
        Builder.toList_append, toList_putWord, ih acc, List.flatten_cons]

private theorem toList_putTails_uint (m : Nat) (vs : List (ValBA (.uint m))) :
    (putTails (vs.map (partOfBA (.uint m)))).toList = [] := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa only [List.map_cons, partOfBA, Ty.isStatic, putTails] using ih

/-- Static parts lay out as concatenation: the heads are the encodings and
the tail section is empty. -/
theorem toList_putParts_uint (m : Nat) (vs : List (ValBA (.uint m))) :
    (putParts (vs.map (partOfBA (.uint m)))).toList
      = (vs.map fun v => bytesOfWord v.val).flatten := by
  rw [putParts, Builder.toList_append, toList_putHeads_uint, toList_putTails_uint,
    List.append_nil]

/-- `encode` with the `uint` array arm fused (the swap the compiler acts
on; every theorem stays stated over `encode`). -/
def encodeFast (t : Ty) (v : ValBA t) : ByteArray :=
  match t, v with
  | .array (.uint _), ⟨vs, _⟩ =>
      emitWords (pushLimb (UInt64.ofNat vs.length)
        (Chunks.pushZeros32 (ByteArray.emptyWithCapacity (32 + 32 * vs.length)) 24)) vs
  | t, v => encode t v

@[csimp] theorem encode_eq_fast : @encode = @encodeFast := by
  funext t v
  match t, v with
  | .uint _, _ | .int _, _ | .bool, _ | .address, _ | .bytesN _, _ | .bytes, _
  | .string, _ | .fixedArray _ _, _ | .tuple _, _ => rfl
  | .array (.int _), _ | .array .bool, _ | .array .address, _ | .array (.bytesN _), _
  | .array .bytes, _ | .array .string, _ | .array (.array _), _
  | .array (.fixedArray _ _), _ | .array (.tuple _), _ => rfl
  | .array (.uint m), ⟨vs, h⟩ =>
      apply ByteArray.data_inj
      rw [← Array.toList_inj]
      show (encode (.array (.uint m)) ⟨vs, h⟩).data.toList
        = (emitWords (pushLimb (UInt64.ofNat vs.length)
            (Chunks.pushZeros32 (ByteArray.emptyWithCapacity (32 + 32 * vs.length)) 24))
            vs).data.toList
      rw [encode, Builder.data_toList_run]
      have hput : putBA (.array (.uint m)) ⟨vs, h⟩
          = putUint vs.length ++ putParts (vs.map (partOfBA (.uint m))) := by
        rw [putBA]
      rw [hput, Builder.toList_append, toList_putUint, toList_putParts_uint]
      rw [data_toList_emitWords, pushLimb_eq, Chunks.data_toList_pushZeros32 _ (by omega),
        toList_emptyWithCapacity, List.nil_append, encodeBEU_window (by omega),
        encodeUint_eq, show (32 : Nat) = 8 + 24 from rfl,
        encodeBEU_pad (show vs.length < 256 ^ 8 by omega) 24, List.append_assoc]

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
