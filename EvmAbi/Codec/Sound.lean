import EvmAbi.Codec

/-!
# EvmAbi.Codec.Sound

The soundness family of the linear decoder: whenever `decode` succeeds, the
consumed front of the buffer is exactly the encoding of the decoded value —
`decode t buf = some (v, rest)` implies `encode t v ++ rest = buf`.  The
section is layered like the roundtrip family (`EvmAbi.Codec.Roundtrip`):
per-constructor *word atoms* reuse the word-recovery lemmas of
`EvmAbi.Codec`, and the *walkers* (`decodeElem_sound_static` /
`decodeElem_sound_dynamic`, `decodeElems_sound`, `decodeTuple_sound`)
thread them through a run of parts.

This is what makes `decodeStrict` (`EvmAbi.Codec.Strict`) the strict
counterpart of `encode`.
-/

namespace EvmAbi

open Ty
open Binary
open Builder

/-! ## soundness: the linear decoder only produces encodings -/

/- The mirror of the roundtrips: whenever the linear decoder succeeds, the
consumed front of the buffer is exactly the encoding of the decoded value.
This is what makes `decodeStrict` -- the decoder plus an
exact-consumption check -- the strict counterpart of `encode`.

The section is layered like the roundtrip section:

* **word atoms** -- one lemma per constructor.  Each unpacks the single
  `decode` step, projects the pair, and recombines the buffer with
  `List.take_append_drop`; the `int`/`bool`/`bytesN` arms reuse the
  word-recovery lemmas of the helper section.
* **walkers** -- `decodeElem_sound_static`/`_dynamic` pin one
  component's head slot to the encoding and its frontier slice to the
  tail; the element-list and tuple walkers thread them through a run of
  parts; the prefix form `decode_sound` assembles the atoms and
  walkers. -/

/-- `decodeElem` of a static type reads in place and keeps the
frontier. -/
theorem decodeElem_static (t : Ty) (head tails : List UInt8) (E : Nat)
    (h : t.isStatic = true) :
    (decodeElem t).run head tails E = (match decode t head with
      | some (v, rest) => some ⟨v, rest, tails, E⟩
      | none => none) := by
  unfold decodeElem
  rw [h]
  rfl

/-- `decodeElem` of a dynamic type checks the offset word against
the frontier. -/
theorem decodeElem_dynamic (t : Ty) (head tails : List UInt8) (E : Nat)
    (h : t.isStatic = false) :
    (decodeElem t).run head tails E = (match natAt head 0 with
      | none => none
      | some o => if o = E then
          match decode t tails with
          | some (v, rest) => some ⟨v, head.drop 32, rest, E + (tails.length - rest.length)⟩
          | none => none
        else none) := by
  unfold decodeElem
  rw [h]
  rfl

/- ### word atoms -/

/-- `decode` at `uint` reads a canonical `uint` word. -/
theorem decode_uint_sound (m : Nat) (v : Ty.Val (.uint m)) (buf rest : List UInt8)
    (h : decode (.uint m) buf = some (v, rest)) :
    encode (.uint m) v ++ rest = buf := by
  obtain ⟨n, hn⟩ := v
  simp only [decode] at h
  cases hdu : decodeUint buf with
  | none => simp only [hdu] at h; contradiction
  | some x =>
      simp only [hdu] at h
      by_cases hx : x < 2 ^ m
      · rw [dif_pos hx] at h
        have hpair := Option.some.inj h
        have hxn : x = n := congrArg (fun p => p.1.val) hpair
        have hrest : buf.drop 32 = rest := congrArg (fun p => p.2) hpair
        subst hxn
        simp only [encode, put, toList_putUint]
        rw [← hrest, ← buf_take_32_eq_encodeUint_of_decodeUint buf x hdu,
          List.take_append_drop 32 buf]
      · rw [dif_neg hx] at h; contradiction

/-- `decode` at `int` reads a canonical `int` word. -/
theorem decode_int_sound (m : Nat) (v : Ty.Val (.int m)) (buf rest : List UInt8)
    (h : decode (.int m) buf = some (v, rest)) :
    encode (.int m) v ++ rest = buf := by
  obtain ⟨i, hi⟩ := v
  simp only [decode] at h
  cases hdi : decodeInt buf with
  | none => simp only [hdi] at h; contradiction
  | some x =>
      simp only [hdi] at h
      by_cases hx : -((2 ^ (m - 1) : Nat) : Int) ≤ x ∧ x < ((2 ^ (m - 1) : Nat) : Int)
      · rw [dif_pos hx] at h
        have hpair := Option.some.inj h
        have hxi : x = i := congrArg (fun p => p.1.val) hpair
        have hrest : buf.drop 32 = rest := congrArg (fun p => p.2) hpair
        subst hxi
        have hword : ∃ w, decodeUint buf = some w ∧ encodeInt x = encodeUint w := by
          cases hdw : decodeUint buf with
          | none => simp only [decodeInt, hdw] at hdi; contradiction
          | some w => exact ⟨w, rfl, encodeInt_eq_encodeUint_of_decodeInt hdi hdw⟩
        obtain ⟨w, hdw, henc⟩ := hword
        simp only [encode, put, toList_putInt]
        rw [henc, ← hrest, ← buf_take_32_eq_encodeUint_of_decodeUint buf w hdw,
          List.take_append_drop 32 buf]
      · rw [dif_neg hx] at h; contradiction

/-- `decode` at `bool` reads a canonical `bool` word. -/
theorem decode_bool_sound (v : Ty.Val .bool) (buf rest : List UInt8)
    (h : decode .bool buf = some (v, rest)) : encode .bool v ++ rest = buf := by
  simp only [decode] at h
  cases hdb : decodeBool buf with
  | none => simp only [hdb] at h; contradiction
  | some b =>
      simp only [hdb] at h
      have hpair := Option.some.inj h
      have hvb : b = v := congrArg Prod.fst hpair
      have hrest : buf.drop 32 = rest := congrArg Prod.snd hpair
      subst hvb
      have hdu : decodeUint buf = some (if b then 1 else 0) :=
        (decodeBool_eq_some_iff buf b).mp hdb
      have htake := buf_take_32_eq_encodeUint_of_decodeUint buf (if b then 1 else 0) hdu
      simp only [encode, put, toList_putBool, encodeBool]
      rw [← hrest, ← htake, List.take_append_drop 32 buf]

/-- `decode` at `address` reads a canonical `address` word. -/
theorem decode_address_sound (v : Ty.Val .address) (buf rest : List UInt8)
    (h : decode .address buf = some (v, rest)) : encode .address v ++ rest = buf := by
  obtain ⟨n, hn⟩ := v
  simp only [decode] at h
  cases hda : decodeAddress buf with
  | none => simp only [hda] at h; contradiction
  | some x =>
      simp only [hda] at h
      by_cases hx : x < 2 ^ 160
      · rw [dif_pos hx] at h
        have hpair := Option.some.inj h
        have hxn : x = n := congrArg (fun p => p.1.val) hpair
        have hrest : buf.drop 32 = rest := congrArg (fun p => p.2) hpair
        subst hxn
        simp only [encode, put, toList_putAddress, encodeAddress]
        rw [← hrest, ← buf_take_32_eq_encodeUint_of_decodeUint buf x hda,
          List.take_append_drop 32 buf]
      · rw [dif_neg hx] at h; contradiction

/-- `decode` at `bytesN` reads a canonical `bytesN` word. -/
theorem decode_bytesN_sound (m : Nat) (v : Ty.Val (.bytesN m)) (buf rest : List UInt8)
    (h : decode (.bytesN m) buf = some (v, rest)) :
    encode (.bytesN m) v ++ rest = buf := by
  obtain ⟨bs, hbs⟩ := v
  simp only [decode] at h
  cases hdb : decodeBytesN m buf with
  | none => simp only [hdb] at h; contradiction
  | some xs =>
      simp only [hdb] at h
      by_cases hx : xs.length = m
      · rw [dif_pos hx] at h
        have hpair := Option.some.inj h
        have hxs : xs = bs := congrArg (fun p => p.1.val) hpair
        have hrest : buf.drop 32 = rest := congrArg (fun p => p.2) hpair
        subst hxs
        have htake := buf_take_32_eq_encodeBytesN_of_decodeBytesN hdb
        simp only [encode, put, toList_putBytesN]
        rw [← hrest, ← htake, List.take_append_drop 32 buf]
      · rw [dif_neg hx] at h; contradiction

/-- `decode` at `bytes` reads a canonical `bytes` payload. -/
theorem decode_bytes_sound (v : Ty.Val .bytes) (buf rest : List UInt8)
    (h : decode .bytes buf = some (v, rest)) : encode .bytes v ++ rest = buf := by
  obtain ⟨bs, hlb⟩ := v
  simp only [decode] at h
  split at h
  · next xs n hp =>
      injection (Option.some.inj h) with hxs' hrest
      injection hxs' with hxs
      subst hxs
      have htake := (take_eq_encodeBytes_of_decodeBytesPrefix buf xs n hp).1
      simp only [encode, put, toList_putBytes]
      rw [← hrest, ← htake, List.take_append_drop n buf]
  · contradiction

/-- `decode` at `string` reads a canonical `string` payload. -/
theorem decode_string_sound (v : Ty.Val .string) (buf rest : List UInt8)
    (h : decode .string buf = some (v, rest)) : encode .string v ++ rest = buf := by
  obtain ⟨s, hlb⟩ := v
  simp only [decode] at h
  split at h
  · next xs n hp =>
      split at h
      · next t hus =>
          injection (Option.some.inj h) with ht' hrest
          injection ht' with ht
          subst ht
          have htake := (take_eq_encodeBytes_of_decodeBytesPrefix buf xs n hp).1
          have hxs : xs = t.toUTF8.data.toList := by
            have hutf : t.toUTF8 = xs.toByteArray := toUTF8_of_fromUTF8? hus
            rw [hutf, List.data_toByteArray]
          simp only [encode, put, toList_putString, encodeString]
          rw [← hrest, ← hxs, ← htake, List.take_append_drop n buf]
      · contradiction
  · contradiction

/- ### the walkers -/

mutual
/-- **Soundness, per-component, static**: a canonical static component
reads back inline, leaving the frontier untouched. -/
theorem decodeElem_sound_static (t : Ty) (hv : t.Valid) (v : t.Val)
    (head tails : List UInt8) (E : Nat) (hs : t.isStatic = true)
    (h : (decodeElem t).run head tails E = some ⟨v, head', tails', E'⟩) :
    head = encode t v ++ head' ∧ tails' = tails ∧ E' = E := by
  rw [decodeElem_static t head tails E hs] at h
  cases ht : decode t head with
  | none => simp only [ht] at h; contradiction
  | some p =>
      obtain ⟨v', rest'⟩ := p
      simp only [ht] at h
      have hpair := Option.some.inj h
      have hv' : v' = v := congrArg (fun p => p.val) hpair
      have hhd : rest' = head' := congrArg (fun p => p.head) hpair
      have htl : tails = tails' := congrArg (fun p => p.tails) hpair
      have hE' : E = E' := congrArg (fun p => p.frontier) hpair
      subst hv'
      rw [← hhd, ← htl, ← hE']
      constructor
      · exact (decode_sound t hv v' head rest' ht).symm
      · constructor <;> rfl
termination_by 8 * sizeOf t + 1

/-- **Soundness, per-component, dynamic**: a canonical dynamic component's
head slot holds the offset word `E`, its frontier slice its tail, and the
frontier advances by the tail size. -/
theorem decodeElem_sound_dynamic (t : Ty) (hv : t.Valid) (v : t.Val)
    (head tails : List UInt8) (E : Nat) (hs : t.isStatic = false)
    (h : (decodeElem t).run head tails E = some ⟨v, head', tails', E'⟩) :
    head = encodeUint E ++ head' ∧ tails = encode t v ++ tails' ∧
      E' = E + (partOf t v).tailSize := by
  rw [decodeElem_dynamic t head tails E hs] at h
  cases hn : natAt head 0 with
  | none => simp only [hn] at h; contradiction
  | some o =>
      simp only [hn] at h
      by_cases ho : o = E
      · rw [if_pos ho] at h
        cases ht : decode t tails with
        | none => simp only [ht] at h; contradiction
        | some p =>
            obtain ⟨v', rest'⟩ := p
            simp only [ht] at h
            have hpair := Option.some.inj h
            have hv' : v' = v := congrArg (fun p => p.val) hpair
            have hhd : head.drop 32 = head' := congrArg (fun p => p.head) hpair
            have hrt : rest' = tails' := congrArg (fun p => p.tails) hpair
            have hE' : E + (tails.length - rest'.length) = E' :=
              congrArg (fun p => p.frontier) hpair
            have hword : head.take 32 = encodeUint E :=
              take_32_eq_encodeUint_of_natAt head 0 E (by simpa [ho] using hn)
            have hhead : head = encodeUint E ++ head' := by
              rw [← hword, ← hhd, List.take_append_drop 32 head]
            have htail : tails = encode t v ++ tails' := by
              have hsnd := decode_sound t hv v' tails rest' ht
              rw [hv', hrt] at hsnd
              exact hsnd.symm
            have hE'' : E' = E + (partOf t v).tailSize := by
              rw [← hE', hrt]
              rw [htail, List.length_append, Nat.add_sub_cancel]
              rw [tailSize_partOf_dynamic t v hs]
            exact ⟨hhead, htail, hE''⟩
      · rw [if_neg ho] at h; contradiction
termination_by 8 * sizeOf t + 1

/-- **Soundness, element lists**: a run of canonical elements that reads
back has consumed exactly its head and tail encodings. -/
theorem decodeElems_sound (t : Ty) (hv : t.Valid) (vs : List t.Val) (k : Nat)
    (hk : vs.length = k) (E : Nat) (head tails : List UInt8)
    (h : (decodeElems t k).run head tails E = some ⟨⟨vs, hk⟩, head', tails', E'⟩) :
    head = encodeHeads E (vs.map (partOf t)) ++ head' ∧
    tails = encodeTails (vs.map (partOf t)) ++ tails' ∧
    E' = E + tailSizes (vs.map (partOf t)) := by
  induction vs generalizing k E head tails with
  | nil =>
      subst hk
      change (decodeElems t 0).run head tails E = some ⟨⟨[], rfl⟩, head', tails', E'⟩ at h
      simp only [decodeElems, Get2.pure_run] at h
      have hhd : head = head' := congrArg (fun p => p.head) (Option.some.inj h)
      have htl : tails = tails' := congrArg (fun p => p.tails) (Option.some.inj h)
      have hE' : E = E' := congrArg (fun p => p.frontier) (Option.some.inj h)
      rw [hhd, htl, ← hE']
      simp [encodeHeads, encodeTails, putHeads, putTails, tailSizes, Builder.toList_empty]
  | cons w ws ih =>
      have hk' : k = ws.length + 1 := by rw [← hk, List.length_cons]
      subst hk'
      simp only [List.map_cons, decodeElems, Get2.bind_run, Get2.pure_run] at h ⊢
      cases he : (decodeElem t).run head tails E with
      | none => simp only [he] at h; contradiction
      | some p =>
          obtain ⟨v, head0, tails0, E0⟩ := p
          simp only [he] at h
          cases hi : (decodeElems t ws.length).run head0 tails0 E0 with
          | none => simp only [hi] at h; contradiction
          | some q =>
              obtain ⟨⟨ws', hws'⟩, head1, tails1, E1⟩ := q
              simp only [hi] at h
              have hpair := Option.some.inj h
              have hvs' : v :: ws' = w :: ws := congrArg (fun p => p.val.val) hpair
              have hhd1 : head1 = head' := congrArg (fun p => p.head) hpair
              have htl1 : tails1 = tails' := congrArg (fun p => p.tails) hpair
              injection hvs' with hv hws''
              subst hv
              subst hws''
              have hE1 : E1 = E' := congrArg (fun p => p.frontier) hpair
              rw [hhd1, htl1, hE1] at hi
              have hih : head0 = encodeHeads E0 (ws'.map (partOf t)) ++ head' ∧
                  tails0 = encodeTails (ws'.map (partOf t)) ++ tails' ∧
                  E' = E0 + tailSizes (ws'.map (partOf t)) :=
                ih ws'.length hws' E0 head0 tails0 hi
              cases hs0 : t.isStatic
              · have hsf : t.isStatic = false := hs0
                obtain ⟨hhead, htail, hE0'⟩ :=
                  decodeElem_sound_dynamic t hv v head tails E hsf he
                refine ⟨?_, ?_, ?_⟩
                · rw [hhead, hih.1, hE0']
                  rw [partOf_dynamic t v hsf, encodeHeads_cons_dynamic]
                  simp [Part.tailSize]
                · rw [htail, hih.2.1]
                  rw [partOf_dynamic t v hsf, encodeTails_cons_dynamic, List.append_assoc]
                  rfl
                · rw [hih.2.2, hE0']
                  simp [tailSizes, Nat.add_assoc]
              · have hst : t.isStatic = true := hs0
                obtain ⟨hhead, htl0, hE0⟩ :=
                  decodeElem_sound_static t hv v head tails E hst he
                refine ⟨?_, ?_, ?_⟩
                · rw [hhead, hih.1, hE0]
                  rw [partOf_static t v hst, encodeHeads_cons_static, List.append_assoc]
                  rfl
                · rw [← htl0, hih.2.1]
                  rw [partOf_static t v hst, encodeTails_cons_static]
                · rw [hih.2.2, hE0]
                  simp [tailSizes, tailSize_partOf_static t v hst]
termination_by 8 * sizeOf t + 2

/-- **Soundness, tuples**: a canonical tuple that reads back has consumed
exactly its head and tail encodings. -/
theorem decodeTuple_sound : (ts : List Ty) → AllValid ts → (vs : TupleVal ts) →
    (E : Nat) → (head tails : List UInt8) →
    (decodeTuple ts).run head tails E = some ⟨vs, head', tails', E'⟩ →
    head = encodeHeads E (partsOfTuple ts vs) ++ head' ∧
    tails = encodeTails (partsOfTuple ts vs) ++ tails' ∧
    E' = E + tailSizes (partsOfTuple ts vs)
  | [], hv, vs, E, head, tails, h => by
      simp only [decodeTuple, Get2.pure_run] at h
      have hhd : head = head' := congrArg (fun p => p.head) (Option.some.inj h)
      have htl : tails = tails' := congrArg (fun p => p.tails) (Option.some.inj h)
      have hE' : E = E' := congrArg (fun p => p.frontier) (Option.some.inj h)
      rw [hhd, htl, ← hE']
      simp [partsOfTuple, encodeHeads, encodeTails, putHeads, putTails, tailSizes,
        Builder.toList_empty]
  | t :: ts, hv, (v, vs), E, head, tails, h => by
      obtain ⟨hvt, hvs⟩ := hv
      simp only [partsOfTuple, decodeTuple, Get2.bind_run, Get2.pure_run] at h ⊢
      cases he : (decodeElem t).run head tails E with
      | none => simp only [he] at h; contradiction
      | some p =>
          obtain ⟨v', head0, tails0, E0⟩ := p
          simp only [he] at h
          cases hi : (decodeTuple ts).run head0 tails0 E0 with
          | none => simp only [hi] at h; contradiction
          | some q =>
              obtain ⟨vs', head1, tails1, E1⟩ := q
              simp only [hi] at h
              have hpair := Option.some.inj h
              have hv' : v' = v := congrArg (fun p => p.val.1) hpair
              have hvs' : vs' = vs := congrArg (fun p => p.val.2) hpair
              have hhd1 : head1 = head' := congrArg (fun p => p.head) hpair
              have htl1 : tails1 = tails' := congrArg (fun p => p.tails) hpair
              subst hv'
              subst hvs'
              have hE1 : E1 = E' := congrArg (fun p => p.frontier) hpair
              have hih : head0 = encodeHeads E0 (partsOfTuple ts vs') ++ head1 ∧
                  tails0 = encodeTails (partsOfTuple ts vs') ++ tails1 ∧
                  E1 = E0 + tailSizes (partsOfTuple ts vs') :=
                decodeTuple_sound ts hvs vs' E0 head0 tails0 hi
              cases hs0 : t.isStatic
              · have hsf : t.isStatic = false := hs0
                obtain ⟨hhead, htail, hE0'⟩ :=
                  decodeElem_sound_dynamic t hvt v' head tails E hsf he
                refine ⟨?_, ?_, ?_⟩
                · rw [hhead, hih.1, hE0', hhd1]
                  rw [partOf_dynamic t v' hsf, encodeHeads_cons_dynamic]
                  simp [Part.tailSize]
                · rw [htail, hih.2.1, htl1]
                  rw [partOf_dynamic t v' hsf, encodeTails_cons_dynamic, List.append_assoc]
                  rfl
                · rw [← hE1, hih.2.2, hE0']
                  simp [tailSizes, Nat.add_assoc]
              · have hst : t.isStatic = true := hs0
                obtain ⟨hhead, htl0, hE0⟩ :=
                  decodeElem_sound_static t hvt v' head tails E hst he
                refine ⟨?_, ?_, ?_⟩
                · rw [hhead, hih.1, hE0, hhd1]
                  rw [partOf_static t v' hst, encodeHeads_cons_static, List.append_assoc]
                  rfl
                · rw [← htl0, hih.2.1, htl1]
                  rw [partOf_static t v' hst, encodeTails_cons_static]
                · rw [← hE1, hih.2.2, hE0]
                  simp [tailSizes, tailSize_partOf_static t v' hst]
termination_by ts => 8 * sizeOf ts + 3

/-- **Soundness, prefix form**: whenever the linear decoder succeeds, the
buffer is the encoding of the decoded value plus the remainder. -/
theorem decode_sound (t : Ty) (hv : t.Valid) (v : t.Val) (buf rest : List UInt8)
    (h : decode t buf = some (v, rest)) : encode t v ++ rest = buf := by
  cases t with
  | uint m => exact decode_uint_sound m v buf rest h
  | int m => exact decode_int_sound m v buf rest h
  | bool => exact decode_bool_sound v buf rest h
  | address => exact decode_address_sound v buf rest h
  | bytesN m => exact decode_bytesN_sound m v buf rest h
  | bytes => exact decode_bytes_sound v buf rest h
  | string => exact decode_string_sound v buf rest h
  | array t =>
      obtain ⟨vs, hlk⟩ := v
      have hvt : t.Valid := hv
      simp only [decode] at h
      split at h
      · contradiction
      · next k hk =>
          cases he : (decodeElems t k).run (buf.drop 32) (buf.drop (32 + k * t.headSize))
            (k * t.headSize) with
          | none => simp only [he] at h; contradiction
          | some q =>
              obtain ⟨⟨vs', hvs'⟩, head0, tails0, E0⟩ := q
              simp only [he] at h
              have hpair := Option.some.inj h
              have hvs'eq : vs' = vs := congrArg (fun p => p.1.val) hpair
              have hrt : tails0 = rest := congrArg (fun p => p.2) hpair
              have hsnd := decodeElems_sound t hvt vs' k hvs' (k * t.headSize)
                (buf.drop 32) (buf.drop (32 + k * t.headSize)) he
              have hlenH : headSizes (vs'.map (partOf t)) = vs'.length * t.headSize :=
                headSizes_map_partOf_any t hvt vs'
              have htake : buf.take 32 = encodeUint k :=
                buf_take_32_eq_encodeUint_of_decodeUint buf k hk
              have hhead0 : head0 = encodeTails (vs'.map (partOf t)) ++ tails0 := by
                have hlen : (encodeHeads (k * t.headSize) (vs'.map (partOf t))).length =
                    k * t.headSize := by
                  rw [length_encodeHeads, hlenH, hvs']
                have hd := congrArg (fun x => x.drop (k * t.headSize)) hsnd.1
                rw [drop_append_of_length hlen] at hd
                rw [List.drop_drop] at hd
                rw [← hd, hsnd.2.1]
              have hinner : encodeHeads (k * t.headSize) (vs'.map (partOf t)) ++
                  (encodeTails (vs'.map (partOf t)) ++ rest) = buf.drop 32 := by
                rw [hsnd.1, hhead0, hrt]
              simp only [encode, put, toList_putUint, toList_append]
              rw [← hvs'eq, hvs', ← htake, ← encodeParts, encodeParts_unfold, hlenH, hvs',
                List.append_assoc, List.append_assoc, hinner, List.take_append_drop 32 buf]
  | fixedArray t n =>
      obtain ⟨vs, hvs⟩ := v
      have hvt : t.Valid := hv
      simp only [decode] at h
      cases he : (decodeElems t n).run buf (buf.drop (n * t.headSize)) (n * t.headSize) with
      | none => simp only [he] at h; contradiction
      | some q =>
          obtain ⟨⟨vs', hvs'⟩, head0, tails0, E0⟩ := q
          simp only [he] at h
          have hpair := Option.some.inj h
          have hvs'eq : vs' = vs := congrArg (fun p => p.1.val) hpair
          have hrt : tails0 = rest := congrArg (fun p => p.2) hpair
          have hsnd := decodeElems_sound t hvt vs' n hvs' (n * t.headSize) buf
            (buf.drop (n * t.headSize)) he
          have hlenH : headSizes (vs'.map (partOf t)) = n * t.headSize := by
            rw [headSizes_map_partOf_any t hvt vs', hvs']
          have hhead0 : head0 = encodeTails (vs'.map (partOf t)) ++ tails0 := by
            have hlen : (encodeHeads (n * t.headSize) (vs'.map (partOf t))).length =
                n * t.headSize := by
              rw [length_encodeHeads, hlenH]
            have hd := congrArg (fun x => x.drop (n * t.headSize)) hsnd.1
            rw [drop_append_of_length hlen] at hd
            rw [← hd, hsnd.2.1]
          simp only [encode, put]
          rw [← hvs'eq, ← encodeParts, encodeParts_unfold, hlenH, hsnd.1, hhead0, hrt,
            List.append_assoc]
  | tuple ts =>
      have hvts : AllValid ts := hv
      simp only [decode] at h
      cases he : (decodeTuple ts).run buf (buf.drop (headSizeSum ts)) (headSizeSum ts) with
      | none => simp only [he] at h; contradiction
      | some q =>
          obtain ⟨vs', head0, tails0, E0⟩ := q
          simp only [he] at h
          have hpair := Option.some.inj h
          have hvs' : vs' = v := congrArg (fun p => p.1) hpair
          have hrt : tails0 = rest := congrArg (fun p => p.2) hpair
          subst hvs'
          have hsnd := decodeTuple_sound ts hvts vs' (headSizeSum ts) buf
            (buf.drop (headSizeSum ts)) he
          have hlenH : headSizes (partsOfTuple ts vs') = headSizeSum ts :=
            headSizes_partsOfTuple_any ts hvts vs'
          have hhead0 : head0 = encodeTails (partsOfTuple ts vs') ++ tails0 := by
            have hlen : (encodeHeads (headSizeSum ts) (partsOfTuple ts vs')).length =
                headSizeSum ts := by
              rw [length_encodeHeads, hlenH]
            have hd := congrArg (fun x => x.drop (headSizeSum ts)) hsnd.1
            rw [drop_append_of_length hlen] at hd
            rw [← hd, hsnd.2.1]
          simp only [encode, put]
          rw [← encodeParts, encodeParts_unfold, hlenH, hsnd.1, hhead0, hrt, List.append_assoc]
termination_by 8 * sizeOf t
end

end EvmAbi
