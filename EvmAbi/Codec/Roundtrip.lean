import EvmAbi.Codec

/-!
# EvmAbi.Codec.Roundtrip

The roundtrip family of the linear decoder: every encoding of a valid type
decodes back, leaving the suffix untouched.  `decodeElem_roundtrip` owns
the static/dynamic case split (the frontier check is free on encodings, by
the offset correctness theorems of `EvmAbi.Parts`); the element and tuple
walkers (`decodeElems_roundtrip`, `decodeTuple_roundtrip`) thread the
frontier through a run of parts; `decode_roundtrip` is the prefix form.

Split out of the single `EvmAbi.Codec` module so each theorem family is its
own file.  `EvmAbi.Codec.Sound` is the mirror family (the decoder only
produces encodings), `EvmAbi.Codec.Strict` the strict API built on both.
-/

namespace EvmAbi

open Ty
open Binary
open Builder

/- ## roundtrip: the linear decoder recovers encodings -/

/- The frontier check is *free* on encodings: the offset word written by
`putParts` for a dynamic component is exactly the frontier, by the offset
correctness theorems of `EvmAbi.Parts`. -/
/-- `decode` at `bytes` through a known prefix-decode result. -/
theorem decode_bytes_pos {buf bs : List UInt8} {n : Nat}
    (hp : decodeBytesPrefix buf = some (bs, n)) :
    decode .bytes buf = some (⟨bs, length_lt_of_decodeBytesPrefix hp⟩, buf.drop n) := by
  simp only [decode]
  split
  · next bs' n' hp' =>
      rw [hp] at hp'
      simp only [Option.some.injEq, Prod.mk.injEq] at hp'
      obtain ⟨rfl, rfl⟩ := hp'
      rfl
  · next hp' => rw [hp] at hp'; contradiction

/-- `decode` at `string` through known prefix-decode and UTF-8
results. -/
theorem decode_string_pos {buf bs : List UInt8} {n : Nat} {s : String}
    (hp : decodeBytesPrefix buf = some (bs, n))
    (hs : String.fromUTF8? bs.toByteArray = some s) :
    decode .string buf = some (⟨s, size_toUTF8_lt_of_decodeBytesPrefix hp hs⟩, buf.drop n) := by
  simp only [decode]
  split
  · next bs' n' hp' =>
      rw [hp] at hp'
      simp only [Option.some.injEq, Prod.mk.injEq] at hp'
      obtain ⟨rfl, rfl⟩ := hp'
      split
      · next s' hs' =>
          rw [hs] at hs'
          obtain rfl := Option.some.inj hs'
          rfl
      · next hs' => rw [hs] at hs'; contradiction
  · next hp' => rw [hp] at hp'; contradiction

mutual
/-- **Roundtrip, per-component**: one canonical component reads back from
its head slot — static in place, dynamic through its offset word (which the
frontier check `offset = E` verifies) — and the frontier advances by the
component's tail size. -/
theorem decodeElem_roundtrip (t : Ty) (hv : t.Valid) (v : t.Val)
    (xs zs : List Part) (off : Nat) (hoff : off = headSizes xs)
    (E : Nat) (hE : E = tailOffset (xs ++ partOf t v :: zs) xs.length)
    (rest : List UInt8)
    (hwf : WF (xs ++ partOf t v :: zs))
    (hb : (encodeParts (xs ++ partOf t v :: zs) ++ rest).length < 2 ^ 256) :
    (decodeElem t).run
      ((encodeParts (xs ++ partOf t v :: zs) ++ rest).drop off)
      ((encodeParts (xs ++ partOf t v :: zs) ++ rest).drop E) E =
    some ⟨v, (encodeParts (xs ++ partOf t v :: zs) ++ rest).drop (off + t.headSize),
          (encodeParts (xs ++ partOf t v :: zs) ++ rest).drop (E + (partOf t v).tailSize),
          E + (partOf t v).tailSize⟩ := by
  cases hs : t.isStatic
  · have hsf : t.isStatic = false := hs
    have hhead32 : t.headSize = 32 := headSize_of_dynamic t hsf
    have htailLen : (partOf t v).tailSize = (encode t v).length := tailSize_partOf_dynamic t v hs
    have hnat0 := natAt_offset_partOf_dynamic t v hsf xs zs rest hwf hb
    have hnat : natAt ((encodeParts (xs ++ partOf t v :: zs) ++ rest).drop off) 0 = some E := by
      have hd : 32 ∣ headSizes xs := dvd_headSizes (fun q hq => hwf q (List.mem_append_left _ hq))
      have hoff32 : headSizes xs = 32 * (headSizes xs / 32) := by
        simpa [Nat.mul_comm] using (Nat.div_mul_cancel hd).symm
      rw [hoff, natAt_drop _ _ _ hoff32, hnat0, hE]
    have hdropTail := drop_tail_partOf_dynamic t v hsf xs zs rest
    have hb' : (encode t v ++ (encodeTails zs ++ rest)).length < 2 ^ 256 := by
      rw [← hdropTail, ← hE]
      rw [List.length_drop]
      omega
    have hr := decode_roundtrip t hv v (encodeTails zs ++ rest) hb'
    unfold decodeElem
    simp only [hs]
    rw [hnat]
    dsimp only []
    simp only [if_true]
    rw [show (encodeParts (xs ++ partOf t v :: zs) ++ rest).drop E =
        encode t v ++ (encodeTails zs ++ rest) from by rw [hE, hdropTail]]
    rw [hr]
    dsimp only []
    rw [htailLen]
    have htlen' : (encode t v ++ (encodeTails zs ++ rest)).length -
        (encodeTails zs ++ rest).length = (encode t v).length := by
      rw [List.length_append, Nat.add_sub_cancel]
    rw [← List.drop_drop, ← hhead32, htlen']
    rw [show (encodeParts (xs ++ partOf t v :: zs) ++ rest).drop (E + (encode t v).length) =
        encodeTails zs ++ rest from by
      rw [hE, ← List.drop_drop, hdropTail]
      exact drop_append_of_length rfl]
  · have hstatic := drop_head_partOf_static t hs v xs zs rest off hoff
    have hlen : (encode t v).length = t.headSize := encode_length_static t hs hv v
    have htail0 : (partOf t v).tailSize = 0 := tailSize_partOf_static t v hs
    have hb' : (encode t v ++ (encodeHeads (headSizes (xs ++ partOf t v :: zs) + tailSizes xs) zs ++
        (encodeTails (xs ++ partOf t v :: zs) ++ rest))).length < 2 ^ 256 := by
      rw [← hstatic]
      rw [List.length_drop]
      omega
    have hr := decode_roundtrip t hv v
      (encodeHeads (headSizes (xs ++ partOf t v :: zs) + tailSizes xs) zs ++
        (encodeTails (xs ++ partOf t v :: zs) ++ rest)) hb'
    simp only [decodeElem, hs]
    rw [hstatic, hr, htail0]
    dsimp only []
    simp only [Nat.add_zero]
    congr 1
    rw [← List.drop_drop, hstatic, drop_append_of_length hlen]
termination_by 8 * sizeOf t + 1

/-- **Roundtrip, element lists**: a run of canonical elements reads back
from their own head/tail layout, the frontier advancing exactly along the
tails. -/
theorem decodeElems_roundtrip (t : Ty) (hv : t.Valid) (vs : List t.Val) (k : Nat)
    (hk : vs.length = k)
    (xs ys : List Part) (off : Nat) (hoff : off = headSizes xs)
    (E : Nat) (hE : E = tailOffset (xs ++ vs.map (partOf t) ++ ys) xs.length)
    (rest : List UInt8)
    (hwf : WF (xs ++ vs.map (partOf t) ++ ys))
    (hb : (encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest).length < 2 ^ 256) :
    (decodeElems t k).run
      ((encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest).drop off)
      ((encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest).drop E) E =
    some ⟨⟨vs, hk⟩,
      (encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest).drop (off + k * t.headSize),
      (encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest).drop (E + tailSizes (vs.map (partOf t))),
      E + tailSizes (vs.map (partOf t))⟩ := by
  induction vs generalizing k xs off E with
  | nil =>
      subst hk
      simp only [List.map_nil, List.length_nil, decodeElems, Get2.pure_run, tailSizes,
        Nat.add_zero, Nat.zero_mul]
  | cons w ws ih =>
      have hk' : k = ws.length + 1 := by rw [← hk, List.length_cons]
      subst hk'
      simp only [List.map_cons, decodeElems, Get2.bind_run, Get2.pure_run]
      simp only [List.map_cons] at hwf hb hE
      simp only [List.append_assoc, List.cons_append] at hwf hb hE ⊢
      have hre : xs ++ (partOf t w :: (ws.map (partOf t) ++ ys)) =
          ((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys := by
        simp [List.append_assoc]
      have hwf' : WF (((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys) := by
        rwa [← hre]
      have hb' : (encodeParts (((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys) ++ rest).length <
          2 ^ 256 := by
        rwa [← hre]
      have hoff' : off + t.headSize = headSizes (xs ++ [partOf t w]) := by
        rw [headSizes_snoc_partOf t hv w xs off hoff]
      have hE' : E + (partOf t w).tailSize =
          tailOffset ((xs ++ [partOf t w]) ++ ws.map (partOf t) ++ ys)
            (xs ++ [partOf t w]).length := by
        rw [← hre]
        rw [tailOffset_snoc (partOf t w) xs (ws.map (partOf t) ++ ys) E hE]
      have helem := decodeElem_roundtrip t hv w xs (ws.map (partOf t) ++ ys) off hoff E hE rest hwf hb
      rw [helem]
      dsimp only []
      rw [hre,
        ih (ws.length) rfl (xs ++ [partOf t w]) (off + t.headSize) hoff'
          (E + (partOf t w).tailSize) hE' hwf' hb']
      dsimp only []
      simp only [Option.some.injEq]
      apply Get2.Result.ext
      · apply Subtype.ext
        rfl
      · rw [show off + t.headSize + ws.length * t.headSize =
            off + (ws.length + 1) * t.headSize from by
          rw [Nat.add_mul, Nat.one_mul]
          ac_rfl]
      · rw [show E + (partOf t w).tailSize + tailSizes (List.map (partOf t) ws) =
            E + tailSizes (partOf t w :: List.map (partOf t) ws) from by
          simp [tailSizes, Nat.add_assoc]]
      · rw [show E + (partOf t w).tailSize + tailSizes (List.map (partOf t) ws) =
            E + tailSizes (partOf t w :: List.map (partOf t) ws) from by
          simp [tailSizes, Nat.add_assoc]]
termination_by 8 * sizeOf t + 2

/-- **Roundtrip, tuples**: a canonical tuple reads back from its own
head/tail layout. -/
theorem decodeTuple_roundtrip : (ts : List Ty) → AllValid ts → (vs : TupleVal ts) →
    (xs ys : List Part) → (off : Nat) → off = headSizes xs →
    (E : Nat) → E = tailOffset (xs ++ partsOfTuple ts vs ++ ys) xs.length →
    (rest : List UInt8) → WF (xs ++ partsOfTuple ts vs ++ ys) →
    (encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest).length < 2 ^ 256 →
    (decodeTuple ts).run
      ((encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest).drop off)
      ((encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest).drop E) E =
    some ⟨vs,
      (encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest).drop (off + headSizeSum ts),
      (encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest).drop (E + tailSizes (partsOfTuple ts vs)),
      E + tailSizes (partsOfTuple ts vs)⟩
  | [], _, _, _, _, _, _, _, _, _, _, _ => by
      simp only [partsOfTuple, decodeTuple, Get2.pure_run, tailSizes, Nat.add_zero]
      rfl
  | t :: ts, hv, (v, vs), xs, ys, off, hoff, E, hE, rest, hwf, hb => by
      obtain ⟨hvt, hvs⟩ := hv
      simp only [partsOfTuple, decodeTuple, Get2.bind_run, Get2.pure_run]
      simp only [partsOfTuple] at hwf hb hE
      simp only [List.append_assoc, List.cons_append] at hwf hb hE ⊢
      have hre : xs ++ (partOf t v :: (partsOfTuple ts vs ++ ys)) =
          ((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys := by
        simp [List.append_assoc]
      have hwf' : WF (((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys) := by
        rwa [← hre]
      have hb' : (encodeParts (((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys) ++ rest).length <
          2 ^ 256 := by
        rwa [← hre]
      have hoff' : off + t.headSize = headSizes (xs ++ [partOf t v]) := by
        rw [headSizes_snoc_partOf t hvt v xs off hoff]
      have hE' : E + (partOf t v).tailSize =
          tailOffset ((xs ++ [partOf t v]) ++ partsOfTuple ts vs ++ ys)
            (xs ++ [partOf t v]).length := by
        rw [← hre]
        rw [tailOffset_snoc (partOf t v) xs (partsOfTuple ts vs ++ ys) E hE]
      have helem := decodeElem_roundtrip t hvt v xs (partsOfTuple ts vs ++ ys) off hoff E hE rest hwf hb
      rw [helem]
      dsimp only []
      rw [hre,
        decodeTuple_roundtrip ts hvs vs (xs ++ [partOf t v]) ys (off + t.headSize) hoff'
          (E + (partOf t v).tailSize) hE' rest hwf' hb']
      dsimp only []
      simp only [tailSizes, Nat.add_assoc]
      rfl
termination_by ts => 8 * sizeOf ts + 3

/-- **Roundtrip, prefix form**: every value of a valid type reads back
canonically from the front of its own encoding, leaving the suffix
touched.  `hb` bounds the whole buffer (so no offset word wraps); the
dynamic payload bounds are intrinsic to `Val`. -/
theorem decode_roundtrip (t : Ty) (hv : t.Valid) (v : t.Val)
    (rest : List UInt8) (hb : (encode t v ++ rest).length < 2 ^ 256) :
    decode t (encode t v ++ rest) = some (v, rest) := by
  cases t with
  | uint m =>
      obtain ⟨n, hn⟩ := v
      have hdec : decodeUint (encodeUint n ++ rest) = some n :=
        decodeUint_append n rest
          (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (n := 2) (by decide) hv.2.1))
      simp only [encode, put, decode, toList_putUint]
      rw [hdec]
      dsimp only []
      rw [dif_pos hn]
      simp [length_encodeUint]
  | int m =>
      obtain ⟨i, hi⟩ := v
      have h0 : 0 < m := by have h8 := hv.1; omega
      have hdec : decodeInt (encodeInt i ++ rest) = some i :=
        decodeInt_append h0 hv.2.1 hi.1 hi.2 rest
      simp only [encode, put, decode, toList_putInt]
      rw [hdec]
      dsimp only []
      rw [dif_pos hi]
      simp [encodeInt, length_encodeUint]
  | bool =>
      simp only [encode, put, decode, toList_putBool]
      rw [decodeBool_append v rest]
      simp [encodeBool, length_encodeUint]
  | address =>
      obtain ⟨n, hn⟩ := v
      have hdec : decodeAddress (encodeAddress n ++ rest) = some n :=
        decodeAddress_append n rest hn
      simp only [encode, put, decode, toList_putAddress]
      rw [hdec]
      dsimp only []
      rw [dif_pos hn]
      simp [encodeAddress, length_encodeUint]
  | bytesN m =>
      obtain ⟨bs, hbs⟩ := v
      have hdec : decodeBytesN m (encodeBytesN bs ++ rest) = some bs :=
        decodeBytesN_append hv.2 hbs rest
      have hlen : (encodeBytesN bs).length = 32 :=
        length_encodeBytesN (by rw [hbs]; exact hv.2)
      simp only [encode, put, decode, toList_putBytesN]
      rw [hdec]
      dsimp only []
      rw [dif_pos hbs]
      rw [show (encodeBytesN bs ++ rest).drop 32 = rest from drop_append_of_length hlen]
  | bytes =>
      obtain ⟨bs, hlb⟩ := v
      have hr := decodeBytesPrefix_append (bs := bs) (rest := rest) hlb
      simp only [encode, put, toList_putBytes]
      rw [decode_bytes_pos hr]
      rw [drop_append_of_length rfl]
  | string =>
      obtain ⟨s, hlb⟩ := v
      have hb2 : s.toUTF8.data.toList.length < 2 ^ 256 := by
        rw [← Binary.ByteArray.size_eq_toList_length s.toUTF8]
        exact hlb
      have hr := decodeBytesPrefix_append (bs := s.toUTF8.data.toList) (rest := rest) hb2
      have hus : String.fromUTF8? (s.toUTF8.data.toList).toByteArray = some s := by
        rw [dataToList_toByteArray]
        exact fromUTF8?_toUTF8 s
      simp only [encode, put, toList_putString, encodeString]
      rw [decode_string_pos hr hus]
      rw [drop_append_of_length rfl]
  | array t =>
      obtain ⟨vs, hlk⟩ := v
      have hvt : t.Valid := hv
      have hbT : (encodeParts (vs.map (partOf t)) ++ rest).length < 2 ^ 256 := by
        have hb' := hb
        simp only [encode, put, toList_append, toList_putUint, List.length_append,
          length_encodeUint] at hb'
        simp only [encodeParts, List.length_append]
        omega
      have hlenH : headSizes (vs.map (partOf t)) = vs.length * t.headSize := by
        rw [headSizes_map_partOf_any t hvt vs]
      have hE : vs.length * t.headSize = tailOffset ([] ++ vs.map (partOf t) ++ []) 0 := by
        simp [tailOffset, tailSizes, hlenH]
      have hwalk := decodeElems_roundtrip t hvt vs vs.length rfl [] [] 0 (by simp [headSizes])
        (vs.length * t.headSize) hE rest (by simpa using wf_map_partOf t hvt vs) (by simpa using hbT)
      simp only [List.nil_append, List.append_nil, List.drop_zero] at hwalk
      have hheads : (encodeParts (vs.map (partOf t)) ++ rest).drop (vs.length * t.headSize) =
          encodeTails (vs.map (partOf t)) ++ rest := by
        rw [encodeParts_unfold, List.append_assoc, ← hlenH,
          drop_append_of_length (length_encodeHeads _ _)]
      have htails : (encodeParts (vs.map (partOf t)) ++ rest).drop
          (vs.length * t.headSize + tailSizes (vs.map (partOf t))) = rest := by
        rw [encodeParts_unfold, ← List.drop_drop, List.append_assoc, ← hlenH]
        rw [drop_append_of_length (length_encodeHeads _ _)]
        rw [drop_append_of_length (length_encodeTails _)]
      have hcnt : natAt (encodeUint vs.length ++ (encodeParts (vs.map (partOf t)) ++ rest)) 0 =
          some vs.length := by
        unfold encodeUint
        have hw := natAt_append ([] : List UInt8) (encodeParts (vs.map (partOf t)) ++ rest)
          (UInt256.ofNat vs.length) 0 (by simp)
        rw [List.nil_append] at hw
        rw [hw, UInt256.toNat_ofNat, Nat.mod_eq_of_lt
          (show vs.length < UInt256.size from hlk)]
      simp only [encode, put, decode, toList_append, toList_putUint, List.append_assoc]
      rw [← encodeParts]
      split
      · next hk' => rw [hcnt] at hk'; contradiction
      · next k hk' =>
          rw [hcnt] at hk'
          obtain rfl := Option.some.inj hk'
          rw [← List.drop_drop]
          rw [show (encodeUint vs.length ++ (encodeParts (vs.map (partOf t)) ++ rest)).drop 32 =
              encodeParts (vs.map (partOf t)) ++ rest from drop_append_of_length (length_encodeUint _)]
          rw [hwalk]
          dsimp only []
          rw [htails]
  | fixedArray t n =>
      obtain ⟨vs, hvs⟩ := v
      have hvt : t.Valid := hv
      have hbT : (encodeParts (vs.map (partOf t)) ++ rest).length < 2 ^ 256 := by
        have hb' := hb
        simp only [encode, put, List.length_append] at hb'
        simp only [encodeParts, List.length_append]
        omega
      have hlenH : headSizes (vs.map (partOf t)) = n * t.headSize := by
        rw [headSizes_map_partOf_any t hvt vs, hvs]
      have hE : n * t.headSize = tailOffset ([] ++ vs.map (partOf t) ++ []) 0 := by
        simp [tailOffset, tailSizes, hlenH]
      have hwalk := decodeElems_roundtrip t hvt vs n hvs [] [] 0 (by simp [headSizes])
        (n * t.headSize) hE rest (by simpa using wf_map_partOf t hvt vs) (by simpa using hbT)
      simp only [List.nil_append, List.append_nil, List.drop_zero] at hwalk
      have hheads : (encodeParts (vs.map (partOf t)) ++ rest).drop (n * t.headSize) =
          encodeTails (vs.map (partOf t)) ++ rest := by
        rw [encodeParts_unfold, List.append_assoc, ← hlenH,
          drop_append_of_length (length_encodeHeads _ _)]
      have htails : (encodeParts (vs.map (partOf t)) ++ rest).drop
          (n * t.headSize + tailSizes (vs.map (partOf t))) = rest := by
        rw [encodeParts_unfold, ← List.drop_drop, List.append_assoc, ← hlenH]
        rw [drop_append_of_length (length_encodeHeads _ _)]
        rw [drop_append_of_length (length_encodeTails _)]
      simp only [encode, put, decode]
      rw [← encodeParts]
      rw [hwalk]
      dsimp only []
      rw [htails]
  | tuple ts =>
      have hvts : AllValid ts := hv
      have hbT : (encodeParts (partsOfTuple ts v) ++ rest).length < 2 ^ 256 := by
        have hb' := hb
        simp only [encode, put, List.length_append] at hb'
        simp only [encodeParts, List.length_append]
        omega
      have hlenH : headSizes (partsOfTuple ts v) = headSizeSum ts := by
        rw [headSizes_partsOfTuple_any ts hvts v]
      have hE : headSizeSum ts = tailOffset ([] ++ partsOfTuple ts v ++ []) 0 := by
        simp [tailOffset, tailSizes, ← hlenH]
      have hwalk := decodeTuple_roundtrip ts hvts v [] [] 0 (by simp [headSizes])
        (headSizeSum ts) hE rest (by simpa using wf_partsOfTuple ts hvts v) (by simpa using hbT)
      simp only [List.nil_append, List.append_nil, List.drop_zero] at hwalk
      have hheads : (encodeParts (partsOfTuple ts v) ++ rest).drop (headSizeSum ts) =
          encodeTails (partsOfTuple ts v) ++ rest := by
        rw [encodeParts_unfold, List.append_assoc, ← hlenH,
          drop_append_of_length (length_encodeHeads _ _)]
      have htails : (encodeParts (partsOfTuple ts v) ++ rest).drop
          (headSizeSum ts + tailSizes (partsOfTuple ts v)) = rest := by
        rw [encodeParts_unfold, ← List.drop_drop, List.append_assoc, ← hlenH]
        rw [drop_append_of_length (length_encodeHeads _ _)]
        rw [drop_append_of_length (length_encodeTails _)]
      simp only [encode, put, decode]
      rw [← encodeParts]
      rw [hwalk]
      dsimp only []
      rw [htails]
termination_by 8 * sizeOf t
end

end EvmAbi
