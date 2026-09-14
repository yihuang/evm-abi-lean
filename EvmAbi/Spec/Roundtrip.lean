import EvmAbi.Spec

/-!
# EvmAbi.Spec.Roundtrip

The roundtrip family of the linear decoder, in `namespace EvmAbi.Spec`:
every encoding of a valid type decodes back, leaving the suffix untouched.  `decodeElem_roundtrip` owns
the static/dynamic case split (the frontier check is free on encodings, by
the offset correctness theorems of `EvmAbi.Parts`); the element and tuple
walkers (`decodeElems_roundtrip`, `decodeTuple_roundtrip`) thread the
frontier through a run of parts; `decode_roundtrip` is the prefix form.

Split out of the single `EvmAbi.Spec` module so each theorem family is its
own file.  `EvmAbi.Spec.Sound` is the mirror family (the decoder only
produces encodings), `EvmAbi.Spec.Strict` the strict API built on both.
-/

namespace EvmAbi.Spec

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
    decode .bytes buf = some (⟨bs, length_lt_of_decodeBytesPrefix hp⟩, n, buf.drop n) := by
  simp only [decode]
  split <;> grind

/-- `decode` at `string` through known prefix-decode and UTF-8
results. -/
theorem decode_string_pos {buf bs : List UInt8} {n : Nat} {s : String}
    (hp : decodeBytesPrefix buf = some (bs, n))
    (hs : String.fromUTF8? bs.toByteArray = some s) :
    decode .string buf = some (⟨s, size_toUTF8_lt_of_decodeBytesPrefix hp hs⟩, n, buf.drop n) := by
  simp only [decode]
  split
  · next bs' n' hp' =>
      rw [hp] at hp'
      grind
  · next hp' => grind

mutual
/-- **Roundtrip, per-component**: one canonical component reads back from
its head slot — static in place, dynamic through its offset word (which the
frontier check `offset = E` verifies) — and the frontier advances by the
component's tail size. -/
theorem decodeElem_roundtrip (t : Ty) (v : t.Val)
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
      grind [List.length_drop]
    have hr := decode_roundtrip t v (encodeTails zs ++ rest) hb'
    simp only [decodeElem, hs, hnat, if_true]
    rw [show (encodeParts (xs ++ partOf t v :: zs) ++ rest).drop E =
        encode t v ++ (encodeTails zs ++ rest) from by rw [hE, hdropTail]]
    rw [hr]
    dsimp only []
    rw [htailLen, ← List.drop_drop, ← hhead32,
      show (encodeParts (xs ++ partOf t v :: zs) ++ rest).drop (E + (encode t v).length) =
          encodeTails zs ++ rest from by
        rw [hE, ← List.drop_drop, hdropTail]
        exact drop_append_of_length rfl]
  · have hstatic := drop_head_partOf_static t hs v xs zs rest off hoff
    have hlen : (encode t v).length = t.headSize := encode_length_static t hs v
    have htail0 : (partOf t v).tailSize = 0 := tailSize_partOf_static t v hs
    have hb' : (encode t v ++ (encodeHeads (headSizes (xs ++ partOf t v :: zs) + tailSizes xs) zs ++
        (encodeTails (xs ++ partOf t v :: zs) ++ rest))).length < 2 ^ 256 := by
      grind [List.length_drop]
    have hr := decode_roundtrip t v
      (encodeHeads (headSizes (xs ++ partOf t v :: zs) + tailSizes xs) zs ++
        (encodeTails (xs ++ partOf t v :: zs) ++ rest)) hb'
    simp only [decodeElem, hs]
    rw [hstatic, hr, htail0]
    simp only [Nat.add_zero]
    congr 1
    rw [← List.drop_drop, hstatic, drop_append_of_length hlen]
termination_by 8 * sizeOf t + 1

/-- **Roundtrip, element lists**: a run of canonical elements reads back
from their own head/tail layout, the frontier advancing exactly along the
tails. -/
theorem decodeElems_roundtrip (t : Ty) (vs : List t.Val) (k : Nat)
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
      have hoff' : off + t.headSize = headSizes (xs ++ [partOf t w]) := by
        rw [headSizes_snoc_partOf t w xs off hoff]
      have hE' : E + (partOf t w).tailSize =
          tailOffset ((xs ++ [partOf t w]) ++ ws.map (partOf t) ++ ys)
            (xs ++ [partOf t w]).length := by
        rw [← hre]
        rw [tailOffset_snoc (partOf t w) xs (ws.map (partOf t) ++ ys) E hE]
      have helem := decodeElem_roundtrip t w xs (ws.map (partOf t) ++ ys) off hoff E hE rest hwf hb
      rw [helem]
      dsimp only []
      have hih := ih (ws.length) rfl (xs ++ [partOf t w]) (off + t.headSize) hoff'
        (E + (partOf t w).tailSize) hE' (hre ▸ hwf) (hre ▸ hb)
      rw [hre, hih]
      grind [tailSizes, Nat.add_assoc]
termination_by 8 * sizeOf t + 2

/-- **Roundtrip, tuples**: a canonical tuple reads back from its own
head/tail layout. -/
theorem decodeTuple_roundtrip : (ts : List Ty) → (vs : TupleVal ts) →
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
  | [], _, _, _, _, _, _, _, _, _, _ => by
      simp only [partsOfTuple, decodeTuple, Get2.pure_run, tailSizes, Nat.add_zero]
      rfl
  | t :: ts, (v, vs), xs, ys, off, hoff, E, hE, rest, hwf, hb => by
      simp only [partsOfTuple, decodeTuple, Get2.bind_run, Get2.pure_run]
      simp only [partsOfTuple] at hwf hb hE
      simp only [List.append_assoc, List.cons_append] at hwf hb hE ⊢
      have hre : xs ++ (partOf t v :: (partsOfTuple ts vs ++ ys)) =
          ((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys := by
        simp [List.append_assoc]
      have hoff' : off + t.headSize = headSizes (xs ++ [partOf t v]) := by
        rw [headSizes_snoc_partOf t v xs off hoff]
      have hE' : E + (partOf t v).tailSize =
          tailOffset ((xs ++ [partOf t v]) ++ partsOfTuple ts vs ++ ys)
            (xs ++ [partOf t v]).length := by
        rw [← hre]
        rw [tailOffset_snoc (partOf t v) xs (partsOfTuple ts vs ++ ys) E hE]
      have helem := decodeElem_roundtrip t v xs (partsOfTuple ts vs ++ ys) off hoff E hE rest hwf hb
      rw [helem]
      dsimp only []
      have hrec := decodeTuple_roundtrip ts vs (xs ++ [partOf t v]) ys (off + t.headSize) hoff'
        (E + (partOf t v).tailSize) hE' rest (hre ▸ hwf) (hre ▸ hb)
      rw [hre, hrec]
      dsimp only []
      simp only [tailSizes, Nat.add_assoc]
      rfl
termination_by ts => 8 * sizeOf ts + 3

/-- **Roundtrip, prefix form**: every value of a valid type reads back
canonically from the front of its own encoding, reporting its encoding
length as the consumed count and leaving the suffix untouched.  `hb`
bounds the whole buffer (so no offset word wraps); the dynamic payload
bounds are intrinsic to `Val`. -/
theorem decode_roundtrip (t : Ty) (v : t.Val)
    (rest : List UInt8) (hb : (encode t v ++ rest).length < 2 ^ 256) :
    decode t (encode t v ++ rest) = some (v, (encode t v).length, rest) := by
  cases t with
  | uint m =>
      obtain ⟨n, hn⟩ := v
      have hle : m.bits ≤ 256 := by unfold Width.bits; omega
      have hdec : decodeUint (encodeUint n ++ rest) = some n :=
        decodeUint_append n rest
          (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (n := 2) (by decide) hle))
      grind [encode, put, decode, toList_putUint, length_encodeUint]
  | int m =>
      obtain ⟨i, hi⟩ := v
      have h0 : 0 < m.bits := by unfold Width.bits; omega
      have hle : m.bits ≤ 256 := by unfold Width.bits; omega
      have hdec : decodeInt (encodeInt i ++ rest) = some i :=
        decodeInt_append h0 hle hi.1 hi.2 rest
      simp only [encode, put, decode, toList_putInt, hdec, dif_pos hi]
      simp [encodeInt, length_encodeUint]
  | bool =>
      simp only [encode, put, decode, toList_putBool]
      grind [decodeBool_append v rest, encodeBool, length_encodeUint]
  | address =>
      obtain ⟨bs, hbs⟩ := v
      have hdec : decodeAddress (encodeAddress bs ++ rest) = some bs :=
        decodeAddress_append bs rest hbs
      have hlen : (encodeAddress bs).length = 32 := by
        simp [encodeAddress, length_encodeUint]
      simp only [encode, put, decode, toList_putAddress, hdec, dif_pos hbs, hlen,
        drop_append_of_length]
  | bytesN m =>
      obtain ⟨bs, hbs⟩ := v
      have hle : m.bytes ≤ 32 := by unfold Width.bytes; omega
      have hdec : decodeBytesN m.bytes (encodeBytesN bs ++ rest) = some bs :=
        decodeBytesN_append hle hbs rest
      have hlen : (encodeBytesN bs).length = 32 :=
        length_encodeBytesN (by omega)
      simp only [encode, put, decode, toList_putBytesN, hdec, dif_pos hbs, hlen,
        drop_append_of_length]
  | bytes =>
      obtain ⟨bs, hlb⟩ := v
      have hr := decodeBytesPrefix_append (bs := bs) (rest := rest) hlb
      simp only [encode, put, toList_putBytes, decode_bytes_pos hr, drop_append_of_length rfl]
  | string =>
      obtain ⟨s, hlb⟩ := v
      have hb2 : s.toUTF8.data.toList.length < 2 ^ 64 := by
        rw [← Binary.ByteArray.size_eq_toList_length s.toUTF8]
        exact hlb
      have hr := decodeBytesPrefix_append (bs := s.toUTF8.data.toList) (rest := rest) hb2
      have hus : String.fromUTF8? (s.toUTF8.data.toList).toByteArray = some s := by
        rw [dataToList_toByteArray]
        exact fromUTF8?_toUTF8 s
      simp only [encode, put, toList_putString, encodeString, decode_string_pos hr hus,
        drop_append_of_length rfl]
  | array t =>
      obtain ⟨vs, hlk⟩ := v
      have hbT : (encodeParts (vs.map (partOf t)) ++ rest).length < 2 ^ 256 := by
        simp only [encode, put, toList_append, toList_putUint, List.length_append,
          length_encodeUint, encodeParts] at hb ⊢
        omega
      have hlenH : headSizes (vs.map (partOf t)) = vs.length * t.headSize := by
        rw [headSizes_map_partOf_any t vs]
      have hE : vs.length * t.headSize = tailOffset ([] ++ vs.map (partOf t) ++ []) 0 := by
        simp [tailOffset, tailSizes, hlenH]
      have hwalk := decodeElems_roundtrip t vs vs.length rfl [] [] 0 (by simp [headSizes])
        (vs.length * t.headSize) hE rest (by simpa using wf_map_partOf t vs) (by simpa using hbT)
      simp only [List.nil_append, List.append_nil, List.drop_zero] at hwalk
      have hheads : (encodeParts (vs.map (partOf t)) ++ rest).drop (vs.length * t.headSize) =
          encodeTails (vs.map (partOf t)) ++ rest := by
        grind [encodeParts_unfold, List.append_assoc, length_encodeHeads, drop_append_of_length]
      have htails : (encodeParts (vs.map (partOf t)) ++ rest).drop
          (vs.length * t.headSize + tailSizes (vs.map (partOf t))) = rest := by
        grind [encodeParts_unfold, List.append_assoc, length_encodeHeads, length_encodeTails,
          drop_append_of_length, List.drop_drop]
      have hcnt : natAt (encodeUint vs.length ++ (encodeParts (vs.map (partOf t)) ++ rest)) 0 =
          some vs.length := by
        unfold encodeUint
        have hw := natAt_append ([] : List UInt8) (encodeParts (vs.map (partOf t)) ++ rest)
          (UInt256.ofNat vs.length) 0 (by simp)
        rw [List.nil_append] at hw
        rw [hw, UInt256.toNat_ofNat, Nat.mod_eq_of_lt
          (show vs.length < UInt256.size from lt_two_pow_256_of_lt_two_pow_64 hlk)]
      simp only [encode, put, decode, toList_append, toList_putUint, List.append_assoc]
      rw [← encodeParts]
      split
      · next hk' => rw [hcnt] at hk'; contradiction
      · next k hk' =>
          rw [hcnt] at hk'
          obtain rfl := Option.some.inj hk'
          -- the length word is the value's own length, which its type bounds
          rw [dif_pos hlk, ← List.drop_drop,
            show (encodeUint vs.length ++ (encodeParts (vs.map (partOf t)) ++ rest)).drop 32 =
                encodeParts (vs.map (partOf t)) ++ rest from
              drop_append_of_length (length_encodeUint _)]
          rw [hwalk]
          grind [List.length_append, length_encodeUint, length_encodeParts]
  | fixedArray t n _ =>
      obtain ⟨vs, hvs⟩ := v
      have hbT : (encodeParts (vs.map (partOf t)) ++ rest).length < 2 ^ 256 := by
        simp only [encode, put, List.length_append, encodeParts] at hb ⊢
        omega
      have hlenH : headSizes (vs.map (partOf t)) = n * t.headSize := by
        rw [headSizes_map_partOf_any t vs, hvs]
      have hE : n * t.headSize = tailOffset ([] ++ vs.map (partOf t) ++ []) 0 := by
        simp [tailOffset, tailSizes, hlenH]
      have hwalk := decodeElems_roundtrip t vs n hvs [] [] 0 (by simp [headSizes])
        (n * t.headSize) hE rest (by simpa using wf_map_partOf t vs) (by simpa using hbT)
      simp only [List.nil_append, List.append_nil, List.drop_zero] at hwalk
      have hheads : (encodeParts (vs.map (partOf t)) ++ rest).drop (n * t.headSize) =
          encodeTails (vs.map (partOf t)) ++ rest := by
        grind [encodeParts_unfold, List.append_assoc, length_encodeHeads, drop_append_of_length]
      have htails : (encodeParts (vs.map (partOf t)) ++ rest).drop
          (n * t.headSize + tailSizes (vs.map (partOf t))) = rest := by
        grind [encodeParts_unfold, List.append_assoc, length_encodeHeads, length_encodeTails,
          drop_append_of_length, List.drop_drop]
      simp only [encode, put, decode]
      rw [← encodeParts, hwalk]
      grind [length_encodeParts]
  | tuple head tail =>
      obtain ⟨vh, vtail⟩ := v
      have hbT : (encodeParts (partOf head vh :: partsOfTuple tail vtail) ++ rest).length < 2 ^ 256 := by
        simp only [encode, put, List.length_append, encodeParts] at hb ⊢
        omega
      have hlenH : headSizes (partOf head vh :: partsOfTuple tail vtail) =
          head.headSize + headSizeSum tail := by
        simp only [headSizes, headSize_partOf head vh]
        rw [headSizes_partsOfTuple_any tail vtail]
      have hE : head.headSize + headSizeSum tail =
          tailOffset ([] ++ partOf head vh :: partsOfTuple tail vtail) 0 := by
        simp [tailOffset, tailSizes, ← hlenH]
      have hwf : WF (partOf head vh :: partsOfTuple tail vtail) := by
        simpa [partsOfTuple] using wf_partsOfTuple (head :: tail) (vh, vtail)
      have hwalkHead := decodeElem_roundtrip head vh [] (partsOfTuple tail vtail)
        0 (by simp [headSizes]) (head.headSize + headSizeSum tail) hE rest hwf hbT
      simp only [List.nil_append, List.drop_zero] at hwalkHead
      have hE' : (head.headSize + headSizeSum tail) + (partOf head vh).tailSize =
          tailOffset ([partOf head vh] ++ partsOfTuple tail vtail ++ []) 1 := by
        simpa [List.length_append, List.append_assoc] using
          tailOffset_snoc (partOf head vh) [] (partsOfTuple tail vtail)
            (head.headSize + headSizeSum tail) hE
      have hwfTail : WF ([partOf head vh] ++ partsOfTuple tail vtail ++ []) := by
        simpa [List.append_assoc] using hwf
      have hbTail : (encodeParts ([partOf head vh] ++ partsOfTuple tail vtail ++ []) ++ rest).length < 2 ^ 256 := by
        simpa [List.append_assoc] using hbT
      have hwalkTail := decodeTuple_roundtrip tail vtail [partOf head vh] [] head.headSize
        (by simp [headSizes, headSize_partOf head vh])
        ((head.headSize + headSizeSum tail) + (partOf head vh).tailSize) hE' rest hwfTail hbTail
      have hwalkTail' : (decodeTuple tail).run
          (List.drop head.headSize (encodeParts (partOf head vh :: partsOfTuple tail vtail) ++ rest))
          (List.drop (head.headSize + headSizeSum tail + (partOf head vh).tailSize)
            (encodeParts (partOf head vh :: partsOfTuple tail vtail) ++ rest))
          (head.headSize + headSizeSum tail + (partOf head vh).tailSize) =
        some ⟨vtail,
          List.drop (head.headSize + headSizeSum tail)
            (encodeParts (partOf head vh :: partsOfTuple tail vtail) ++ rest),
          List.drop (head.headSize + headSizeSum tail + (partOf head vh).tailSize +
            tailSizes (partsOfTuple tail vtail))
            (encodeParts (partOf head vh :: partsOfTuple tail vtail) ++ rest),
          head.headSize + headSizeSum tail + (partOf head vh).tailSize +
            tailSizes (partsOfTuple tail vtail)⟩ := by
        simpa [List.append_assoc, List.singleton_append] using hwalkTail
      have hheads : (encodeParts (partOf head vh :: partsOfTuple tail vtail) ++ rest).drop
          (head.headSize + headSizeSum tail) =
          encodeTails (partOf head vh :: partsOfTuple tail vtail) ++ rest := by
        grind [encodeParts_unfold, List.append_assoc, length_encodeHeads, drop_append_of_length]
      have htails : (encodeParts (partOf head vh :: partsOfTuple tail vtail) ++ rest).drop
          (head.headSize + headSizeSum tail + tailSizes (partOf head vh :: partsOfTuple tail vtail)) = rest := by
        grind [encodeParts_unfold, List.append_assoc, length_encodeHeads, length_encodeTails,
          drop_append_of_length, List.drop_drop]
      simp only [encode, put, decode]
      rw [← encodeParts, hwalkHead]
      simp
      rw [hwalkTail']
      dsimp only []
      have hoffset : head.headSize + headSizeSum tail + (partOf head vh).tailSize +
          tailSizes (partsOfTuple tail vtail) =
          head.headSize + headSizeSum tail +
            tailSizes (partOf head vh :: partsOfTuple tail vtail) := by
        simp [tailSizes]
        omega
      grind [length_encodeParts]
termination_by 8 * sizeOf t
end

end EvmAbi.Spec
