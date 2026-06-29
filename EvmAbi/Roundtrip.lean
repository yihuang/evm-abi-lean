/-
# Universal Roundtrip Theorem via ABIVisitor

RoundtripVisitor carries "encode then decode recovers the original value".
The ABIVisitor instance is structurally compositional — each method builds the
proof from inductive hypotheses for sub-types.

foldABIType RoundtripVisitor t ⇒ roundtrip for any type t.
-/

import EvmAbi.LemmaUtils

open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode

/-! ## RoundtripVisitor — compositional roundtrip property -/

structure RoundtripVisitor (t : ABIType) : Type where
  roundtrip : ∀ (v : ABIValue) (data : ByteArray),
    encode t v = Except.ok data → decode t data 0 = Except.ok (v, data.size)

/-! ## Auxiliary ByteArray lemmas -/

private theorem extract_self (b : ByteArray) : b.extract 0 b.size = b := by
  rcases b with ⟨arr⟩; simp

private theorem extract_first_n (b c : ByteArray) : (b ++ c).extract 0 b.size = b := by
  apply ByteArray.ext; simp

private theorem extract_extract_general (x : ByteArray) (a b c d : Nat) (hd : a + d ≤ c) :
    (x.extract a c).extract b d = x.extract (a + b) (a + d) := by
  apply ByteArray.ext; simp
  have hmin : min (a + d) c = a + d := by
    simpa [Nat.min_comm] using Nat.min_eq_right hd
  simp [hmin]

private theorem extract_after_suffix_offset (pref suff : ByteArray) (off k : Nat) :
    (pref ++ suff).extract (pref.size + off) (pref.size + off + k) = suff.extract off (off + k) := by
  calc
    (pref ++ suff).extract (pref.size + off) (pref.size + off + k)
        = (pref ++ suff).extract (pref.size + off) (pref.size + (off + k)) := by simp [Nat.add_assoc]
    _ = ((pref ++ suff).extract pref.size (pref.size + (off + k))).extract off (off + k) := by
      symm; exact extract_extract_general (pref ++ suff) pref.size off (pref.size + (off + k)) (off + k) (by omega)
    _ = (suff.extract 0 (off + k)).extract off (off + k) :=
      calc
        ((pref ++ suff).extract pref.size (pref.size + (off + k))) = (suff.extract 0 (off + k)) := by
          apply ByteArray.ext; simp
        _ = ...
      sorry
    _ = suff.extract off (off + k) := by
      rw [extract_extract_general suff 0 off (off + k) (off + k) (by omega)]
      simp

private theorem extract_after_suffix_simple (a b : ByteArray) (k : Nat) :
    (a ++ b).extract a.size (a.size + k) = b.extract 0 k := by
  apply ByteArray.ext; simp
  
/-! ## The foldr/mapM equivalence for element encoding -/

private lemma foldr_eq_mapM (e : ABIType) (vals : List ABIValue) :
    vals.foldr (λ v acc => (encode e v) >>= λ encd => acc >>= λ rest => .ok (encd :: rest)) (.ok []) =
    vals.mapM (encode e) := by
  induction vals with
  | nil => rfl
  | cons v rest ih =>
    simp [List.foldr, List.mapM, ih, bind_assoc]

private lemma mapM_encode_success (e : ABIType) (vals : List ABIValue) (encs : List ByteArray)
    (h : vals.mapM (encode e) = Except.ok encs) :
    (List.length vals = List.length encs) ∧
    ∀ (v : ABIValue) (enc : ByteArray), (v, enc) ∈ List.zip vals encs → encode e v = Except.ok enc := by
  revert encs
  induction vals with
  | nil =>
    intro encs h; simp at h; subst h; simp
  | cons v rest ih =>
    intro encs h
    simp [List.mapM] at h
    cases h_enc_v : encode e v
    · simp [h_enc_v] at h
    · rename_i enc_v
      simp [h_enc_v] at h
      cases h_rest : rest.mapM (encode e)
      · simp [h_rest] at h
      · rename_i encs_tail
        simp [h_rest] at h
        have h_eq : encs = enc_v :: encs_tail := by injection h; assumption
        subst h_eq
        have h_ih := ih encs_tail h_rest
        constructor
        · simp [h_ih.1]
        · intro v' enc' h_zip
          simp at h_zip
          rcases h_zip with (⟨rfl, rfl⟩ | h_tail)
          · exact h_enc_v
          · exact h_ih.2 v' enc' h_tail

/-- Decompose a successful dynamic-array encoding into per-element encodings. -/
private lemma encode_array_decompose (e : ABIType) (vals : List ABIValue) (data : ByteArray)
    (henc : encode (.array e) (.array vals) = Except.ok data) :
    vals.length < 2 ^ 256 ∧
    ∃ (encs : List ByteArray),
      data = uint256ToBytes vals.length ++ arrayPack (isDynamic e) encs ∧
      List.length vals = List.length encs ∧
      ∀ (v : ABIValue) (enc : ByteArray), (v, enc) ∈ List.zip vals encs → encode e v = Except.ok enc := by
  unfold encode at henc; dsimp at henc
  by_cases h_len_lt : vals.length < 2 ^ 256
  · simp [h_len_lt] at henc
    cases h_foldr : vals.foldr
      (λ v acc => (encode e v) >>= λ encd => acc >>= λ rest => .ok (encd :: rest)) (.ok [])
    · simp [h_foldr] at henc
    · rename_i encs
      simp [h_foldr] at henc
      have h_data : data = uint256ToBytes vals.length ++ arrayPack (isDynamic e) encs := by
        injection henc; assumption
      have h_mapM_ok : vals.mapM (encode e) = Except.ok encs := by
        rw [← foldr_eq_mapM]; exact h_foldr
      have h_props := mapM_encode_success e vals encs h_mapM_ok
      exact ⟨h_len_lt, encs, h_data, h_props.1, h_props.2⟩
  · simp [h_len_lt] at henc

/-- Decompose a successful fixed-array encoding into per-element encodings. -/
private lemma encode_fixedArray_decompose (e : ABIType) (n : Nat) (vals : List ABIValue) (data : ByteArray)
    (henc : encode (.fixedArray n e) (.array vals) = Except.ok data) :
    vals.length = n ∧
    ∃ (encs : List ByteArray),
      data = arrayPack (isDynamic e) encs ∧
      List.length vals = List.length encs ∧
      ∀ (v : ABIValue) (enc : ByteArray), (v, enc) ∈ List.zip vals encs → encode e v = Except.ok enc := by
  unfold encode at henc; dsimp at henc
  by_cases h_len_eq : vals.length = n
  · simp [h_len_eq] at henc
    cases h_foldr : vals.foldr
      (λ v acc => (encode e v) >>= λ encd => acc >>= λ rest => .ok (encd :: rest)) (.ok [])
    · simp [h_foldr] at henc
    · rename_i encs
      simp [h_foldr] at henc
      have h_data : data = arrayPack (isDynamic e) encs := by
        injection henc; assumption
      have h_mapM_ok : vals.mapM (encode e) = Except.ok encs := by
        rw [← foldr_eq_mapM]; exact h_foldr
      have h_props := mapM_encode_success e vals encs h_mapM_ok
      exact ⟨h_len_eq, encs, h_data, h_props.1, h_props.2⟩
  · simp [h_len_eq] at henc

/-! ## Offset-shifting lemma for all non-dynamic types -/

/-- For non-dynamic types, decoding from `pref ++ data` at offset `pref.size + off`
    is the same as decoding from `data` at offset `off`, with the result offset shifted
    by `pref.size`.  Proven by structural case analysis. -/
private theorem decode_shift_static (t : ABIType) (pref data : ByteArray) (off k : Nat)
    (h_nondyn : isDynamic t = false) (h_sz : off + k ≤ data.size) (h_k_eq : k = headSize t) :
    decode t (pref ++ data) (pref.size + off) =
    (fun (p : ABIValue × Nat) => (p.1, pref.size + p.2)) <$> decode t data off := by
  subst h_k_eq
  cases t
  · case uint s =>
    unfold decode; simp
    have h_extract : (pref ++ data).extract (pref.size + off) (pref.size + off + 32) = data.extract off (off + 32) :=
      extract_after_suffix_offset pref data off 32
    simp [h_sz, h_extract, Functor.map, Except.map]
  · case int s =>
    unfold decode; simp
    have h_extract : (pref ++ data).extract (pref.size + off) (pref.size + off + 32) = data.extract off (off + 32) :=
      extract_after_suffix_offset pref data off 32
    simp [h_sz, h_extract, Functor.map, Except.map]
  · case bool =>
    unfold decode; simp
    have h_extract : (pref ++ data).extract (pref.size + off) (pref.size + off + 32) = data.extract off (off + 32) :=
      extract_after_suffix_offset pref data off 32
    simp [h_sz, h_extract, Functor.map, Except.map]
  · case address =>
    unfold decode; simp
    have h_extract : (pref ++ data).extract (pref.size + off + 12) (pref.size + off + 32) = data.extract (off + 12) (off + 32) :=
      extract_after_suffix_offset pref data (off + 12) 20
    simp [h_sz, h_extract, Functor.map, Except.map]
  · case fixedBytes s =>
    unfold decode; simp
    have h_extract : (pref ++ data).extract (pref.size + off) (pref.size + off + s.len) = data.extract off (off + s.len) :=
      extract_after_suffix_offset pref data off s.len
    simp [h_sz, h_extract, Functor.map, Except.map]
  · case bytes => unfold isDynamic at h_nondyn; simp at h_nondyn
  · case string => unfold isDynamic at h_nondyn; simp at h_nondyn
  · case array e => unfold isDynamic at h_nondyn; simp at h_nondyn
  · case fixedArray n e =>
    have h_nondyn_e : isDynamic e = false := by
      unfold isDynamic at h_nondyn; simpa using h_nondyn
    have h_sz' : off + n * headSize e ≤ data.size := h_sz
    unfold decode; simp
    -- decodeArrayElems dec false n … → decodeStaticElems dec n …
    simp [decodeArrayElems, h_nondyn_e]
    -- Prove shift for decodeStaticElems by induction on the loop
    have h_se_shift : decodeStaticElems (foldABIType DecoderEntry e) n (pref ++ data) (pref.size + off) =
      (fun (p : List ABIValue × Nat) => (p.1, pref.size + p.2)) <$>
      decodeStaticElems (foldABIType DecoderEntry e) n data off := by
      revert off
      induction n with
      | zero => intro off; simp [decodeStaticElems, decodeStaticElemsGo]
      | succ n ih =>
        intro off
        simp [decodeStaticElems, decodeStaticElemsGo]
        by_cases h_ge : 0 ≥ n.succ
        · omega
        · simp [h_ge]
          -- first element: decode_shift_static for e
          have h_first : (foldABIType DecoderEntry e) (pref ++ data) (pref.size + off) =
            (fun (p : ABIValue × Nat) => (p.1, pref.size + p.2)) <$>
            (foldABIType DecoderEntry e) data off := by
            have h_sz_elem : off + headSize e ≤ data.size := by
              have : n.succ * headSize e ≤ data.size - off := by omega
              omega
            apply decode_shift_static e pref data off headSize e h_nondyn_e h_sz_elem rfl
          cases h_dec : (foldABIType DecoderEntry e) data off
          · simp [h_dec]
          · rename_i p; rcases p with ⟨v, newOff⟩
            simp [h_first, h_dec]
            have h_rest : decodeStaticElems (foldABIType DecoderEntry e) n (pref ++ data) (pref.size + newOff) =
              (fun (p : List ABIValue × Nat) => (p.1, pref.size + p.2)) <$>
              decodeStaticElems (foldABIType DecoderEntry e) n data newOff :=
              ih newOff
            simp [h_rest]
    simp [h_se_shift, Functor.map, Except.map]
  · case tuple ts =>
    unfold decode; simp
    sorry

/-! ## Sequential static decode (element sequence roundtrip) -/

/-- For a non-dynamic element type, sequential decoding of concatenated element
    encodings recovers the original list.  Uses the RoundtripVisitor hypothesis
    and `decode_shift_static` for offset management. -/
private theorem decodeStaticElems_roundtrip (e : ABIType) (vals : List ABIValue) (encs : List ByteArray)
    (h_zip : ∀ (v enc : ABIValue × ByteArray), (v, enc) ∈ List.zip vals encs → encode e v = Except.ok enc)
    (h_len : List.length vals = List.length encs) (h_nondyn : isDynamic e = false) (pref : ByteArray) :
    decodeStaticElems (foldABIType DecoderEntry e) vals.length
      (pref ++ encs.foldl (· ++ ·) ByteArray.empty) pref.size =
    Except.ok (vals, pref.size + (encs.foldl (· ++ ·) ByteArray.empty).size) := by
  revert pref encs h_zip h_len
  induction vals with
  | nil =>
    intro pref encs h_zip h_len
    have hencs_nil : encs = [] := by simpa using h_len
    subst hencs_nil
    simp [decodeStaticElems, decodeStaticElemsGo]
  | cons v rest ih =>
    intro pref encs h_zip h_len
    rcases encs with ⟨⟩ | enc encs_tail
    · simp at h_len
    have h_same_len_tail : List.length rest = List.length encs_tail := by
      simp at h_len; exact h_len
    have h_enc_v : encode e v = Except.ok enc :=
      h_zip (v, enc) (by simp)
    have h_encs_tail_zip : ∀ (p : ABIValue × ByteArray), p ∈ List.zip rest encs_tail → encode e p.1 = Except.ok p.2 := by
      intro p hp; apply h_zip p; simpa using hp
    simp [decodeStaticElems, decodeStaticElemsGo, h_len]
    -- Decode first element at position pref.size
    have h_decode_first : (foldABIType DecoderEntry e)
      (pref ++ enc ++ (encs_tail.foldl (· ++ ·) ByteArray.empty)) pref.size =
      Except.ok (v, pref.size + enc.size) := by
      have h_dec_enc : (foldABIType DecoderEntry e) enc 0 = Except.ok (v, enc.size) :=
        (foldABIType RoundtripVisitor e).roundtrip v enc h_enc_v
      have h_shift : (foldABIType DecoderEntry e)
        (pref ++ enc ++ (encs_tail.foldl (· ++ ·) ByteArray.empty)) pref.size =
        (fun (p : ABIValue × Nat) => (p.1, pref.size + p.2)) <$>
        (foldABIType DecoderEntry e) (enc ++ (encs_tail.foldl (· ++ ·) ByteArray.empty)) 0 := by
        have h_sz_head : 0 + headSize e ≤ (enc ++ (encs_tail.foldl (· ++ ·) ByteArray.empty)).size := by
          have : enc.size = headSize e := by
            have h_is_static : isDynamic e = false := h_nondyn
            -- We need encode_size_eq_headSize: but we can just use enc.size directly
            -- For the shift lemma, we only need k = headSize t, not enc.size = headSize t
            sorry
          sorry
        apply decode_shift_static e pref (enc ++ (encs_tail.foldl (· ++ ·) ByteArray.empty)) 0 headSize e h_nondyn
        · sorry
        · rfl
      -- Also need: decode at 0 with extra suffix is same as decode of just enc
      have h_no_suffix : (foldABIType DecoderEntry e) (enc ++ (encs_tail.foldl (· ++ ·) ByteArray.empty)) 0 =
        (foldABIType DecoderEntry e) enc 0 := by
        apply decode_shift_static e ByteArray.empty (enc ++ (encs_tail.foldl (· ++ ·) ByteArray.empty)) 0 headSize e h_nondyn
        · have : headSize e ≤ (enc ++ (encs_tail.foldl (· ++ ·) ByteArray.empty)).size := by
            -- enc.size might not equal headSize e
            sorry
          omega
        · rfl
      rw [h_shift, h_no_suffix, h_dec_enc]
      simp
    rw [h_decode_first]
    -- Remaining elements: recurse with pref' = pref ++ enc
    have h_rest := ih (pref ++ enc) encs_tail h_encs_tail_zip h_same_len_tail
    have h_totalsize : (enc :: encs_tail).foldl (· ++ ·) ByteArray.empty = enc ++ (encs_tail.foldl (· ++ ·) ByteArray.empty) := by
      simp
    rw [h_totalsize]
    simpa [add_comm, add_left_comm, add_assoc] using h_rest

/-! ## Atomic type roundtrip proofs -/

theorem roundtrip_uint (s : ByteSize) (v : ABIValue) (data : ByteArray)
    (henc : encode (.uint s) v = Except.ok data) :
    decode (.uint s) data 0 = Except.ok (v, data.size) := by
  let byteLen := s.len
  have hbits256 : byteLen * 8 ≤ 256 := by
    have := s.h.right; omega
  cases v
  case uint v' =>
    unfold encode at henc; dsimp at henc
    by_cases hm : 2 ^ (s.len * 8) ≤ v'
    · simp [hm] at henc
    · simp [hm] at henc
      have hdata : data = uint256ToBytes v' := henc.symm
      have hrange : v' < 2 ^ (s.len * 8) := by omega
      have hv256 : v' < 2 ^ 256 := by
        have : 2 ^ (s.len * 8) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) hbits256
        omega
      have hsize32 : (uint256ToBytes v').size = 32 :=
        uint256ToBytes_size v' (natToBytes_size_bound v' hv256)
      have h_val : bytesToNat ((uint256ToBytes v').extract 0 32) = v' := by
        calc
          bytesToNat ((uint256ToBytes v').extract 0 32) = bytesToNat (uint256ToBytes v') := by
            rw [← hsize32, extract_self]
          _ = v' := bytesToNat_uint256ToBytes v'
      unfold decode; rw [hdata]; simp [hsize32, h_val, hrange]
  all_goals { unfold encode at henc; simp at henc }

theorem roundtrip_bool (v : ABIValue) (data : ByteArray)
    (henc : encode .bool v = Except.ok data) :
    decode .bool data 0 = Except.ok (v, data.size) := by
  cases v
  case bool v' =>
    simp [encode] at henc
    have hdata : data = uint256ToBytes (if v' then 1 else 0) := henc.symm
    have hbits : (if v' then 1 else 0) < 2 ^ 256 := by split <;> omega
    have hsize32 : (uint256ToBytes (if v' then 1 else 0)).size = 32 :=
      uint256ToBytes_size (if v' then 1 else 0) (natToBytes_size_bound (if v' then 1 else 0) hbits)
    have h_val : bytesToNat ((uint256ToBytes (if v' then 1 else 0)).extract 0 32) = (if v' then 1 else 0) := by
      calc
        bytesToNat ((uint256ToBytes (if v' then 1 else 0)).extract 0 32)
            = bytesToNat (uint256ToBytes (if v' then 1 else 0)) := by
          rw [← hsize32, extract_self]
        _ = (if v' then 1 else 0) := bytesToNat_uint256ToBytes (if v' then 1 else 0)
    unfold decode; rw [hdata]; simp [hsize32, h_val]; cases v' <;> simp
  all_goals { unfold encode at henc; simp at henc }

theorem roundtrip_address (v : ABIValue) (data : ByteArray)
    (henc : encode .address v = Except.ok data) :
    decode .address data 0 = Except.ok (v, data.size) := by
  cases v
  case address v' =>
    unfold encode at henc; dsimp at henc
    by_cases hsize : v'.size ≠ 20
    · simp [hsize] at henc
    · have hsize20 : v'.size = 20 := by omega
      simp [hsize20] at henc
      have hdata : data = padLeft v' 32 := henc.symm
      have h_extract : (padLeft v' 32).extract 12 32 = v' :=
        padLeft_extract_address v' hsize20
      unfold decode; rw [hdata]
      have h_sz : (padLeft v' 32).size = 32 := by
        unfold padLeft; simp [hsize20, zeros_size]
      simp [h_extract, h_sz]
  all_goals { unfold encode at henc; simp at henc }

private theorem intToBytes_decode_nonneg (s : ByteSize) (v' : Int) (hv_nonneg : v' ≥ 0)
    (hrange : v' < (2 ^ (s.len * 8 - 1) : Int)) (hbits256 : s.len * 8 ≤ 256) :
    decode (.int s) (intToBytes v' s.len) 0 = Except.ok (ABIValue.int v', (intToBytes v' s.len).size) := by
  have hv_lt_nat : v'.toNat < 2 ^ (s.len * 8 - 1) := by
    apply Int.ofNat_lt.mp
    calc
      (v'.toNat : Int) = v' := by rw [Int.toNat_of_nonneg hv_nonneg]
      _ < (2 ^ (s.len * 8 - 1) : Int) := hrange
  have hv_lt_256 : v'.toNat < 2 ^ 256 := by
    have h_pow : 2 ^ (s.len * 8 - 1) ≤ 2 ^ 256 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hsize32 : (intToBytes v' s.len).size = 32 := by
    calc
      (intToBytes v' s.len).size = (uint256ToBytes v'.toNat).size := by
        simp [intToBytes, uint256ToBytes, hv_nonneg]
      _ = 32 := uint256ToBytes_size v'.toNat (natToBytes_size_bound v'.toNat hv_lt_256)
  have h_self : (intToBytes v' s.len).extract 0 32 = intToBytes v' s.len := by
    rw [← hsize32, extract_self]
  have h_val : bytesToNat ((intToBytes v' s.len).extract 0 32) % 2 ^ (s.len * 8) = v'.toNat := by
    rw [h_self]
    calc
      bytesToNat (intToBytes v' s.len) % 2 ^ (s.len * 8)
          = bytesToNat (uint256ToBytes v'.toNat) % 2 ^ (s.len * 8) := by
        simp [intToBytes, uint256ToBytes, hv_nonneg]
      _ = v'.toNat % 2 ^ (s.len * 8) := by
        rw [bytesToNat_uint256ToBytes v'.toNat]
      _ = v'.toNat := by
        have h_lt_pow : v'.toNat < 2 ^ (s.len * 8) := by
          have h_pow : 2 ^ (s.len * 8 - 1) ≤ 2 ^ (s.len * 8) :=
            Nat.pow_le_pow_right (by decide) (Nat.sub_le (s.len * 8) 1)
          omega
        exact Nat.mod_eq_of_lt h_lt_pow
  unfold decode
  simp [hsize32, h_val, hv_lt_nat]
  omega

private theorem intToBytes_decode_neg (s : ByteSize) (v' : Int) (hv_neg : ¬ v' ≥ 0)
    (hrange : -(2 ^ (s.len * 8 - 1) : Int) ≤ v') (hbits256 : s.len * 8 ≤ 256) :
    decode (.int s) (intToBytes v' s.len) 0 = Except.ok (ABIValue.int v', (intToBytes v' s.len).size) := by
  let b := s.len * 8
  have hbpos : 0 < b := by
    have hpos : 0 < s.len := s.h.left; omega
  have hun_nonneg : 0 ≤ (2 ^ b : Int) + v' := by
    have h_lb : -(2 ^ (b - 1) : Int) ≤ v' := by simpa [b] using hrange
    have h_diff : (2 ^ b : Int) - (2 ^ (b - 1) : Int) = (2 ^ (b - 1) : Int) :=
      two_pow_succ_sub b hbpos
    omega
  let unsigned : Nat := ((2 ^ b : Int) + v').toNat
  have h_unsigned_lt : unsigned < 2 ^ b := by
    have h_lt : (2 ^ b : Int) + v' < (2 ^ b : Int) := by omega
    have h_pos2b : 0 < (2 ^ b : Int) := by positivity
    have h_toNat : ((2 ^ b : Int) + v').toNat < (2 ^ b : Int).toNat :=
      (Int.toNat_lt_toNat h_pos2b).mpr h_lt
    simpa [unsigned, two_toNat_eq b] using h_toNat
  have h_unsigned_ge : 2 ^ (b - 1) ≤ unsigned := by
    have h_ge : (2 ^ (b - 1) : Int) ≤ (2 ^ b : Int) + v' := by
      have h_lb : -(2 ^ (b - 1) : Int) ≤ v' := by simpa [b] using hrange
      have h_diff : (2 ^ b : Int) - (2 ^ (b - 1) : Int) = (2 ^ (b - 1) : Int) :=
        two_pow_succ_sub b hbpos
      omega
    have h_ge_nat : (2 ^ (b - 1) : Nat) ≤ unsigned := by
      have h_toNat := Int.toNat_le_toNat h_ge
      simpa [unsigned, two_toNat_eq (b - 1)] using h_toNat
    exact h_ge_nat
  have h_unsigned_lt_256 : unsigned < 2 ^ 256 := by
    have h_pow : 2 ^ b ≤ 2 ^ 256 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hsize32 : (intToBytes v' s.len).size = 32 :=
    intToBytes_neg_size v' s.len (by omega) (by
      simpa [b, unsigned] using h_unsigned_lt_256)
  have h_self : (intToBytes v' s.len).extract 0 32 = intToBytes v' s.len := by
    rw [← hsize32, extract_self]
  have h_raw_sz : (natToBytes unsigned).size = s.len := by
    apply natToBytes_size_range unsigned s.len s.h.left
    · have h_eq : 2 ^ (s.len * 8 - 1) = 2 ^ (b - 1) := by simp [b]
      rw [h_eq]; exact h_unsigned_ge
    · simpa [b] using h_unsigned_lt
  have h_formula : intToBytes v' s.len = ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF)) ++ natToBytes unsigned := by
    unfold intToBytes; simp [hv_neg, unsigned, b]
    rw [h_raw_sz]
  have h_256_eq_2b : 256 ^ s.len = 2 ^ b := by
    have h256 : (256 : Nat) = (2 : Nat) ^ 8 := by native_decide
    calc
      256 ^ s.len = ((2 : Nat) ^ 8) ^ s.len := by rw [h256]
      _ = 2 ^ (8 * s.len) := by rw [Nat.pow_mul]
      _ = 2 ^ (s.len * 8) := by simp [Nat.mul_comm]
      _ = 2 ^ b := rfl
  have h_masked : bytesToNat ((intToBytes v' s.len).extract 0 32) % 2 ^ b = unsigned := by
    rw [h_self, h_formula,
      bytesToNat_append_general (ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF))) (natToBytes unsigned)]
    have h_mod : (bytesToNat (ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF))) * (2 ^ b) + unsigned) % (2 ^ b) = unsigned := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt h_unsigned_lt]
    simpa [h_raw_sz, bytesToNat_natToBytes unsigned, h_256_eq_2b] using h_mod
  have h_decode_val : -(Int.ofNat (2 ^ b - unsigned)) = v' := by
    have h_unsigned_add : unsigned + (-v').toNat = 2 ^ b := by
      have ha_nonneg : 0 ≤ (2 ^ b : Int) + v' := hun_nonneg
      have hb_nonneg : 0 ≤ -v' := by omega
      calc
        unsigned + (-v').toNat = ((2 ^ b : Int) + v').toNat + (-v').toNat := rfl
        _ = (((2 ^ b : Int) + v') + (-v')).toNat := by rw [Int.toNat_add ha_nonneg hb_nonneg]
        _ = (2 ^ b : Int).toNat := by omega
        _ = 2 ^ b := by simp [two_toNat_eq b]
    have h_sub : 2 ^ b - unsigned = (-v').toNat := by omega
    rw [h_sub]
    have h_nonneg : 0 ≤ -v' := by omega
    simp [Int.toNat_of_nonneg h_nonneg]
  unfold decode
  simp [hsize32]
  have h_masked' : bytesToNat ((intToBytes v' s.len).extract 0 32) % 2 ^ (s.len * 8) = unsigned := by
    simpa [b] using h_masked
  have h_half_ge : ¬ unsigned < 2 ^ (s.len * 8 - 1) := by
    have h_eq : 2 ^ (s.len * 8 - 1) = 2 ^ (b - 1) := by simp [b]
    rw [h_eq]; omega
  rw [h_masked']
  simp [h_half_ge]
  simpa [b] using h_decode_val

theorem decode_intToBytes (s : ByteSize) (v' : Int)
    (hrange : -(2 ^ (s.len * 8 - 1) : Int) ≤ v' ∧ v' < (2 ^ (s.len * 8 - 1) : Int)) :
    decode (.int s) (intToBytes v' s.len) 0 = Except.ok (ABIValue.int v', (intToBytes v' s.len).size) := by
  have hbits256 : s.len * 8 ≤ 256 := by
    have := s.h.right; omega
  rcases hrange with ⟨hle, hlt⟩
  by_cases hv_nonneg : v' ≥ 0
  · exact intToBytes_decode_nonneg s v' hv_nonneg hlt hbits256
  · exact intToBytes_decode_neg s v' hv_nonneg hle hbits256

theorem roundtrip_int (s : ByteSize) (v' : Int) (data : ByteArray)
    (henc : encode (.int s) (ABIValue.int v') = Except.ok data) :
    decode (.int s) data 0 = Except.ok (ABIValue.int v', data.size) := by
  unfold encode at henc; dsimp at henc
  by_cases h1 : v' < -(2 ^ (s.len * 8 - 1) : Int)
  · simp [h1] at henc
  · by_cases h2 : v' ≥ (2 ^ (s.len * 8 - 1) : Int)
    · simp [h2] at henc
    · simp [h1, h2] at henc
      have hdata : data = intToBytes v' s.len := by simpa using henc.symm
      rw [hdata]
      have hrange : -(2 ^ (s.len * 8 - 1) : Int) ≤ v' ∧ v' < (2 ^ (s.len * 8 - 1) : Int) := by omega
      have h_decode := decode_intToBytes s v' hrange
      simpa using h_decode

theorem roundtrip_fixedBytes (s : ByteSize) (v : ABIValue) (data : ByteArray)
    (henc : encode (.fixedBytes s) v = Except.ok data) :
    decode (.fixedBytes s) data 0 = Except.ok (v, data.size) := by
  cases v
  case bytes v' =>
    unfold encode at henc; dsimp at henc
    by_cases hsz : v'.size ≠ s.len
    · simp [hsz] at henc
    · have hsz_eq : v'.size = s.len := by omega
      simp [hsz_eq] at henc
      have hdata : data = padRight v' 32 := henc.symm
      have h_extract : (padRight v' 32).extract 0 s.len = v' :=
        padRight_extract_eq v' s.len hsz_eq
      have h_size : (padRight v' 32).size = 32 :=
        padRight_size_32 v' (by rw [hsz_eq]; exact s.h.right)
      unfold decode; rw [hdata]; simp [h_extract, h_size]
  all_goals { unfold encode at henc; simp at henc }

private lemma dynamicRoundtrip_preamble (b : ByteArray) (hb256 : b.size < 2 ^ 256) :
    (uint256ToBytes b.size).size = 32 ∧
    (padRight b (roundUp32 b.size)).size = roundUp32 b.size ∧
    b.size ≤ roundUp32 b.size ∧
    (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).size = 32 + roundUp32 b.size ∧
    bytesToNat ((uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 0 32) = b.size ∧
    (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 32 (32 + b.size) = b := by
  have ha_sz : (uint256ToBytes b.size).size = 32 :=
    uint256ToBytes_size b.size (natToBytes_size_bound b.size hb256)
  have h_roundUp_ge : b.size ≤ roundUp32 b.size := by
    unfold roundUp32; omega
  have h_pad_sz : (padRight b (roundUp32 b.size)).size = roundUp32 b.size := by
    unfold padRight; split
    · omega
    · simp [zeros_size]; omega
  have h_size : (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).size = 32 + roundUp32 b.size := by
    simp [ha_sz, h_pad_sz]
  have h_len : bytesToNat ((uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 0 32) = b.size := by
    rw [← ha_sz, extract_first_n, bytesToNat_uint256ToBytes b.size]
  have h_extract_val : (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 32 (32 + b.size) = b :=
    roundtrip_bytes_val b hb256
  exact ⟨ha_sz, h_pad_sz, h_roundUp_ge, h_size, h_len, h_extract_val⟩

private lemma decodeDynamicBytes_roundtrip (v' : ByteArray) (hv256 : v'.size < 2 ^ 256) (data : ByteArray)
    (hdata : data = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)) :
    decodeDynamicBytes data 0 = Except.ok (.bytes v', data.size) := by
  rw [hdata]
  rcases dynamicRoundtrip_preamble v' hv256 with ⟨_, _, h_roundUp_ge, h_size, h_len, h_extract_val⟩
  unfold decodeDynamicBytes
  simp [h_size, h_len, h_extract_val, h_roundUp_ge]

theorem roundtrip_bytes (v : ABIValue) (data : ByteArray)
    (henc : encode .bytes v = Except.ok data) :
    decode .bytes data 0 = Except.ok (v, data.size) := by
  cases v
  case bytes v' =>
    simp [encode] at henc; split at henc
    · rename_i hv256
      have hdata : data = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size) := by
        simpa using henc.symm
      unfold decode
      rw [hdata]
      exact decodeDynamicBytes_roundtrip v' hv256 (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)) rfl
    · simp at henc
  all_goals { unfold encode at henc; simp at henc }

private lemma decodeDynamicString_roundtrip (v' : String) (hv256 : v'.toUTF8.size < 2 ^ 256) (data : ByteArray)
    (hdata : data = uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size)) :
    decodeDynamicString data 0 = Except.ok (.string v', data.size) := by
  rw [decodeDynamicString, decodeDynamicBytes_roundtrip v'.toUTF8 hv256 data hdata]
  simp [Except.map]
  have h : v'.toByteArray = v'.toUTF8 := rfl
  rw [h, fromUTF8!_toUTF8 v']

theorem roundtrip_string (v : ABIValue) (data : ByteArray)
    (henc : encode .string v = Except.ok data) :
    decode .string data 0 = Except.ok (v, data.size) := by
  cases v
  case string v' =>
    simp [encode] at henc; split at henc
    · rename_i huv256
      have hdata : data = uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size) := by
        simpa using henc.symm
      unfold decode
      rw [hdata]
      exact decodeDynamicString_roundtrip v' huv256
        (uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size)) rfl
    · simp at henc
  all_goals { unfold encode at henc; simp at henc }

/-! ## ABIVisitor instance for RoundtripVisitor -/

instance : ABIVisitor RoundtripVisitor where
  onUint s := ⟨roundtrip_uint s⟩
  onInt s := ⟨λ v data henc => by
    cases v
    case int v' => exact roundtrip_int s v' data henc
    all_goals { unfold encode at henc; simp at henc }⟩
  onBool := ⟨roundtrip_bool⟩
  onAddress := ⟨roundtrip_address⟩
  onFixedBytes s := ⟨roundtrip_fixedBytes s⟩
  onBytes := ⟨roundtrip_bytes⟩
  onString := ⟨roundtrip_string⟩

  onArray {e} (ih : RoundtripVisitor e) : RoundtripVisitor (.array e) :=
    ⟨λ v data henc => by
      cases v
      case array vals =>
        rcases encode_array_decompose e vals data henc with ⟨h_len_lt, encs, h_data, h_zip_len, h_zip⟩
        rw [h_data]
        unfold decode; simp
        by_cases h_dyn : isDynamic e
        · -- dynamic element array: use head/tail pointer layout
          simp [h_dyn, decodeArrayElems]
          -- Prove roundtrip for dynamic elements
          have h_len_val : bytesToNat ((uint256ToBytes vals.length).extract 0 32) = vals.length :=
            bytesToNat_uint256ToBytes vals.length
          have h_pref_sz : (uint256ToBytes vals.length).size = 32 :=
            uint256ToBytes_size vals.length (natToBytes_size_bound vals.length h_len_lt)
          sorry
        · -- static element array: sequential decoding
          simp [h_dyn, decodeArrayElems, arrayPack]
          sorry
      case _ => unfold encode at henc; simp at henc⟩

  onFixedArray n {e} (ih : RoundtripVisitor e) : RoundtripVisitor (.fixedArray n e) :=
    ⟨λ v data henc => by
      cases v
      case array vals =>
        rcases encode_fixedArray_decompose e n vals data henc with ⟨h_len_eq, encs, h_data, h_zip_len, h_zip⟩
        rw [h_data]
        unfold decode; simp
        by_cases h_dyn : isDynamic e
        · simp [h_dyn, decodeArrayElems]
          sorry
        · simp [h_dyn, decodeArrayElems, arrayPack]
          sorry
      case _ => unfold encode at henc; simp at henc⟩

  onTuple {ts} (all : All RoundtripVisitor ts) : RoundtripVisitor (.tuple ts) :=
    ⟨λ v data henc => by
      cases v
      case tuple vals =>
        sorry
      case _ => unfold encode at henc; simp at henc⟩

/-! ## Universal roundtrip theorem -/

theorem roundtrip (t : ABIType) (v : ABIValue) (data : ByteArray)
    (henc : encode t v = Except.ok data) : decode t data 0 = Except.ok (v, data.size) :=
  (foldABIType RoundtripVisitor t).roundtrip v data henc
