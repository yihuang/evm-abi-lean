/-
# Universal Roundtrip Theorem: encode ∘ decode = id
-/

import EvmAbi.LemmaUtils

open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode
set_option linter.unusedVariables false


/- uint256 encode → decode recovers the original value. -/
theorem roundtrip_uint (s : ByteSize) (v : ABIValue) (data : ByteArray) (henc : encode (.uint s) v = Except.ok data) :
    decode (.uint s) data 0 = Except.ok (v, data.size) := by
  let byteLen := s.len
  have hbits256 : byteLen * 8 ≤ 256 := by
    have := s.h.right
    omega
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
          _ = v' := bytesToNat_uint256ToBytes v' hv256
      unfold decode; rw [hdata]; simp [hsize32, h_val, hrange]
  case int v' => simp [encode] at henc
  case bool v' => simp [encode] at henc
  case bytes v' => simp [encode] at henc
  case string v' => simp [encode] at henc
  case address v' => simp [encode] at henc
  case array vals => simp [encode] at henc
  case tuple vals => simp [encode] at henc

/- bool encode → decode recovers the original value. -/
theorem roundtrip_bool (v : ABIValue) (data : ByteArray) (henc : encode .bool v = Except.ok data) :
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
        bytesToNat ((uint256ToBytes (if v' then 1 else 0)).extract 0 32) = bytesToNat (uint256ToBytes (if v' then 1 else 0)) := by
          rw [← hsize32, extract_self]
        _ = (if v' then 1 else 0) := bytesToNat_uint256ToBytes (if v' then 1 else 0) hbits
    unfold decode; rw [hdata]; simp [hsize32, h_val]; cases v' <;> simp
  case uint v' => simp [encode] at henc
  case int v' => simp [encode] at henc
  case bytes v' => simp [encode] at henc
  case string v' => simp [encode] at henc
  case address v' => simp [encode] at henc
  case array vals => simp [encode] at henc
  case tuple vals => simp [encode] at henc

/- address encode → decode recovers the original 20-byte value. -/
theorem roundtrip_address (v : ABIValue) (data : ByteArray) (henc : encode .address v = Except.ok data) :
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
  case uint v' => simp [encode] at henc
  case int v' => simp [encode] at henc
  case bool v' => simp [encode] at henc
  case bytes v' => simp [encode] at henc
  case string v' => simp [encode] at henc
  case array vals => simp [encode] at henc
  case tuple vals => simp [encode] at henc


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
        rw [bytesToNat_uint256ToBytes v'.toNat hv_lt_256]
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
    rw [h_self, h_formula, bytesToNat_append_general (ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF))) (natToBytes unsigned)]
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

theorem roundtrip_int (s : ByteSize) (v' : Int) (data : ByteArray) (henc : encode (.int s) (ABIValue.int v') = Except.ok data) :
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
lemma dynamicRoundtrip_preamble (b : ByteArray) (hb256 : b.size < 2 ^ 256) :
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
    rw [← ha_sz, extract_first_n, bytesToNat_uint256ToBytes b.size hb256]
  have h_extract_val : (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 32 (32 + b.size) = b :=
    roundtrip_bytes_val b hb256
  exact ⟨ha_sz, h_pad_sz, h_roundUp_ge, h_size, h_len, h_extract_val⟩

theorem decodeDynamicBytes_roundtrip (v' : ByteArray) (hv256 : v'.size < 2 ^ 256) (data : ByteArray)
    (hdata : data = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)) :
    decodeDynamicBytes data 0 = Except.ok (.bytes v', data.size) := by
  rw [hdata]
  rcases dynamicRoundtrip_preamble v' hv256 with ⟨_, _, h_roundUp_ge, h_size, h_len, h_extract_val⟩
  unfold decodeDynamicBytes
  simp [h_size, h_len, h_extract_val, h_roundUp_ge]

theorem roundtrip_bytes_full (v' : ByteArray) (data : ByteArray) (henc : encode .bytes (ABIValue.bytes v') = Except.ok data) :
    decode .bytes data 0 = Except.ok (ABIValue.bytes v', data.size) := by
  simp [encode] at henc; split at henc
  · rename_i hv256
    have hdata : data = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size) := by
      simpa using henc.symm
    unfold decode
    rw [hdata]
    exact decodeDynamicBytes_roundtrip v' hv256 (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)) rfl
  · simp at henc

theorem decodeDynamicString_roundtrip (v' : String) (hv256 : v'.toUTF8.size < 2 ^ 256) (data : ByteArray)
    (hdata : data = uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size)) :
    decodeDynamicString data 0 = Except.ok (.string v', data.size) := by
  let utf8 := v'.toUTF8
  have huv256 : utf8.size < 2 ^ 256 := hv256
  have hdata' : data = uint256ToBytes utf8.size ++ padRight utf8 (roundUp32 utf8.size) := by
    simpa [utf8] using hdata
  rw [hdata']
  rcases dynamicRoundtrip_preamble utf8 huv256 with ⟨ha_sz, h_pad_sz, _, h_size, h_len, h_extract_val⟩
  unfold decodeDynamicString; dsimp; simp
  rw [ha_sz, h_pad_sz, h_len, h_extract_val, fromUTF8!_toUTF8 v']
  have h1 : ¬ (32 + roundUp32 utf8.size < 32) := by omega
  have h2 : ¬ (32 + roundUp32 utf8.size < 32 + utf8.size) := by omega
  simp [h1, h2]
theorem roundtrip_string_full (v' : String) (data : ByteArray) (henc : encode .string (ABIValue.string v') = Except.ok data) :
    decode .string data 0 = Except.ok (ABIValue.string v', data.size) := by
  simp [encode] at henc; split at henc
  · rename_i huv256
    have hdata : data = uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size) := by
      simpa using henc.symm
    unfold decode
    rw [hdata]
    exact decodeDynamicString_roundtrip v' huv256 (uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size)) rfl
  · simp at henc

/-- For ATOMIC non-dynamic types, encode always produces exactly 32 bytes.
    This theorem is FALSE for arrays and tuples (e.g., uint[4] encodes to 128 bytes),
    so callers must provide h_atomic: isAtomic t. -/
theorem encode_atomic_nondyn_size (t : ABIType) (v : ABIValue) (data : ByteArray) (henc : encode t v = Except.ok data)
    (h_nondyn : isDynamic t = false) (h_atomic : isAtomic t) : data.size = 32 := by
  cases t
  case uint s =>
    cases v
    case uint n =>
      unfold encode at henc; dsimp at henc
      by_cases hn : n ≥ 2 ^ (s.len * 8)
      · simp [hn] at henc
      · simp [hn] at henc
        have hdata : data = uint256ToBytes n := henc.symm
        rw [hdata]
        have h_bound : n < 2 ^ 256 := by
          have hlen : s.len * 8 ≤ 256 := by
            have := s.h.right; omega
          have hp : 2 ^ (s.len * 8) ≤ 2 ^ 256 :=
            Nat.pow_le_pow_right (by omega) hlen
          omega
        have hsz : (natToBytes n).size ≤ 32 := natToBytes_size_bound n h_bound
        exact uint256ToBytes_size n hsz
    all_goals { unfold encode at henc; simp at henc }
  case int s =>
    cases v
    case int n =>
      unfold encode at henc; dsimp at henc
      by_cases h1 : n < -(2 ^ (s.len * 8 - 1) : Int)
      · simp [h1] at henc
      · by_cases h2 : n ≥ (2 ^ (s.len * 8 - 1) : Int)
        · simp [h2] at henc
        · simp [h1, h2] at henc
          have hdata : data = intToBytes n s.len := henc.symm
          rw [hdata]
          by_cases hn_nonneg : n ≥ 0
          · have h_lt : n < (2 ^ (s.len * 8 - 1) : Int) := by omega
            have h_nat_lt : n.toNat < 2 ^ (s.len * 8 - 1) :=
              (Int.ofNat_lt.mp (by
                have h_n_nat : (n.toNat : Int) = n := Int.toNat_of_nonneg hn_nonneg
                simpa [h_n_nat] using h_lt))
            have h_bound : n.toNat < 2 ^ 256 :=
              calc
                n.toNat < 2 ^ (s.len * 8 - 1) := h_nat_lt
                _ ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by
                  have hlen : s.len * 8 - 1 ≤ 256 := by
                    have : s.len ≤ 32 := s.h.right; omega
                  exact hlen)
            have hsz : (natToBytes n.toNat).size ≤ 32 := natToBytes_size_bound n.toNat h_bound
            calc
              (intToBytes n s.len).size = (uint256ToBytes n.toNat).size := by
                simp [intToBytes, uint256ToBytes, hn_nonneg]
              _ = 32 := uint256ToBytes_size n.toNat hsz
          · have h_bounded : ((2 : Int) ^ (s.len * 8) + n).toNat < 2 ^ 256 := by
              have h_nonneg : 0 ≤ (2 : Int) ^ (s.len * 8) := two_pow_nonneg (s.len * 8)
              have h_lt : (2 : Int) ^ (s.len * 8) + n < (2 : Int) ^ (s.len * 8) := by omega
              have hpos : 0 < (2 : Int) ^ (s.len * 8) := by positivity
              have h_lt_nat : ((2 : Int) ^ (s.len * 8) + n).toNat < ((2 : Int) ^ (s.len * 8)).toNat :=
                (Int.toNat_lt_toNat hpos).mpr h_lt
              have h_toNat : ((2 : Int) ^ (s.len * 8)).toNat = (2 : Nat) ^ (s.len * 8) :=
                two_toNat_eq (s.len * 8)
              have h_lt_nat' : ((2 : Int) ^ (s.len * 8) + n).toNat < (2 : Nat) ^ (s.len * 8) := by
                simpa [h_toNat] using h_lt_nat
              have h256 : (2 : Nat) ^ (s.len * 8) ≤ 2 ^ 256 :=
                Nat.pow_le_pow_right (by omega) (by
                  have : s.len ≤ 32 := s.h.right; omega)
              exact Nat.lt_of_lt_of_le h_lt_nat' h256
            exact intToBytes_neg_size n s.len (by omega) h_bounded
    all_goals { unfold encode at henc; simp at henc }
  case bool =>
    unfold isAtomic at h_atomic; simp at h_atomic
    cases v
    case bool b =>
      unfold encode at henc; simp at henc
      have hdata : data = uint256ToBytes (if b then 1 else 0) := henc.symm
      rw [hdata]
      have h_bound : (if b then 1 else 0) < 2 ^ 256 := by split <;> omega
      have hsz : (natToBytes (if b then 1 else 0)).size ≤ 32 :=
        natToBytes_size_bound (if b then 1 else 0) h_bound
      exact uint256ToBytes_size (if b then 1 else 0) hsz
    all_goals { unfold encode at henc; simp at henc }
  case bytesM s =>
    cases v
    case bytes b =>
      unfold encode at henc
      by_cases hsz : b.size ≠ s.len
      · simp [hsz] at henc
      · simp [hsz] at henc
        have hdata : data = padRight b 32 := henc.symm
        rw [hdata]
        have h_sz32 : b.size ≤ 32 := by
          rw [show b.size = s.len from by omega]; exact s.h.right
        unfold padRight; split
        · omega
        · simp [zeros_size]; omega
    all_goals { unfold encode at henc; simp at henc }
  case address =>
    unfold isAtomic at h_atomic; simp at h_atomic
    cases v
    case address b =>
      unfold encode at henc
      by_cases hsz : b.size ≠ 20
      · simp [hsz] at henc
      · simp [show b.size = 20 from by omega] at henc
        have hdata : data = padLeft b 32 := henc.symm
        rw [hdata]
        unfold padLeft
        have h20 : b.size = 20 := by omega
        simp [h20, zeros_size]
    all_goals { unfold encode at henc; simp at henc }
  case bytes => unfold isDynamic at h_nondyn; simp at h_nondyn
  case string => unfold isDynamic at h_nondyn; simp at h_nondyn
  case array _ _ =>
    unfold isAtomic at h_atomic; simp at h_atomic
  case tuple _ =>
    unfold isAtomic at h_atomic; simp at h_atomic

/-! ## Static array encoding size -/

/-- Size of static encoding with arbitrary accumulator.
    Only valid for ATOMIC element types (encodes to 32 bytes each). -/
theorem encodeFixedArrayStatic_size_gen (elemType : ABIType) (vals : List ABIValue) (acc enc : ByteArray)
    (henc : encodeFixedArrayStatic elemType vals acc = Except.ok enc)
    (h_nondyn : isDynamic elemType = false) (h_atomic : isAtomic elemType) : enc.size = acc.size + vals.length * 32 := by
  revert acc enc henc h_nondyn h_atomic
  induction vals with
  | nil =>
    intro acc enc henc _ _
    simp [encodeFixedArrayStatic] at henc
    subst henc; simp
  | cons v rest ih =>
    intro acc enc henc h_nondyn h_atomic
    simp [encodeFixedArrayStatic] at henc
    cases henc_v : encode elemType v
    · simp [henc_v] at henc
    · rename_i enc_v
      simp [henc_v] at henc
      have h_sz_v : enc_v.size = 32 := encode_atomic_nondyn_size elemType v enc_v henc_v h_nondyn h_atomic
      have h_rest := ih (acc ++ enc_v) enc henc h_nondyn h_atomic
      rw [h_rest]
      have h_acc_size : (acc ++ enc_v).size = acc.size + 32 := by
        simp [h_sz_v]
      rw [h_acc_size]
      simp [show (v :: rest).length = rest.length + 1 by simp]
      omega

/-- Size of static encoding starting from empty.
    Corollary of encodeFixedArrayStatic_size_gen. Only valid for atomic element types. -/
theorem encodeFixedArrayStatic_size (elemType : ABIType) (vals : List ABIValue) (enc : ByteArray)
    (henc : encodeFixedArrayStatic elemType vals ByteArray.empty = Except.ok enc)
    (h_nondyn : isDynamic elemType = false) (h_atomic : isAtomic elemType) : enc.size = vals.length * 32 := by
  have h := encodeFixedArrayStatic_size_gen elemType vals ByteArray.empty enc henc h_nondyn h_atomic
  simp at h; exact h

/-- Shift the start index of goStatic by one: running from (n+1) at (i+1) with the same offset
    is equivalent to running from n at i. The termination measure (n-i) is the same. -/
theorem goStatic_shift_one (elemType : ABIType) (data : ByteArray) (n i off : Nat) (acc : List ABIValue) :
    decodeFixedArray_goStatic elemType (n+1) data (i+1) off acc =
    decodeFixedArray_goStatic elemType n data i off acc :=
by
  have h_all : ∀ (k : Nat), ∀ (n i off : Nat) (acc : List ABIValue), n - i = k →
      decodeFixedArray_goStatic elemType (n+1) data (i+1) off acc =
      decodeFixedArray_goStatic elemType n data i off acc := by
    intro k
    refine Nat.strongRecOn k ?_
    intro m IH n i off acc hm
    by_cases h : i ≥ n
    · have h' : i+1 ≥ n+1 := by omega
      simp [decodeFixedArray_goStatic, h, h']
    · have h_not_ge : ¬ i ≥ n := by omega
      have h_not_ge' : ¬ i+1 ≥ n+1 := by omega
      rw [decodeFixedArray_goStatic, decodeFixedArray_goStatic]
      rw [if_neg h_not_ge, if_neg h_not_ge']
      cases h_dec : decode elemType data off
      · rfl
      · rename_i p; rcases p with ⟨v, newOff⟩
        simp
        have hm' : n - (i+1) < m := by
          have hpos : n - i > 0 := by
            have : i < n := by omega
            omega
          rw [hm] at hpos
          omega
        have h_IH := IH (n - (i+1)) hm' n (i+1) newOff (v :: acc) rfl
        exact h_IH
  exact h_all (n - i) n i off acc rfl

/-- Prepending v to the accumulator (via acc ++ [v]) results in v being prepended to the result list.
    Works for any starting offset. Proved by induction on n, using goStatic_shift_one. -/
theorem goStatic_prepend_initial (e : ABIType) (data : ByteArray) (n : Nat) (v : ABIValue) :
    ∀ (off : Nat) (acc : List ABIValue),
    decodeFixedArray_goStatic e n data 0 off (acc ++ [v]) =
    (fun (p : List ABIValue × Nat) => (v :: p.1, p.2)) <$> decodeFixedArray_goStatic e n data 0 off acc :=
by
  induction n with
  | zero =>
    intro off acc
    rw [decodeFixedArray_goStatic, decodeFixedArray_goStatic]
    simp
  | succ n ih =>
    intro off acc
    have h_lt : ¬ 0 ≥ n.succ := by omega
    rw [decodeFixedArray_goStatic, if_neg h_lt,
      decodeFixedArray_goStatic, if_neg h_lt]
    cases h_dec : decode e data off
    · rfl
    · rename_i p; rcases p with ⟨v', newOff⟩
      simp
      have h1 : decodeFixedArray_goStatic e (n+1) data 1 newOff (v' :: (acc ++ [v])) =
        decodeFixedArray_goStatic e n data 0 newOff (v' :: (acc ++ [v])) := by
        simpa using goStatic_shift_one e data n 0 newOff (v' :: (acc ++ [v]))
      have h2 : decodeFixedArray_goStatic e (n+1) data 1 newOff (v' :: acc) =
        decodeFixedArray_goStatic e n data 0 newOff (v' :: acc) := by
        simpa using goStatic_shift_one e data n 0 newOff (v' :: acc)
      have h_assoc : v' :: (acc ++ [v]) = (v' :: acc) ++ [v] := by simp
      rw [h1, h2, h_assoc]
      rw [ih newOff (v' :: acc)]

/-- Extract composition: first extract [a, c), then extract [b, d) from that result,
    equals extracting [a+b, a+d) from the original. -/
theorem extract_extract_general (x : ByteArray) (a b c d : Nat) (hb : b ≤ d) (hd : a + d ≤ c) :
    (x.extract a c).extract b d = x.extract (a + b) (a + d) := by
  apply ByteArray.ext
  simp
  have hmin : min (a + d) c = a + d := by
    simpa [Nat.min_comm] using Nat.min_eq_right hd
  simp [hmin]
/-- Extracting from (pref ++ suff) past pref.size is the same as extracting from suff. -/
theorem extract_after_suffix_offset (pref suff : ByteArray) (off k : Nat) :
    (pref ++ suff).extract (pref.size + off) (pref.size + off + k) = suff.extract off (off + k) := by
  calc
    (pref ++ suff).extract (pref.size + off) (pref.size + off + k)
        = (pref ++ suff).extract (pref.size + off) (pref.size + (off + k)) := by simp [Nat.add_assoc]
    _ = ((pref ++ suff).extract pref.size (pref.size + (off + k))).extract off (off + k) := by
      symm; exact extract_extract_general (pref ++ suff) pref.size off (pref.size + (off + k)) (off + k) (by omega) (by omega)
    _ = (suff.extract 0 (off + k)).extract off (off + k) := by
      rw [extract_after_suffix pref suff (off + k)]
    _ = suff.extract off (off + k) := by
      rw [extract_extract_general suff 0 off (off + k) (off + k) (by omega) (by omega)]
      simp


/-! ## Atomic element offset shift lemmas -/

/-- When an atomic type decodes successfully, the new offset is off + 32. -/
theorem decode_atomic_new_off (t : ABIType) (data : ByteArray) (off : Nat) (v : ABIValue) (newOff : Nat)
    (h_nondyn : isDynamic t = false) (h_atomic : isAtomic t)
    (h_decode : decode t data off = Except.ok (v, newOff)) : newOff = off + 32 :=
by
  cases t
  · case uint s =>
    unfold decode at h_decode
    by_cases h_size : off + 32 > data.size
    · simp [h_size] at h_decode
    · simp [h_size] at h_decode
      repeat (split at h_decode <;> try simp at h_decode)
      all_goals
        try (rcases h_decode with ⟨hv, hoff⟩; exact hoff.symm)
        try (simp at h_decode)
  · case int s =>
    unfold decode at h_decode
    by_cases h_size : off + 32 > data.size
    · simp [h_size] at h_decode
    · simp [h_size] at h_decode
      repeat (split at h_decode <;> try simp at h_decode)
      all_goals
        try (rcases h_decode with ⟨hv, hoff⟩; exact hoff.symm)
        try (simp at h_decode)
  · case bool =>
    unfold decode at h_decode
    by_cases h_size : off + 32 > data.size
    · simp [h_size] at h_decode
    · simp [h_size] at h_decode
      by_cases h0 : bytesToNat (data.extract off (off + 32)) = 0
      · simp [h0] at h_decode
        rcases h_decode with ⟨hv, hoff⟩
        exact hoff.symm
      · simp [h0] at h_decode
        by_cases h1 : bytesToNat (data.extract off (off + 32)) = 1
        · simp [h0, h1] at h_decode
          rcases h_decode with ⟨hv, hoff⟩
          exact hoff.symm
        · simp [h0, h1] at h_decode
  · case bytesM s =>
    unfold decode at h_decode
    by_cases h_size : off + 32 > data.size
    · simp [h_size] at h_decode
    · simp [h_size] at h_decode
      repeat (split at h_decode <;> try simp at h_decode)
      all_goals
        try (rcases h_decode with ⟨hv, hoff⟩; exact hoff.symm)
        try (simp at h_decode)
  · case address =>
    unfold decode at h_decode
    by_cases h_size : off + 32 > data.size
    · simp [h_size] at h_decode
    · simp [h_size] at h_decode
      repeat (split at h_decode <;> try simp at h_decode)
      all_goals
        try (rcases h_decode with ⟨hv, hoff⟩; exact hoff.symm)
        try (simp at h_decode)
  · case bytes => unfold isDynamic at h_nondyn; simp at h_nondyn
  · case string => unfold isDynamic at h_nondyn; simp at h_nondyn
  · case array e sOpt => unfold isAtomic at h_atomic; simp at h_atomic
  · case tuple es => unfold isAtomic at h_atomic; simp at h_atomic

/-- For atomic non-dynamic types with enough data, decoding from (pref ++ suffix) at (pref.size + off)
    equals decoding from suffix at off, with the offset shifted by pref.size.
    Requires h_suff_size: off + 32 ≤ suffix.size so both sides have enough data. -/
theorem decode_atomic_offset_shift (t : ABIType) (pref suffix : ByteArray) (off : Nat)
    (h_nondyn : isDynamic t = false) (h_atomic : isAtomic t)
    (h_suff_size : off + 32 ≤ suffix.size) :
    decode t (pref ++ suffix) (pref.size + off) = 
    (fun (p : ABIValue × Nat) => (p.1, pref.size + p.2)) <$> decode t suffix off :=
by
  have h_size : ¬ (pref.size + off + 32 > (pref ++ suffix).size) := by
    simp; omega
  have h_extract32 : (pref ++ suffix).extract (pref.size + off) (pref.size + off + 32) = suffix.extract off (off + 32) :=
    extract_after_suffix_offset pref suffix off 32
  cases t
  · case uint s =>
    unfold decode
    have h_suff_sz : off + 32 ≤ suffix.size := h_suff_size
    by_cases h_sz1 : pref.size + off + 32 > (pref ++ suffix).size
    · exfalso; exact h_size h_sz1
    · by_cases h_sz2 : off + 32 > suffix.size
      · exfalso; omega
      · by_cases h_val : 2 ^ (s.len * 8) ≤ bytesToNat (suffix.extract off (off + 32))
        · rw [if_neg h_sz1, if_neg h_sz2, h_extract32]
          simp [h_val, Functor.map, Except.map, Nat.add_assoc]
        · rw [if_neg h_sz1, if_neg h_sz2, h_extract32]
          simp [h_val, Functor.map, Except.map, Nat.add_assoc]
  · case int s =>
    unfold decode
    by_cases h_sz1 : pref.size + off + 32 > (pref ++ suffix).size
    · exfalso; exact h_size h_sz1
    · by_cases h_sz2 : off + 32 > suffix.size
      · exfalso; omega
      · by_cases h_val : bytesToNat (suffix.extract off (off + 32)) % 2 ^ (s.len * 8) < 2 ^ (s.len * 8 - 1)
        · rw [if_neg h_sz1, if_neg h_sz2, h_extract32]
          simp [h_val, Functor.map, Except.map, Nat.add_assoc]
        · rw [if_neg h_sz1, if_neg h_sz2, h_extract32]
          simp [h_val, Functor.map, Except.map, Nat.add_assoc]
  · case bool =>
    unfold decode
    by_cases h_sz1 : pref.size + off + 32 > (pref ++ suffix).size
    · exfalso; exact h_size h_sz1
    · by_cases h_sz2 : off + 32 > suffix.size
      · exfalso; omega
      · by_cases h_val : bytesToNat (suffix.extract off (off + 32)) = 0
        · rw [if_neg h_sz1, if_neg h_sz2, h_extract32]
          simp [h_val, Functor.map, Except.map, Nat.add_assoc]
        · by_cases h_val' : bytesToNat (suffix.extract off (off + 32)) = 1
          · rw [if_neg h_sz1, if_neg h_sz2, h_extract32]
            simp [h_val, h_val', Functor.map, Except.map, Nat.add_assoc]
          · rw [if_neg h_sz1, if_neg h_sz2, h_extract32]
            simp [h_val, h_val', Functor.map, Except.map, Nat.add_assoc]
  · case bytesM s =>
    have h_extract_slen : (pref ++ suffix).extract (pref.size + off) (pref.size + off + s.len) = suffix.extract off (off + s.len) :=
      extract_after_suffix_offset pref suffix off s.len
    unfold decode
    by_cases h_sz1 : pref.size + off + 32 > (pref ++ suffix).size
    · exfalso; exact h_size h_sz1
    · by_cases h_sz2 : off + 32 > suffix.size
      · exfalso; omega
      · rw [if_neg h_sz1, if_neg h_sz2]
        rw [h_extract_slen]
        simp [Functor.map, Except.map, Nat.add_assoc]
  · case address =>
    have h_extract_addr : (pref ++ suffix).extract (pref.size + off + 12) (pref.size + off + 32) = suffix.extract (off + 12) (off + 32) := by
      calc
        (pref ++ suffix).extract (pref.size + off + 12) (pref.size + off + 32)
            = (pref ++ suffix).extract (pref.size + (off + 12)) (pref.size + (off + 12) + 20) := by
              have hA : pref.size + off + 12 = pref.size + (off + 12) := by omega
              have hB : pref.size + off + 32 = pref.size + (off + 12) + 20 := by omega
              simp [hA, hB]
        _ = suffix.extract (off + 12) ((off + 12) + 20) := extract_after_suffix_offset pref suffix (off + 12) 20
        _ = suffix.extract (off + 12) (off + 32) := by
          have hB : (off + 12) + 20 = off + 32 := by omega
          simp [hB]
    unfold decode
    by_cases h_sz1 : pref.size + off + 32 > (pref ++ suffix).size
    · exfalso; exact h_size h_sz1
    · by_cases h_sz2 : off + 32 > suffix.size
      · exfalso; omega
      · rw [if_neg h_sz1, if_neg h_sz2]
        rw [h_extract_addr]
        simp [Functor.map, Except.map, Nat.add_assoc]
  · case bytes => unfold isDynamic at h_nondyn; simp at h_nondyn
  · case string => unfold isDynamic at h_nondyn; simp at h_nondyn
  · case array e sOpt => unfold isAtomic at h_atomic; simp at h_atomic
  · case tuple es => unfold isAtomic at h_atomic; simp at h_atomic

/-- Shifting goStatic data and offset by a prefix: running on (pref ++ suff) at offset (pref.size + off)
    equals running on suff at offset off, with the result offset shifted.
    Requires that the suffix has enough data for all remaining elements. -/
theorem goStatic_offset_shift (e : ABIType) (pref suff : ByteArray) (n i off : Nat) (acc : List ABIValue)
    (h_nondyn : isDynamic e = false) (h_atomic : isAtomic e)
    (h_suff_size : off + (n - i) * 32 ≤ suff.size) :
    decodeFixedArray_goStatic e n (pref ++ suff) i (pref.size + off) acc =
    (fun (p : List ABIValue × Nat) => (p.1, pref.size + p.2)) <$> decodeFixedArray_goStatic e n suff i off acc :=
by
  have h_all : ∀ (k : Nat), ∀ (n i off : Nat) (acc : List ABIValue), n - i = k →
    off + (n - i) * 32 ≤ suff.size →
    decodeFixedArray_goStatic e n (pref ++ suff) i (pref.size + off) acc =
    (fun (p : List ABIValue × Nat) => (p.1, pref.size + p.2)) <$> decodeFixedArray_goStatic e n suff i off acc := by
    intro k
    refine Nat.strongRecOn k ?_
    intro m IH n i off acc hm hsz
    by_cases h : i ≥ n
    · simp [decodeFixedArray_goStatic, h]
    · have h_not_ge : ¬ i ≥ n := by omega
      rw [decodeFixedArray_goStatic, decodeFixedArray_goStatic]
      rw [if_neg h_not_ge, if_neg h_not_ge]
      -- enough data for the first decode
      have h_suff_32 : off + 32 ≤ suff.size := by
        have : n - i ≥ 1 := by omega
        omega
      have h_decode_eq : decode e (pref ++ suff) (pref.size + off) = 
        (fun (p : ABIValue × Nat) => (p.1, pref.size + p.2)) <$> decode e suff off :=
        decode_atomic_offset_shift e pref suff off h_nondyn h_atomic h_suff_32
      cases h_dec : decode e suff off
      · rw [h_decode_eq, h_dec]; rfl
      · rename_i p; rcases p with ⟨v, newOff⟩
        have h_newOff : newOff = off + 32 :=
          decode_atomic_new_off e suff off v newOff h_nondyn h_atomic h_dec
        subst h_newOff
        have hm' : n - (i+1) < m := by
          have : n - (i+1) < n - i := by omega
          rw [hm] at this; exact this
        have hsz' : (off + 32) + (n - (i+1)) * 32 ≤ suff.size := by
          have : off + (n - i) * 32 = (off + 32) + (n - (i+1)) * 32 := by omega
          rw [← this]; exact hsz
        rw [h_decode_eq, h_dec]
        simp
        exact IH (n - (i+1)) hm' n (i+1) (off + 32) (v :: acc) rfl hsz'
  exact h_all (n - i) n i off acc rfl h_suff_size

/-- Relation between encoding with any accumulator and encoding from empty. -/
theorem encodeFixedArrayStatic_eq (elemType : ABIType) (vals : List ABIValue) (acc : ByteArray) :
    encodeFixedArrayStatic elemType vals acc =
    match encodeFixedArrayStatic elemType vals ByteArray.empty with
    | Except.ok suffix => Except.ok (acc ++ suffix)
    | Except.error e => Except.error e := by
  revert acc
  induction vals with
  | nil => intro acc; simp [encodeFixedArrayStatic]
  | cons v rest ih =>
    intro acc
    simp [encodeFixedArrayStatic]
    cases h_enc_v : encode elemType v
    · simp [h_enc_v]
    · rename_i enc_v
      simp [h_enc_v]
      cases h_rest : encodeFixedArrayStatic elemType rest ByteArray.empty
      · rename_i e
        simp [h_rest, ih enc_v, ih (acc ++ enc_v)]
      · rename_i suffix
        have h_rest_result : encodeFixedArrayStatic elemType rest enc_v = Except.ok (enc_v ++ suffix) := by
          rw [ih enc_v, h_rest]
        have h_ih' : encodeFixedArrayStatic elemType rest (acc ++ enc_v) = Except.ok ((acc ++ enc_v) ++ suffix) := by
          rw [ih (acc ++ enc_v), h_rest]
        rw [h_rest_result, h_ih']
        have h_assoc : (acc ++ enc_v) ++ suffix = acc ++ (enc_v ++ suffix) := by
          apply ByteArray.ext; simp
        rw [h_assoc]

/-- Corollary: if encoding from empty succeeds, encoding from any accumulator adds it as prefix. -/
theorem encodeFixedArrayStatic_acc (elemType : ABIType) (vals : List ABIValue) (acc suffix : ByteArray)
    (h_empty : encodeFixedArrayStatic elemType vals ByteArray.empty = Except.ok suffix) :
    encodeFixedArrayStatic elemType vals acc = Except.ok (acc ++ suffix) := by
  rw [encodeFixedArrayStatic_eq elemType vals acc, h_empty]

/-- If encoding vals with accumulator acc succeeds, the result is acc ++ suffix
    where suffix encodes vals from empty. -/
theorem encodeFixedArrayStatic_prefix (elemType : ABIType) (vals : List ABIValue) (acc enc : ByteArray)
    (henc : encodeFixedArrayStatic elemType vals acc = Except.ok enc) :
    ∃ (suffix : ByteArray), encodeFixedArrayStatic elemType vals ByteArray.empty = Except.ok suffix ∧ enc = acc ++ suffix := by
  rw [encodeFixedArrayStatic_eq elemType vals acc] at henc
  cases h_suffix : encodeFixedArrayStatic elemType vals ByteArray.empty
  · simp [h_suffix] at henc
  · rename_i suffix
    simp [h_suffix] at henc
    have henc_eq : enc = acc ++ suffix := by
      have htemp : (Except.ok (acc ++ suffix) : Except String ByteArray) = (Except.ok enc : Except String ByteArray) := by
        simpa [h_suffix] using henc
      have htemp' : acc ++ suffix = enc := by injection htemp
      exact htemp'.symm
    exact ⟨suffix, rfl, henc_eq⟩


/-- Static array roundtrip: encoding vals via encodeFixedArrayStatic followed by
    decodeFixedArray_goStatic recovers (vals, enc.size). -/
theorem static_array_roundtrip (elemType : ABIType) (vals : List ABIValue) (enc : ByteArray)
    (henc : encodeFixedArrayStatic elemType vals ByteArray.empty = Except.ok enc)
    (h_nondyn : isDynamic elemType = false) (h_atomic : isAtomic elemType) :
    decodeFixedArray_goStatic elemType vals.length enc 0 0 [] = Except.ok (vals, enc.size) :=
by
  induction vals generalizing enc with
  | nil =>
    simp [encodeFixedArrayStatic] at henc
    subst henc; simp [decodeFixedArray_goStatic]
  | cons v rest ih =>
    simp [encodeFixedArrayStatic] at henc
    cases h_enc_v : encode elemType v
    · simp [h_enc_v] at henc
    · rename_i enc_v
      simp [h_enc_v] at henc
      have h_sz_v : enc_v.size = 32 := encode_atomic_nondyn_size elemType v enc_v h_enc_v h_nondyn h_atomic
      have h_decode_v : decode elemType enc_v 0 = Except.ok (v, enc_v.size) := by
        cases elemType
        · case uint s => exact roundtrip_uint s v enc_v h_enc_v
        · case int s =>
          cases v
          case int v' => exact roundtrip_int s v' enc_v h_enc_v
          case uint v' => simp [encode] at h_enc_v
          case bool v' => simp [encode] at h_enc_v
          case bytes v' => simp [encode] at h_enc_v
          case string v' => simp [encode] at h_enc_v
          case address v' => simp [encode] at h_enc_v
          case array _ => simp [encode] at h_enc_v
          case tuple _ => simp [encode] at h_enc_v
        · case bool => exact roundtrip_bool v enc_v h_enc_v
        · case bytesM s =>
          cases v
          case bytes v' =>
            unfold encode at h_enc_v; dsimp at h_enc_v
            by_cases hsz : v'.size ≠ s.len
            · simp [hsz] at h_enc_v
            · have hsz_eq : v'.size = s.len := by omega
              simp [hsz_eq] at h_enc_v
              have hdata' : enc_v = padRight v' 32 := h_enc_v.symm
              have h_extract' : (padRight v' 32).extract 0 s.len = v' := padRight_extract_eq v' s.len hsz_eq
              have h_size' : (padRight v' 32).size = 32 := by
                have h_v32 : v'.size ≤ 32 := by rw [hsz_eq]; exact s.h.right
                unfold padRight; split
                · omega
                · have h_lt : v'.size < 32 := by omega
                  calc
                    (v' ++ zeros (32 - v'.size)).size = v'.size + (zeros (32 - v'.size)).size := by simp
                    _ = v'.size + (32 - v'.size) := by simp [zeros_size]
                    _ = 32 := by omega
              unfold decode; rw [hdata']; simp [h_extract', h_size']
          case uint v' => simp [encode] at h_enc_v
          case int v' => simp [encode] at h_enc_v
          case bool v' => simp [encode] at h_enc_v
          case string v' => simp [encode] at h_enc_v
          case address v' => simp [encode] at h_enc_v
          case array _ => simp [encode] at h_enc_v
          case tuple _ => simp [encode] at h_enc_v
        · case address => exact roundtrip_address v enc_v h_enc_v
        · case bytes => simp [isDynamic] at h_nondyn
        · case string => simp [isDynamic] at h_nondyn
        · case array e sOpt => simp [isAtomic] at h_atomic
        · case tuple es => simp [isAtomic] at h_atomic
      rcases encodeFixedArrayStatic_prefix elemType rest enc_v enc henc with ⟨suffix, henc_suffix⟩
      -- h_suff_decode: there's enough data to decode the first element
      have h_suff_decode : 0 + 32 ≤ (enc_v ++ suffix).size := by
        simp [h_sz_v]
      -- Step 1: decode first element at offset 0
      have h_decode_first : decode elemType enc 0 = Except.ok (v, enc_v.size) := by
        rw [henc_suffix.2]
        have h_extract_0_32 : (enc_v ++ suffix).extract 0 32 = enc_v.extract 0 32 := by
          calc
            (enc_v ++ suffix).extract 0 32 = (enc_v ++ suffix).extract 0 enc_v.size := by simp [h_sz_v]
            _ = enc_v := extract_first_n enc_v suffix
            _ = enc_v.extract 0 32 := by rw [← h_sz_v, extract_self enc_v]
        have h_decode_eq : decode elemType (enc_v ++ suffix) 0 = decode elemType enc_v 0 := by
          cases elemType
          · case uint s =>
            unfold decode; simp [h_sz_v, h_extract_0_32]
          · case int s =>
            unfold decode; simp [h_sz_v, h_extract_0_32]
          · case bool =>
            unfold decode; simp [h_sz_v, h_extract_0_32]
          · case bytesM s =>
            have hslen32 : s.len ≤ 32 := s.h.right
            have h_extract_slen : (enc_v ++ suffix).extract 0 s.len = enc_v.extract 0 s.len := by
              calc
                (enc_v ++ suffix).extract 0 s.len = ((enc_v ++ suffix).extract 0 32).extract 0 s.len := by
                  rw [extract_extract_general (enc_v ++ suffix) 0 0 32 s.len (by omega) (by simpa using hslen32)]
                  simp
                _ = (enc_v.extract 0 32).extract 0 s.len := by rw [h_extract_0_32]
                _ = enc_v.extract 0 s.len := by
                  rw [extract_extract_general enc_v 0 0 32 s.len (by omega) (by simpa using hslen32)]
                  simp
            unfold decode; simp [h_sz_v, h_extract_slen]
          · case address =>
            have h_extract_addr : (enc_v ++ suffix).extract 12 32 = enc_v.extract 12 32 := by
              calc
                (enc_v ++ suffix).extract 12 32 = ((enc_v ++ suffix).extract 0 32).extract 12 32 := by
                  rw [extract_extract_general (enc_v ++ suffix) 0 12 32 32 (by omega) (by omega)]
                _ = (enc_v.extract 0 32).extract 12 32 := by rw [h_extract_0_32]
                _ = enc_v.extract 12 32 := by
                  rw [extract_extract_general enc_v 0 12 32 32 (by omega) (by omega)]
            unfold decode; simp [h_sz_v, h_extract_addr]
          · case bytes => unfold isDynamic at h_nondyn; simp at h_nondyn
          · case string => unfold isDynamic at h_nondyn; simp at h_nondyn
          · case array e sOpt => unfold isAtomic at h_atomic; simp at h_atomic
          · case tuple es => unfold isAtomic at h_atomic; simp at h_atomic
        rw [h_decode_eq, h_decode_v]
      have h_first_step : decodeFixedArray_goStatic elemType ((v :: rest).length) enc 0 0 [] =
        decodeFixedArray_goStatic elemType rest.length enc 0 enc_v.size [v] := by
        simp
        rw [decodeFixedArray_goStatic, if_neg (by omega : ¬ 0 ≥ rest.length + 1)]
        simp [h_decode_first]
        rw [goStatic_shift_one elemType enc rest.length 0 enc_v.size [v]]
      rw [h_first_step]
      -- Step 3: use goStatic_prepend_initial to peel off [v]
      have h_prepend : decodeFixedArray_goStatic elemType rest.length enc 0 enc_v.size ([] ++ [v]) =
        (fun (p : List ABIValue × Nat) => (v :: p.1, p.2)) <$> decodeFixedArray_goStatic elemType rest.length enc 0 enc_v.size [] :=
        goStatic_prepend_initial elemType enc rest.length v enc_v.size []
      have h_prepend' : decodeFixedArray_goStatic elemType rest.length enc 0 enc_v.size [v] =
        (fun (p : List ABIValue × Nat) => (v :: p.1, p.2)) <$> decodeFixedArray_goStatic elemType rest.length enc 0 enc_v.size [] := by
        simpa using h_prepend
      rw [h_prepend']
      -- Step 4: henc_suffix already gives the encoding of rest from empty
      have h_rest_empty : encodeFixedArrayStatic elemType rest ByteArray.empty = Except.ok suffix := henc_suffix.1
      have h_suff_sz : suffix.size = rest.length * 32 :=
        encodeFixedArrayStatic_size elemType rest suffix h_rest_empty h_nondyn h_atomic
      have h_suff_gs : 0 + (rest.length - 0) * 32 ≤ suffix.size := by
        rw [h_suff_sz]; omega
      -- Step 5: relate goStatic on enc (starting at enc_v.size) to goStatic on suffix (starting at 0)
      have henc_eq : enc = enc_v ++ suffix := henc_suffix.2
      rw [henc_eq]
      have h_gs := goStatic_offset_shift elemType enc_v suffix rest.length 0 0 [] h_nondyn h_atomic h_suff_gs
      have h_ih := ih suffix h_rest_empty
      calc
        (fun p : List ABIValue × Nat => (v :: p.1, p.2)) <$>
            decodeFixedArray_goStatic elemType rest.length (enc_v ++ suffix) 0 enc_v.size []
            = (fun p : List ABIValue × Nat => (v :: p.1, p.2)) <$>
                ((fun p : List ABIValue × Nat => (p.1, enc_v.size + p.2)) <$>
                  decodeFixedArray_goStatic elemType rest.length suffix 0 0 []) := by
          rw [show decodeFixedArray_goStatic elemType rest.length (enc_v ++ suffix) 0 enc_v.size [] = 
                     (fun (p : List ABIValue × Nat) => (p.1, enc_v.size + p.2)) <$>
                       decodeFixedArray_goStatic elemType rest.length suffix 0 0 [] from h_gs]
        _ = Except.ok (v :: rest, (enc_v ++ suffix).size) := by
          rw [h_ih]
          calc
            (fun p : List ABIValue × Nat => (v :: p.1, p.2)) <$>
              ((fun p : List ABIValue × Nat => (p.1, enc_v.size + p.2)) <$> Except.ok (rest, suffix.size))
                = (fun p : List ABIValue × Nat => (v :: p.1, p.2)) <$> Except.ok (rest, enc_v.size + suffix.size) := by
              simp [Functor.map, Except.map]
            _ = Except.ok (v :: rest, enc_v.size + suffix.size) := by
              simp [Functor.map, Except.map]
            _ = Except.ok (v :: rest, (enc_v ++ suffix).size) := by
              simp [h_sz_v]

termination_by (abiSize elemType, 1, vals.length)
decreasing_by
  · apply Prod.Lex.right (a := abiSize elemType)
    apply Prod.Lex.left; omega
  · apply Prod.Lex.right (a := abiSize elemType)
    apply Prod.Lex.right (a := 1); simp


/-- Universal roundtrip: encoding followed by decoding recovers the original value. -/
theorem roundtrip_aux (t : ABIType) (v : ABIValue) (data : ByteArray) (henc : encode t v = Except.ok data) :
    decode t data 0 = Except.ok (v, data.size) :=
  match t with
  | .uint s => roundtrip_uint s v data henc
  | .int s => by
      cases v
      case int v' => exact roundtrip_int s v' data henc
      case uint v' => simp [encode] at henc
      case bool v' => simp [encode] at henc
      case bytes v' => simp [encode] at henc
      case string v' => simp [encode] at henc
      case address v' => simp [encode] at henc
      case array _ => simp [encode] at henc
      case tuple _ => simp [encode] at henc
  | .bool => roundtrip_bool v data henc
  | .bytesM s => by
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
          have h_size : (padRight v' 32).size = 32 := by
            have h_v32 : v'.size ≤ 32 := by
              rw [hsz_eq]
              exact s.h.right
            unfold padRight; split
            · omega
            · have h_lt : v'.size < 32 := by omega
              calc
                (v' ++ zeros (32 - v'.size)).size = v'.size + (zeros (32 - v'.size)).size := by simp
                _ = v'.size + (32 - v'.size) := by simp [zeros_size]
                _ = 32 := by omega
          unfold decode; rw [hdata]; simp [h_extract, h_size]
      case uint v' => simp [encode] at henc
      case int v' => simp [encode] at henc
      case bool v' => simp [encode] at henc
      case string v' => simp [encode] at henc
      case address v' => simp [encode] at henc
      case array _ => simp [encode] at henc
      case tuple _ => simp [encode] at henc
  | .address => roundtrip_address v data henc
  | .bytes => by
      cases v
      case bytes v' => exact roundtrip_bytes_full v' data henc
      case uint v' => simp [encode] at henc
      case int v' => simp [encode] at henc
      case bool v' => simp [encode] at henc
      case string v' => simp [encode] at henc
      case address v' => simp [encode] at henc
      case array _ => simp [encode] at henc
      case tuple _ => simp [encode] at henc
  | .string => by
      cases v
      case string v' => exact roundtrip_string_full v' data henc
      case uint v' => simp [encode] at henc
      case int v' => simp [encode] at henc
      case bool v' => simp [encode] at henc
      case bytes v' => simp [encode] at henc
      case address v' => simp [encode] at henc
      case array _ => simp [encode] at henc
      case tuple _ => simp [encode] at henc

  | .tuple elems => by
      cases v
      case tuple vals => sorry
      case uint v' => simp [encode] at henc
      case int v' => simp [encode] at henc
      case bool v' => simp [encode] at henc
      case bytes v' => simp [encode] at henc
      case string v' => simp [encode] at henc
      case address v' => simp [encode] at henc
      case array _ => simp [encode] at henc
  | .array elemType sizeOpt => by
      cases v
      case array vals =>
        unfold encode at henc; dsimp at henc
        by_cases h_dyn : isDynamic elemType
        · simp [h_dyn] at henc; sorry
        · simp [h_dyn] at henc
          have h_nondyn : isDynamic elemType = false := by
            simpa using h_dyn
          cases sizeOpt
          · -- Variable-length array
            simp at henc
            by_cases h_len_lt : vals.length < 2 ^ 256
            · split at henc
              · rename_i h_len_lt'
                cases h_enc : encodeFixedArrayStatic elemType vals ByteArray.empty
                · simp [h_enc] at henc
                · rename_i enc
                  simp [h_enc] at henc
                  have hdata : data = uint256ToBytes vals.length ++ enc := henc.symm
                  rw [hdata]
                  have h_atomic : isAtomic elemType := by
                    cases elemType
                    · case uint s => rfl
                    · case int s => rfl
                    · case bool => rfl
                    · case bytesM s => rfl
                    · case address => rfl
                    · case bytes => simp [isDynamic] at h_nondyn
                    · case string => simp [isDynamic] at h_nondyn
                    · case array e s => sorry
                    · case tuple es => sorry
                  have h_enc_size : enc.size = vals.length * 32 :=
                    encodeFixedArrayStatic_size elemType vals enc h_enc h_nondyn h_atomic
                  have h_decode_go : decodeFixedArray_goStatic elemType vals.length enc 0 0 [] = Except.ok (vals, enc.size) :=
                    static_array_roundtrip elemType vals enc h_enc h_nondyn h_atomic
                  have h_len_val : bytesToNat (uint256ToBytes vals.length) = vals.length :=
                    bytesToNat_uint256ToBytes vals.length h_len_lt
                  have h_sz : (uint256ToBytes vals.length).size = 32 := by
                    apply uint256ToBytes_size; exact natToBytes_size_bound vals.length h_len_lt
                  have h_go_shift : decodeFixedArray_goStatic elemType vals.length
                      (uint256ToBytes vals.length ++ enc) 0 32 [] =
                      (fun (p : List ABIValue × Nat) => (p.1, 32 + p.2)) <$>
                      decodeFixedArray_goStatic elemType vals.length enc 0 0 [] := by
                    have h_suff_size : (0 : Nat) + (vals.length - 0) * 32 ≤ enc.size := by
                      rw [h_enc_size]; omega
                    rw [← h_sz]
                    exact goStatic_offset_shift elemType (uint256ToBytes vals.length) enc
                      vals.length 0 0 [] h_nondyn h_atomic h_suff_size
                  unfold decode; simp
                  unfold decodeDynamicArray
                  simp
                  have h_not_short : ¬ ((uint256ToBytes vals.length).size + enc.size < 32) := by
                    rw [h_sz]; omega
                  simp [h_not_short]
                  have h_extract : ((uint256ToBytes vals.length ++ enc).extract 0 32) = uint256ToBytes vals.length := by
                    rw [← h_sz, extract_first_n]
                  simp [h_extract, h_len_val, decodeFixedArray, h_nondyn]
                  rw [h_go_shift, h_decode_go]
                  simp [h_enc_size, h_sz]
              · simp at henc
            · split at henc
              · rename_i h; exfalso; exact h_len_lt h
              · simp at henc
          · rename_i n
            -- Fixed-size array
            have h_len_eq : vals.length = n := by
              by_cases h : vals.length = n
              · exact h
              · exfalso; simp [h] at henc
            simp [h_len_eq] at henc
            cases h_enc_val : encodeFixedArrayStatic elemType vals ByteArray.empty
            · simp [h_enc_val] at henc
            · rename_i encVal
              simp [h_enc_val] at henc
              have h_enc : encodeFixedArrayStatic elemType vals ByteArray.empty = Except.ok encVal := h_enc_val
              have h_atomic : isAtomic elemType := by
                cases elemType
                · case uint s => rfl
                · case int s => rfl
                · case bool => rfl
                · case bytesM s => rfl
                · case address => rfl
                · case bytes => simp [isDynamic] at h_nondyn
                · case string => simp [isDynamic] at h_nondyn
                · case array e sOpt => sorry
                · case tuple es => sorry
              have h_roundtrip := static_array_roundtrip elemType vals encVal h_enc h_nondyn h_atomic
              have hdata : data = encVal := henc.symm
              rw [hdata]
              have h_decode : decode (.array elemType (some n)) encVal 0 = Except.ok (ABIValue.array vals, encVal.size) := by
                simp [decode, decodeFixedArray, h_nondyn]
                rw [← h_len_eq, h_roundtrip]
              exact h_decode
      case uint v' => simp [encode] at henc
      case int v' => simp [encode] at henc
      case bool v' => simp [encode] at henc
      case bytes v' => simp [encode] at henc
      case string v' => simp [encode] at henc
      case address v' => simp [encode] at henc
      case tuple _ => simp [encode] at henc
