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


theorem roundtrip_int (s : ByteSize) (v' : Int) (data : ByteArray) (henc : encode (.int s) (ABIValue.int v') = Except.ok data) :
    decode (.int s) data 0 = Except.ok (ABIValue.int v', data.size) := by
  let byteLen := s.len
  have hbits256 : byteLen * 8 ≤ 256 := by
    have := s.h.right
    omega
  unfold encode at henc; dsimp at henc
  by_cases h1 : v' < -(2 ^ (s.len * 8 - 1) : Int)
  · simp [h1] at henc
  · by_cases h2 : v' ≥ (2 ^ (s.len * 8 - 1) : Int)
    · simp [h2] at henc
    · simp [h1, h2] at henc
      have hdata : data = intToBytes v' s.len := by simpa using henc.symm
      have hrange : -(2 ^ (s.len * 8 - 1) : Int) ≤ v' ∧ v' < (2 ^ (s.len * 8 - 1) : Int) := by omega
      by_cases hv_nonneg : v' ≥ 0
      · have hv_lt_nat : v'.toNat < 2 ^ (s.len * 8 - 1) := by
          apply Int.ofNat_lt.mp
          calc
            (v'.toNat : Int) = v' := by rw [Int.toNat_of_nonneg hv_nonneg]
            _ < (2 ^ (s.len * 8 - 1) : Int) := hrange.2
        have hv_lt_256 : v'.toNat < 2 ^ 256 := by
          have : v'.toNat < 2 ^ (s.len * 8 - 1) := hv_lt_nat
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
        unfold decode; rw [hdata]
        simp [hsize32, h_val, hv_lt_nat]
        omega
      · -- v' < 0
        let b := s.len * 8
        have hbpos : 0 < b := by
          have hpos : 0 < s.len := s.h.left
          omega
        have hun_nonneg : 0 ≤ (2 ^ b : Int) + v' := by
          have h_lb : -(2 ^ (b - 1) : Int) ≤ v' := hrange.1
          have h_diff : (2 ^ b : Int) - (2 ^ (b - 1) : Int) = (2 ^ (b - 1) : Int) :=
            two_pow_succ_sub b hbpos
          omega
        let unsigned : Nat := ((2 ^ b : Int) + v').toNat
        have h_unsigned_lt : unsigned < 2 ^ b := by
          have h_lt : (2 ^ b : Int) + v' < (2 ^ b : Int) := by omega
          have h_nonneg2 : 0 ≤ (2 ^ b : Int) := two_pow_nonneg b
          have h_pos2b : 0 < (2 ^ b : Int) := by
            induction b with
            | zero => omega
            | succ b ih =>
              rw [show (2 : Int) ^ (b+1) = (2 : Int) ^ b * (2 : Int) from rfl]
              exact Int.mul_pos ih (by omega : 0 < (2 : Int))
          have h_toNat : ((2 ^ b : Int) + v').toNat < (2 ^ b : Int).toNat :=
            ((Int.toNat_lt_toNat (h_pos2b : 0 < (2 ^ b : Int))).mpr h_lt)
          simpa [unsigned, show ((2 ^ b : Int).toNat : Nat) = (2 : Nat) ^ b from two_toNat_eq b]
            using h_toNat
        have h_unsigned_ge : 2 ^ (b - 1) ≤ unsigned := by
          have h_ge : (2 ^ (b - 1) : Int) ≤ (2 ^ b : Int) + v' := by
            have h_lb : -(2 ^ (b - 1) : Int) ≤ v' := hrange.1
            have h_diff : (2 ^ b : Int) - (2 ^ (b - 1) : Int) = (2 ^ (b - 1) : Int) :=
              two_pow_succ_sub b hbpos
            have h_two_b : (2 ^ b : Int) = 2 * (2 : Int) ^ (b - 1) := by omega
            omega
          have h_ge_nat : (2 ^ (b - 1) : Nat) ≤ unsigned := by
            have h_toNat := Int.toNat_le_toNat h_ge
            have h_left : ((2 : Int) ^ (b - 1)).toNat = (2 : Nat) ^ (b - 1) :=
              two_toNat_eq (b - 1)
            simpa [unsigned, h_left] using h_toNat
          exact h_ge_nat
        have h_unsigned_lt_256 : unsigned < 2 ^ 256 := by
          have : 2 ^ b ≤ 2 ^ 256 :=
            Nat.pow_le_pow_right (by omega) (by
              have := s.h.right
              omega)
          omega
        have hv_nonpos : ¬ v' ≥ 0 := by omega
        have h_raw_sz : (natToBytes unsigned).size = s.len := by
          apply natToBytes_size_range unsigned s.len (by
            have := s.h.left
            exact this)
          · have : 2 ^ (s.len * 8 - 1) = 2 ^ (b - 1) := by
              simp [b]
            rw [this]
            exact h_unsigned_ge
          · simpa [b] using h_unsigned_lt
        have hsize32 : (intToBytes v' s.len).size = 32 :=
          intToBytes_neg_size v' s.len hv_nonpos
            (by
              simpa [b, unsigned] using h_unsigned_lt_256)
        have h_self : (intToBytes v' s.len).extract 0 32 = intToBytes v' s.len := by
          rw [← hsize32, extract_self]
        have h_256_eq_2b : 256 ^ s.len = 2 ^ b := by
          have h256 : (256 : Nat) = (2 : Nat) ^ 8 := by native_decide
          calc
            256 ^ s.len = ((2 : Nat) ^ 8) ^ s.len := by rw [h256]
            _ = 2 ^ (8 * s.len) := by rw [Nat.pow_mul]
            _ = 2 ^ (s.len * 8) := by simp [Nat.mul_comm]
            _ = 2 ^ b := rfl
        have ha_sz : (ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF))).size = 32 - s.len := by
          unfold ByteArray.size; simp
        have h_formula : intToBytes v' s.len = (ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF))) ++ (natToBytes unsigned) := by
          unfold intToBytes
          split
          · exfalso; exact hv_nonpos (by omega)
          · simp [unsigned, b, h_raw_sz]
        have h_suffix : (intToBytes v' s.len).extract (32 - s.len) 32 = natToBytes unsigned := by
          rw [h_formula]
          have h := extract_after_suffix (ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF))) (natToBytes unsigned) (natToBytes unsigned).size
          have ha_sz' : ({ data := Array.replicate (32 - s.len) 255 } : ByteArray).size = 32 - s.len := by
            unfold ByteArray.size; simp
          have h_add : 32 - s.len + s.len = 32 := by omega
          have h' : (({ data := Array.replicate (32 - s.len) 255 } : ByteArray) ++ natToBytes unsigned).extract (32 - s.len) 32
              = (natToBytes unsigned).extract 0 (natToBytes unsigned).size := by
            simpa [ha_sz', h_add, h_raw_sz] using h
          calc
            (({ data := Array.replicate (32 - s.len) 255 } : ByteArray) ++ natToBytes unsigned).extract (32 - s.len) 32
                = (natToBytes unsigned).extract 0 (natToBytes unsigned).size := h'
            _ = natToBytes unsigned := extract_self (natToBytes unsigned)
        have h_masked : bytesToNat ((intToBytes v' s.len).extract 0 32) % (2 ^ b) = unsigned := by
          rw [h_self, h_formula, bytesToNat_append_general (ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF))) (natToBytes unsigned), h_raw_sz,
            bytesToNat_natToBytes unsigned, h_256_eq_2b]
          have h_mod : (bytesToNat (ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF))) * (2 ^ b) + unsigned) % (2 ^ b) = unsigned := by
            simp [Nat.add_mod, Nat.mod_eq_of_lt h_unsigned_lt]
          exact h_mod
        have h_ge_half : 2 ^ (b - 1) ≤ bytesToNat ((intToBytes v' s.len).extract 0 32) % (2 ^ b) := by
          rw [h_masked]
          exact h_unsigned_ge
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
        unfold decode; rw [hdata]
        simp [hsize32]
        have h_masked' : bytesToNat (intToBytes v' s.len) % 2 ^ (s.len * 8) = unsigned := by
          simpa [h_self, b] using h_masked
        have h_not_lt' : ¬ unsigned < 2 ^ (s.len * 8 - 1) := by
          have : 2 ^ (s.len * 8 - 1) = 2 ^ (b - 1) := by simp [b]
          rw [this]
          omega
        have h_decode_val' : -(Int.ofNat (2 ^ (s.len * 8) - unsigned)) = v' := by
          simpa [b] using h_decode_val
        rw [h_self]
        simp [h_not_lt', h_masked']
        exact h_decode_val'

/- dynamic bytes encode → decode recovers the original ByteArray. -/
theorem roundtrip_bytes_full (v' : ByteArray) (data : ByteArray) (henc : encode .bytes (ABIValue.bytes v') = Except.ok data) :
    decode .bytes data 0 = Except.ok (ABIValue.bytes v', data.size) := by
  simp [encode] at henc; split at henc
  · rename_i hv256
    have hdata : data = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size) := by
      simpa using henc.symm
    have ha_sz : (uint256ToBytes v'.size).size = 32 :=
      uint256ToBytes_size v'.size (natToBytes_size_bound v'.size hv256)
    have h_roundUp_ge : v'.size ≤ roundUp32 v'.size := by
      have : roundUp32 v'.size = ((v'.size + 31) / 32) * 32 := rfl
      omega
    have h_pad_sz : (padRight v' (roundUp32 v'.size)).size = roundUp32 v'.size := by
      unfold padRight; split
      · omega
      · simp [zeros_size]; omega
    have h_extract_len : data.extract 0 32 = uint256ToBytes v'.size := by
      rw [hdata, ← ha_sz]
      exact extract_first_n (uint256ToBytes v'.size) (padRight v' (roundUp32 v'.size))
    have h_len : bytesToNat (data.extract 0 32) = v'.size := by
      rw [h_extract_len, bytesToNat_uint256ToBytes v'.size hv256]
    have h_extract_val : data.extract 32 (32 + v'.size) = v' := by
      rw [hdata, roundtrip_bytes_val v' hv256]
    unfold decode; rw [hdata]; unfold decodeDynamicBytes
    have h_size : (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)).size = 32 + roundUp32 v'.size := by
      simp [ha_sz, h_pad_sz]
    have h1 : ¬ (32 > 32 + roundUp32 v'.size) := by omega
    have h_len' : bytesToNat ((uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)).extract 0 32) = v'.size := by
      simpa [hdata] using h_len
    have h_extract_val' : (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)).extract 32 (32 + v'.size) = v' := by
      simpa [hdata] using h_extract_val
    simp [h_size, h1, h_len', h_extract_val', h_roundUp_ge]
  · simp at henc

/- string encode → decode recovers the original String. -/
theorem roundtrip_string_full (v' : String) (data : ByteArray) (henc : encode .string (ABIValue.string v') = Except.ok data) :
    decode .string data 0 = Except.ok (ABIValue.string v', data.size) := by
  simp [encode] at henc; split at henc
  · rename_i huv256
    let utf8 := v'.toUTF8
    have hdata : data = uint256ToBytes utf8.size ++ padRight utf8 (roundUp32 utf8.size) := by
      simpa [utf8] using henc.symm
    have ha_sz : (uint256ToBytes utf8.size).size = 32 :=
      uint256ToBytes_size utf8.size (natToBytes_size_bound utf8.size huv256)
    have h_roundUp_ge : utf8.size ≤ roundUp32 utf8.size := by
      have : roundUp32 utf8.size = ((utf8.size + 31) / 32) * 32 := rfl
      omega
    have h_pad_sz : (padRight utf8 (roundUp32 utf8.size)).size = roundUp32 utf8.size := by
      unfold padRight; split
      · omega
      · simp [zeros_size]; omega
    have h_extract_len : data.extract 0 32 = uint256ToBytes utf8.size := by
      rw [hdata, ← ha_sz]
      exact extract_first_n (uint256ToBytes utf8.size) (padRight utf8 (roundUp32 utf8.size))
    have h_len : bytesToNat (data.extract 0 32) = utf8.size := by
      rw [h_extract_len, bytesToNat_uint256ToBytes utf8.size huv256]
    have h_extract_val : data.extract 32 (32 + utf8.size) = utf8 := by
      rw [hdata, roundtrip_bytes_val utf8 huv256]
    unfold decode; rw [hdata]; unfold decodeDynamicString
    have h_from_utf8 : String.fromUTF8! utf8 = v' := by
      dsimp [utf8]; exact fromUTF8!_toUTF8 v'
    have h_size : (uint256ToBytes utf8.size ++ padRight utf8 (roundUp32 utf8.size)).size = 32 + roundUp32 utf8.size := by
      simp [ha_sz, h_pad_sz]
    have h1 : ¬ (32 > 32 + roundUp32 utf8.size) := by omega
    have h2 : ¬ (32 + utf8.size > 32 + roundUp32 utf8.size) := by omega
    have h_len' : bytesToNat ((uint256ToBytes utf8.size ++ padRight utf8 (roundUp32 utf8.size)).extract 0 32) = utf8.size := by
      simpa [hdata] using h_len
    have h_extract_val' : (uint256ToBytes utf8.size ++ padRight utf8 (roundUp32 utf8.size)).extract 32 (32 + utf8.size) = utf8 := by
      simpa [hdata] using h_extract_val
    simp [h_size, h1, h_len', h_extract_val', h_from_utf8, h_roundUp_ge]
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
    case int v' => unfold encode at henc; simp at henc
    case bool v' => unfold encode at henc; simp at henc
    case bytes v' => unfold encode at henc; simp at henc
    case string v' => unfold encode at henc; simp at henc
    case address v' => unfold encode at henc; simp at henc
    case array v' => unfold encode at henc; simp at henc
    case tuple v' => unfold encode at henc; simp at henc
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
              have hpos : 0 < (2 : Int) ^ (s.len * 8) := by
                have h_nat_pos : (0 : Nat) < (2 : Nat) ^ (s.len * 8) := by
                  induction s.len * 8 with
                  | zero => decide
                  | succ n ih =>
                    rw [Nat.pow_succ]
                    exact Nat.mul_pos ih (by omega)
                have : ((0 : Nat) : Int) < ((2 : Nat) ^ (s.len * 8) : Int) :=
                  Int.ofNat_lt.mpr h_nat_pos
                simpa
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
    case uint v' => unfold encode at henc; simp at henc
    case bool v' => unfold encode at henc; simp at henc
    case bytes v' => unfold encode at henc; simp at henc
    case string v' => unfold encode at henc; simp at henc
    case address v' => unfold encode at henc; simp at henc
    case array v' => unfold encode at henc; simp at henc
    case tuple v' => unfold encode at henc; simp at henc
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
    case int v' => unfold encode at henc; simp at henc
    case uint v' => unfold encode at henc; simp at henc
    case bytes v' => unfold encode at henc; simp at henc
    case string v' => unfold encode at henc; simp at henc
    case address v' => unfold encode at henc; simp at henc
    case array v' => unfold encode at henc; simp at henc
    case tuple v' => unfold encode at henc; simp at henc
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
    case int v' => unfold encode at henc; simp at henc
    case uint v' => unfold encode at henc; simp at henc
    case bool v' => unfold encode at henc; simp at henc
    case string v' => unfold encode at henc; simp at henc
    case address v' => unfold encode at henc; simp at henc
    case array v' => unfold encode at henc; simp at henc
    case tuple v' => unfold encode at henc; simp at henc
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
    case int v' => unfold encode at henc; simp at henc
    case uint v' => unfold encode at henc; simp at henc
    case bool v' => unfold encode at henc; simp at henc
    case bytes v' => unfold encode at henc; simp at henc
    case string v' => unfold encode at henc; simp at henc
    case array v' => unfold encode at henc; simp at henc
    case tuple v' => unfold encode at henc; simp at henc
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
  | .array elemType sizeOpt => by
      cases v
      case array vals => sorry
      case uint v' => simp [encode] at henc
      case int v' => simp [encode] at henc
      case bool v' => simp [encode] at henc
      case bytes v' => simp [encode] at henc
      case string v' => simp [encode] at henc
      case address v' => simp [encode] at henc
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
