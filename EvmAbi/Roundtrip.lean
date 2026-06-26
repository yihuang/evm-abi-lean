/-
# Universal Roundtrip Theorem: encode ∘ decode = id
-/

import EvmAbi.LemmaUtils

open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode
set_option linter.unusedVariables false


/- uint256 encode → decode recovers the original value. -/
theorem roundtrip_uint (byteLen : Nat) (h : byteLen ≤ 32) (v : ABIValue) (data : ByteArray) (henc : encode (.uint byteLen h) v = Except.ok data) :
    decode (.uint byteLen h) data 0 = Except.ok (v, data.size) := by
  cases v
  case uint v' =>
    unfold encode at henc; dsimp at henc
    have hbits256 : byteLen * 8 ≤ 256 := by omega
    by_cases hm : 2 ^ (byteLen * 8) ≤ v'
    · simp [hm] at henc
    · simp [hm] at henc
      have hdata : data = uint256ToBytes v' := henc.symm
      have hrange : v' < 2 ^ (byteLen * 8) := by omega
      have hv256 : v' < 2 ^ 256 := by
        have : 2 ^ (byteLen * 8) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) hbits256
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


theorem roundtrip_int (byteLen : Nat) (h : byteLen ≤ 32) (v' : Int) (data : ByteArray) (henc : encode (.int byteLen h) (ABIValue.int v') = Except.ok data) :
    decode (.int byteLen h) data 0 = Except.ok (ABIValue.int v', data.size) := by
  have hbits256 : byteLen * 8 ≤ 256 := by omega
  unfold encode at henc; dsimp at henc
  by_cases h1 : v' < -(2 ^ (byteLen * 8 - 1) : Int)
  · simp [h1] at henc
  · by_cases h2 : v' ≥ (2 ^ (byteLen * 8 - 1) : Int)
    · simp [h2] at henc
    · simp [h1, h2] at henc
      have hdata : data = intToBytes v' byteLen := henc.symm
      have hrange : -(2 ^ (byteLen * 8 - 1) : Int) ≤ v' ∧ v' < (2 ^ (byteLen * 8 - 1) : Int) := by omega
      by_cases hv_nonneg : v' ≥ 0
      · have hv_lt_nat : v'.toNat < 2 ^ (byteLen * 8 - 1) := by
          apply Int.ofNat_lt.mp
          calc
            (v'.toNat : Int) = v' := by rw [Int.toNat_of_nonneg hv_nonneg]
            _ < (2 ^ (byteLen * 8 - 1) : Int) := hrange.2
        have hv_lt_256 : v'.toNat < 2 ^ 256 := by
          have : v'.toNat < 2 ^ (byteLen * 8 - 1) := hv_lt_nat
          have h_pow : 2 ^ (byteLen * 8 - 1) ≤ 2 ^ 256 :=
            Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have hsize32 : (intToBytes v' byteLen).size = 32 := by
          calc
            (intToBytes v' byteLen).size = (uint256ToBytes v'.toNat).size := by
              simp [intToBytes, uint256ToBytes, hv_nonneg]
            _ = 32 := uint256ToBytes_size v'.toNat (natToBytes_size_bound v'.toNat hv_lt_256)
        have h_self : (intToBytes v' byteLen).extract 0 32 = intToBytes v' byteLen := by
          rw [← hsize32, extract_self]

        have h_val : bytesToNat ((intToBytes v' byteLen).extract 0 32) % 2 ^ (byteLen * 8) = v'.toNat := by
          rw [h_self]
          calc
            bytesToNat (intToBytes v' byteLen) % 2 ^ (byteLen * 8)
                = bytesToNat (uint256ToBytes v'.toNat) % 2 ^ (byteLen * 8) := by
              simp [intToBytes, uint256ToBytes, hv_nonneg]
            _ = v'.toNat % 2 ^ (byteLen * 8) := by
              rw [bytesToNat_uint256ToBytes v'.toNat hv_lt_256]
            _ = v'.toNat := by
              have h_lt_pow : v'.toNat < 2 ^ (byteLen * 8) := by
                have h_pow : 2 ^ (byteLen * 8 - 1) ≤ 2 ^ (byteLen * 8) :=
                  Nat.pow_le_pow_right (by decide) (Nat.sub_le (byteLen * 8) 1)
                omega
              exact Nat.mod_eq_of_lt h_lt_pow
        unfold decode; rw [hdata]
        simp [hsize32, h_val, hv_lt_nat]
        omega
      · sorry

/- dynamic bytes encode → decode recovers the original ByteArray. -/
theorem roundtrip_bytes_full (v' : ByteArray) (data : ByteArray) (henc : encode .bytes (ABIValue.bytes v') = Except.ok data) :
    decode .bytes data 0 = Except.ok (ABIValue.bytes v', data.size) := by
  simp [encode] at henc
  have hdata : data = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size) := henc.symm
  by_cases hv256 : v'.size < 2 ^ 256
  · have ha_sz : (uint256ToBytes v'.size).size = 32 :=
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
  · sorry

/- string encode → decode recovers the original String. -/
theorem roundtrip_string_full (v' : String) (data : ByteArray) (henc : encode .string (ABIValue.string v') = Except.ok data) :
    decode .string data 0 = Except.ok (ABIValue.string v', data.size) := by
  simp [encode] at henc
  let utf8 := v'.toUTF8
  have hdata : data = uint256ToBytes utf8.size ++ padRight utf8 (roundUp32 utf8.size) := henc.symm
  by_cases huv256 : utf8.size < 2 ^ 256
  · have ha_sz : (uint256ToBytes utf8.size).size = 32 :=
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
  · sorry

/- Universal roundtrip: for any type, encode then decode recovers the original value and size. -/
theorem roundtrip_aux (t : ABIType) (v : ABIValue) (data : ByteArray) (henc : encode t v = Except.ok data) :
    decode t data 0 = Except.ok (v, data.size) :=
  match t with
  | .uint byteLen h => roundtrip_uint byteLen h v data henc
  | .int byteLen h => by
      cases v
      case int v' => exact roundtrip_int byteLen h v' data henc
      case uint v' => simp [encode] at henc
      case bool v' => simp [encode] at henc
      case bytes v' => simp [encode] at henc
      case string v' => simp [encode] at henc
      case address v' => simp [encode] at henc
      case array _ => simp [encode] at henc
      case tuple _ => simp [encode] at henc
  | .bool => roundtrip_bool v data henc
  | .bytesM sz h => by
      cases v
      case bytes v' =>
        unfold encode at henc; dsimp at henc
        by_cases hsz : v'.size ≠ sz
        · simp [hsz] at henc
        · have hsz_eq : v'.size = sz := by omega
          simp [hsz_eq] at henc
          have hdata : data = padRight v' 32 := henc.symm
          have h_extract : (padRight v' 32).extract 0 sz = v' :=
            padRight_extract_eq v' sz hsz_eq
          have h_size : (padRight v' 32).size = 32 := by
            have h_v32 : v'.size ≤ 32 := by omega
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
      case array vals =>
        unfold encode at henc; simp at henc
        by_cases h_dyn : isDynamic elemType
        · sorry
        · sorry
      case uint v' => simp [encode] at henc
      case int v' => simp [encode] at henc
      case bool v' => simp [encode] at henc
      case bytes v' => simp [encode] at henc
      case string v' => simp [encode] at henc
      case address v' => simp [encode] at henc
      case tuple _ => simp [encode] at henc
  | .tuple elems => by
      cases v
      case tuple vals =>
        unfold encode at henc; dsimp at henc
        by_cases hl : elems.length ≠ vals.length
        · simp [hl] at henc
        · sorry
      case uint v' => simp [encode] at henc
      case int v' => simp [encode] at henc
      case bool v' => simp [encode] at henc
      case bytes v' => simp [encode] at henc
      case string v' => simp [encode] at henc
      case address v' => simp [encode] at henc
      case array _ => simp [encode] at henc
