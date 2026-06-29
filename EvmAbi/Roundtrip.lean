/-
# Universal Roundtrip Theorem via ABIVisitor
-/

import EvmAbi.LemmaUtils
open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode
set_option autoImplicit false

structure RoundtripVisitor (t : ABIType) : Type where
  roundtrip : ∀ (v : ABIValue) (data : ByteArray), encode t v = Except.ok data → decode t data 0 = Except.ok (v, data.size)

/-! ## Dynamic bytes/string helpers -/

private lemma dynamicRoundtrip_preamble (b : ByteArray) (hb256 : b.size < 2 ^ 256) :
    (uint256ToBytes b.size).size = 32 ∧ (padRight b (roundUp32 b.size)).size = roundUp32 b.size ∧
    b.size ≤ roundUp32 b.size ∧ (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).size = 32 + roundUp32 b.size ∧
    bytesToNat ((uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 0 32) = b.size ∧
    (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 32 (32 + b.size) = b := by
  have ha_sz : (uint256ToBytes b.size).size = 32 := uint256ToBytes_size b.size (natToBytes_size_bound b.size hb256)
  have h_roundUp_ge : b.size ≤ roundUp32 b.size := by unfold roundUp32; omega
  have h_pad_sz : (padRight b (roundUp32 b.size)).size = roundUp32 b.size := by
    unfold padRight; split; omega; simp [zeros_size]; omega
  have h_size : (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).size = 32 + roundUp32 b.size := by simp [ha_sz, h_pad_sz]
  have h_len : bytesToNat ((uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 0 32) = b.size := by
    rw [← ha_sz, extract_first_n, bytesToNat_uint256ToBytes b.size]
  have h_extract_val : (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 32 (32 + b.size) = b := roundtrip_bytes_val b hb256
  exact ⟨ha_sz, h_pad_sz, h_roundUp_ge, h_size, h_len, h_extract_val⟩

private lemma decodeDynamicBytes_roundtrip (v' : ByteArray) (hv256 : v'.size < 2 ^ 256) (data : ByteArray)
    (hdata : data = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)) :
    decodeDynamicBytes data 0 = Except.ok (.bytes v', data.size) := by
  rw [hdata]; rcases dynamicRoundtrip_preamble v' hv256 with ⟨_, _, h_roundUp_ge, h_size, h_len, h_extract_val⟩
  unfold decodeDynamicBytes; simp [h_size, h_len, h_extract_val, h_roundUp_ge]

private lemma decodeDynamicString_roundtrip (v' : String) (hv256 : v'.toUTF8.size < 2 ^ 256) (data : ByteArray)
    (hdata : data = uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size)) :
    decodeDynamicString data 0 = Except.ok (.string v', data.size) := by
  rw [decodeDynamicString, decodeDynamicBytes_roundtrip v'.toUTF8 hv256 data hdata]
  simp [Except.map]; have h : v'.toByteArray = v'.toUTF8 := rfl; rw [h, fromUTF8!_toUTF8 v']

/-! ## Atomic proofs -/
/- Each theorem uses `match v` to pattern-match. The fallback `x` case
   derives a contradiction by showing encode must fail for wrong types. -/

theorem roundtrip_uint (s : ByteSize) (v : ABIValue) (data : ByteArray)
    (henc : encode (.uint s) v = Except.ok data) : decode (.uint s) data 0 = Except.ok (v, data.size) := by
  match v with
  | .uint v' =>
    unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    by_cases hm : v' < 2 ^ (s.len * 8)
    · simp [hm] at henc
      have hd : uint256ToBytes v' = data := henc
      rw [hd.symm]
      unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
      have hv256 : v' < 2 ^ 256 := by
        have hbits256 : s.len * 8 ≤ 256 := by have := s.h.right; omega
        have hp : 2 ^ (s.len * 8) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) hbits256
        omega
      have hsize32 : (uint256ToBytes v').size = 32 := uint256ToBytes_size v' (natToBytes_size_bound v' hv256)
      have h_val : bytesToNat ((uint256ToBytes v').extract 0 32) = v' := by
        calc
          bytesToNat ((uint256ToBytes v').extract 0 32) = bytesToNat (uint256ToBytes v') := by rw [← hsize32, extract_self]
          _ = v' := bytesToNat_uint256ToBytes v'
      simp [hsize32, h_val, hm]
    · simp [hm] at henc
  | x =>
    unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    cases x with
    | uint v' =>
      by_cases hm : v' < 2 ^ (s.len * 8)
      · simp [hm] at henc
        have hd : uint256ToBytes v' = data := henc
        rw [hd.symm]
        unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
        have hv256 : v' < 2 ^ 256 := by
          have hbits256 : s.len * 8 ≤ 256 := by have := s.h.right; omega
          have hp : 2 ^ (s.len * 8) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) hbits256
          omega
        have hsize32 : (uint256ToBytes v').size = 32 := uint256ToBytes_size v' (natToBytes_size_bound v' hv256)
        have h_val : bytesToNat ((uint256ToBytes v').extract 0 32) = v' := by
          calc
            bytesToNat ((uint256ToBytes v').extract 0 32) = bytesToNat (uint256ToBytes v') := by rw [← hsize32, extract_self]
            _ = v' := bytesToNat_uint256ToBytes v'
        simp [hsize32, h_val, hm]
      · simp [hm] at henc
    | _ => simp at henc

theorem roundtrip_bool (v : ABIValue) (data : ByteArray)
    (henc : encode .bool v = Except.ok data) : decode .bool data 0 = Except.ok (v, data.size) := by
  match v with
  | .bool v' =>
    unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    simp at henc
    have hd : uint256ToBytes (if v' then 1 else 0) = data := henc
    rw [hd.symm]
    unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
    have hbits : (if v' then 1 else 0) < 2 ^ 256 := by split <;> omega
    have hsize32 : (uint256ToBytes (if v' then 1 else 0)).size = 32 :=
      uint256ToBytes_size (if v' then 1 else 0) (natToBytes_size_bound (if v' then 1 else 0) hbits)
    have h_val : bytesToNat ((uint256ToBytes (if v' then 1 else 0)).extract 0 32) = (if v' then 1 else 0) := by
      calc
        bytesToNat ((uint256ToBytes (if v' then 1 else 0)).extract 0 32) = bytesToNat (uint256ToBytes (if v' then 1 else 0)) := by
          rw [← hsize32, extract_self]
        _ = (if v' then 1 else 0) := bytesToNat_uint256ToBytes (if v' then 1 else 0)
    simp [hsize32]; rw [h_val]; cases v' <;> simp
  | x =>
    unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    cases x with
    | bool v' =>
      simp at henc
      have hd : uint256ToBytes (if v' then 1 else 0) = data := henc
      rw [hd.symm]
      unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
      have hbits : (if v' then 1 else 0) < 2 ^ 256 := by split <;> omega
      have hsize32 : (uint256ToBytes (if v' then 1 else 0)).size = 32 :=
        uint256ToBytes_size (if v' then 1 else 0) (natToBytes_size_bound (if v' then 1 else 0) hbits)
      have h_val : bytesToNat ((uint256ToBytes (if v' then 1 else 0)).extract 0 32) = (if v' then 1 else 0) := by
        calc
          bytesToNat ((uint256ToBytes (if v' then 1 else 0)).extract 0 32) = bytesToNat (uint256ToBytes (if v' then 1 else 0)) := by
            rw [← hsize32, extract_self]
          _ = (if v' then 1 else 0) := bytesToNat_uint256ToBytes (if v' then 1 else 0)
      simp [hsize32]; rw [h_val]; cases v' <;> simp
    | _ => simp at henc

theorem roundtrip_address (v : ABIValue) (data : ByteArray)
    (henc : encode .address v = Except.ok data) : decode .address data 0 = Except.ok (v, data.size) := by
  match v with
  | .address v' =>
    unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    by_cases hsize : v'.size ≠ 20
    · simp [hsize] at henc
    · have hsize20 : v'.size = 20 := by omega
      simp [hsize20] at henc
      have hd : padLeft v' 32 = data := henc
      subst hd
      unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
      have h_extract : (padLeft v' 32).extract 12 32 = v' := padLeft_extract_address v' hsize20
      have h_sz : (padLeft v' 32).size = 32 := by
        unfold padLeft; simp [hsize20, zeros_size]
      simp [hsize20, h_extract, h_sz]
  | x =>
    unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    cases x with
    | address v' =>
      by_cases hsize : v'.size ≠ 20
      · simp [hsize] at henc
      · have hsize20 : v'.size = 20 := by omega
        simp [hsize20] at henc
        have hd : padLeft v' 32 = data := henc
        subst hd
        unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
        have h_extract : (padLeft v' 32).extract 12 32 = v' := padLeft_extract_address v' hsize20
        have h_sz : (padLeft v' 32).size = 32 := by
          unfold padLeft; simp [hsize20, zeros_size]
        simp [hsize20, h_extract, h_sz]
    | _ => simp at henc

theorem roundtrip_fixedBytes (s : ByteSize) (v : ABIValue) (data : ByteArray)
    (henc : encode (.fixedBytes s) v = Except.ok data) : decode (.fixedBytes s) data 0 = Except.ok (v, data.size) := by
  match v with
  | .bytes v' =>
    unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    by_cases hsz : v'.size = s.len
    · simp [hsz] at henc
      have hd : padRight v' 32 = data := henc
      subst hd
      unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
      have h_extract : (padRight v' 32).extract 0 s.len = v' := padRight_extract_eq v' s.len hsz
      have h_size : (padRight v' 32).size = 32 := padRight_size_32 v' (by rw [hsz]; exact s.h.right)
      simp [h_extract, h_size]
    · simp [hsz] at henc
  | x =>
    unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    cases x with
    | bytes v' =>
      by_cases hsz : v'.size = s.len
      · simp [hsz] at henc
        have hd : padRight v' 32 = data := henc
        subst hd
        unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
        have h_extract : (padRight v' 32).extract 0 s.len = v' := padRight_extract_eq v' s.len hsz
        have h_size : (padRight v' 32).size = 32 := padRight_size_32 v' (by rw [hsz]; exact s.h.right)
        simp [h_extract, h_size]
      · simp [hsz] at henc
    | _ => simp at henc

theorem roundtrip_bytes (v : ABIValue) (data : ByteArray)
    (henc : encode .bytes v = Except.ok data) : decode .bytes data 0 = Except.ok (v, data.size) := by
  have h256_eq : (2 : ℕ) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by native_decide
  cases v with
  | bytes v' =>
    by_cases hv256 : v'.size < 2 ^ 256
    · have hval : encode .bytes (ABIValue.bytes v') = Except.ok (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)) := by
        unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp; simpa [h256_eq, hv256]
      have hd : data = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size) := by
        injection hval.symm.trans henc; symm; assumption
      rw [hd]
      unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
      exact decodeDynamicBytes_roundtrip v' hv256 (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)) rfl
    · have hval : encode .bytes (ABIValue.bytes v') = Except.error (.dataTooLong v'.size) := by
        unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
        have h_ge : ¬ v'.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
          rw [← h256_eq]; exact hv256
        simp [h_ge]
      rw [hval] at henc; simp at henc
  | uint n =>
    have h_wrong : encode .bytes (ABIValue.uint n) = Except.error .typeValueMismatch := by
      unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
    rw [h_wrong] at henc; simp at henc
  | bool b =>
    have h_wrong : encode .bytes (ABIValue.bool b) = Except.error .typeValueMismatch := by
      unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
    rw [h_wrong] at henc; simp at henc
  | address a =>
    have h_wrong : encode .bytes (ABIValue.address a) = Except.error .typeValueMismatch := by
      unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
    rw [h_wrong] at henc; simp at henc
  | int i =>
    have h_wrong : encode .bytes (ABIValue.int i) = Except.error .typeValueMismatch := by
      unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
    rw [h_wrong] at henc; simp at henc
  | string s =>
    have h_wrong : encode .bytes (ABIValue.string s) = Except.error .typeValueMismatch := by
      unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
    rw [h_wrong] at henc; simp at henc
  | array arr =>
    have h_wrong : encode .bytes (ABIValue.array arr) = Except.error .typeValueMismatch := by
      unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
    rw [h_wrong] at henc; simp at henc
  | tuple tup =>
    have h_wrong : encode .bytes (ABIValue.tuple tup) = Except.error .typeValueMismatch := by
      unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
    rw [h_wrong] at henc; simp at henc

theorem roundtrip_string (v : ABIValue) (data : ByteArray)
    (henc : encode .string v = Except.ok data) : decode .string data 0 = Except.ok (v, data.size) := by
  have h256_eq : (2 : ℕ) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by native_decide
  cases v with
  | string v' =>
    by_cases huv256 : v'.toUTF8.size < 2 ^ 256
    · have hval : encode .string (ABIValue.string v') = Except.ok (uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size)) := by
        unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp; simpa [h256_eq, huv256]
      have hd : data = uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size) := by
        injection hval.symm.trans henc; symm; assumption
      rw [hd]
      unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
      exact decodeDynamicString_roundtrip v' huv256 (uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size)) rfl
    · have hval : encode .string (ABIValue.string v') = Except.error (.dataTooLong v'.toUTF8.size) := by
        unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
        have h_ge : ¬ v'.toUTF8.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
          rw [← h256_eq]; exact huv256
        have h_ge' : ¬ v'.utf8ByteSize < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
          simpa using h_ge
        simp [h_ge']
      rw [hval] at henc; simp at henc
  | uint n =>
    have h_wrong : encode .string (ABIValue.uint n) = Except.error .typeValueMismatch := by
      unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
    rw [h_wrong] at henc; simp at henc
  | bool b =>
    have h_wrong : encode .string (ABIValue.bool b) = Except.error .typeValueMismatch := by
      unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
    rw [h_wrong] at henc; simp at henc
  | address a =>
    have h_wrong : encode .string (ABIValue.address a) = Except.error .typeValueMismatch := by
      unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
    rw [h_wrong] at henc; simp at henc
  | int i =>
    have h_wrong : encode .string (ABIValue.int i) = Except.error .typeValueMismatch := by
      unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
    rw [h_wrong] at henc; simp at henc
  | bytes b =>
    have h_wrong : encode .string (ABIValue.bytes b) = Except.error .typeValueMismatch := by
      unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
    rw [h_wrong] at henc; simp at henc
  | array arr =>
    have h_wrong : encode .string (ABIValue.array arr) = Except.error .typeValueMismatch := by
      unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
    rw [h_wrong] at henc; simp at henc
  | tuple tup =>
    have h_wrong : encode .string (ABIValue.tuple tup) = Except.error .typeValueMismatch := by
      unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
    rw [h_wrong] at henc; simp at henc

/-! ## Int helper lemmas -/

private theorem intToBytes_decode_nonneg (s : ByteSize) (v' : Int) (hv_nonneg : v' ≥ 0)
    (hrange : v' < (2 ^ (s.len * 8 - 1) : Int)) (hbits256 : s.len * 8 ≤ 256) :
    decode (.int s) (intToBytes v' s.len) 0 = Except.ok (ABIValue.int v', (intToBytes v' s.len).size) := by
  unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
  have hv_lt_nat : v'.toNat < 2 ^ (s.len * 8 - 1) := by
    apply Int.ofNat_lt.mp
    calc
      (v'.toNat : ℤ) = v' := by exact_mod_cast Int.toNat_of_nonneg hv_nonneg
      _ < (2 ^ (s.len * 8 - 1) : ℤ) := hrange
  have hv_lt_256 : v'.toNat < 2 ^ 256 := by
    have h_pow : 2 ^ (s.len * 8 - 1) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by omega)
    have h_bound : v'.toNat < 2 ^ (s.len * 8 - 1) := hv_lt_nat
    exact lt_of_lt_of_le h_bound h_pow
  have hsize32 : (intToBytes v' s.len).size = 32 := by
    calc
      (intToBytes v' s.len).size = (uint256ToBytes v'.toNat).size := by simp [intToBytes, uint256ToBytes, hv_nonneg]
      _ = 32 := uint256ToBytes_size v'.toNat (natToBytes_size_bound v'.toNat hv_lt_256)
  have h_self : (intToBytes v' s.len).extract 0 32 = intToBytes v' s.len := by rw [← hsize32, extract_self]
  have h_lt_pow : v'.toNat < 2 ^ (s.len * 8) := by
    have h_pow : 2 ^ (s.len * 8 - 1) ≤ 2 ^ (s.len * 8) :=
      Nat.pow_le_pow_right (by omega) (Nat.sub_le (s.len * 8) 1)
    exact lt_of_lt_of_le hv_lt_nat h_pow
  have h_val : bytesToNat ((intToBytes v' s.len).extract 0 32) % 2 ^ (s.len * 8) = v'.toNat := by
    rw [h_self]
    calc
      bytesToNat (intToBytes v' s.len) % 2 ^ (s.len * 8) = bytesToNat (uint256ToBytes v'.toNat) % 2 ^ (s.len * 8) := by
        simp [intToBytes, uint256ToBytes, hv_nonneg]
      _ = v'.toNat % 2 ^ (s.len * 8) := by rw [bytesToNat_uint256ToBytes v'.toNat]
      _ = v'.toNat := Nat.mod_eq_of_lt h_lt_pow
  have h_val_int : (bytesToNat ((intToBytes v' s.len).extract 0 32) : ℤ) % ((2 : ℤ) ^ (s.len * 8)) = (v'.toNat : ℤ) := by
    exact_mod_cast h_val
  have h_nonneg_int : (v'.toNat : ℤ) = v' := by exact_mod_cast Int.toNat_of_nonneg hv_nonneg
  have hsize32_int : ((intToBytes v' s.len).size : ℤ) = (32 : ℤ) := by exact_mod_cast hsize32
  have hv_lt_nat_int : (v'.toNat : ℤ) < (2 : ℤ) ^ (s.len * 8 - 1) := by exact_mod_cast hv_lt_nat
  simpa [hsize32, hsize32_int, h_val, h_val_int, hv_lt_nat, hv_lt_nat_int, h_nonneg_int]

private theorem intToBytes_decode_neg (s : ByteSize) (v' : Int) (hv_neg : ¬ v' ≥ 0)
    (hrange : -(2 ^ (s.len * 8 - 1) : Int) ≤ v') (hbits256 : s.len * 8 ≤ 256) :
    decode (.int s) (intToBytes v' s.len) 0 = Except.ok (ABIValue.int v', (intToBytes v' s.len).size) := by
  unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
  let b := s.len * 8; have hbpos : 0 < b := by have hpos : 0 < s.len := s.h.left; omega
  have hun_nonneg : 0 ≤ (2 ^ b : Int) + v' := by
    have h_lb : -(2 ^ (b - 1) : Int) ≤ v' := by simpa [b] using hrange
    have h_diff : (2 ^ b : Int) - (2 ^ (b - 1) : Int) = (2 ^ (b - 1) : Int) := two_pow_succ_sub b hbpos; omega
  let unsigned : Nat := ((2 ^ b : Int) + v').toNat
  have h_unsigned_lt : unsigned < 2 ^ b := by
    have h_lt : (2 ^ b : Int) + v' < (2 ^ b : Int) := by omega
    have h_pos2b : 0 < (2 ^ b : Int) := by positivity
    have h_toNat : ((2 ^ b : Int) + v').toNat < (2 ^ b : Int).toNat := (Int.toNat_lt_toNat h_pos2b).mpr h_lt
    simpa [unsigned, two_toNat_eq b] using h_toNat
  have h_unsigned_ge : 2 ^ (b - 1) ≤ unsigned := by
    have h_ge : (2 ^ (b - 1) : Int) ≤ (2 ^ b : Int) + v' := by
      have h_lb : -(2 ^ (b - 1) : Int) ≤ v' := by simpa [b] using hrange
      have h_diff : (2 ^ b : Int) - (2 ^ (b - 1) : Int) = (2 ^ (b - 1) : Int) := two_pow_succ_sub b hbpos; omega
    have h_ge_nat : (2 ^ (b - 1) : Nat) ≤ unsigned := by
      have h_toNat := Int.toNat_le_toNat h_ge; simpa [unsigned, two_toNat_eq (b - 1)] using h_toNat
    exact h_ge_nat
  have h_unsigned_lt_256 : unsigned < 2 ^ 256 := by
    have h_pow : 2 ^ b ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by omega); omega
  have hsize32 : (intToBytes v' s.len).size = 32 :=
    intToBytes_neg_size v' s.len (by omega) (by simpa [b, unsigned] using h_unsigned_lt_256)
  have h_self : (intToBytes v' s.len).extract 0 32 = intToBytes v' s.len := by rw [← hsize32, extract_self]
  have h_raw_sz : (natToBytes unsigned).size = s.len :=
    natToBytes_size_range unsigned s.len s.h.left
      (by
        have h_eq : s.len * 8 - 1 = b - 1 := by omega
        simpa [b, h_eq] using h_unsigned_ge)
      (by
        simpa [b] using h_unsigned_lt)
  have h_formula : intToBytes v' s.len = ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF)) ++ natToBytes unsigned := by
    unfold intToBytes; simp [hv_neg, unsigned, b]; rw [h_raw_sz]
  have h_256_eq_2b : (256 : Nat) ^ s.len = (2 : Nat) ^ b := by
    have h256_eq : (256 : ℕ) = (2 : ℕ) ^ 8 := by native_decide
    calc
      (256 : Nat) ^ s.len = ((2 : Nat) ^ 8) ^ s.len := by rw [h256_eq]
      _ = (2 : Nat) ^ (8 * s.len) := by rw [Nat.pow_mul]
      _ = (2 : Nat) ^ (s.len * 8) := by simp [Nat.mul_comm]
      _ = (2 : Nat) ^ b := rfl
  have h_val : bytesToNat ((intToBytes v' s.len).extract 0 32) % (2 ^ b) = unsigned := by
    rw [h_self, h_formula, bytesToNat_append_general (ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF))) (natToBytes unsigned)]
    have h_mod : (bytesToNat (ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF))) * (2 ^ b) + unsigned) % (2 ^ b) = unsigned := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt h_unsigned_lt]
    calc
      (bytesToNat (ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF))) * (256 ^ (natToBytes unsigned).size) + bytesToNat (natToBytes unsigned)) % 2 ^ b
          = (bytesToNat (ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF))) * (256 ^ s.len) + unsigned) % 2 ^ b := by
            simp [h_raw_sz, bytesToNat_natToBytes unsigned]
      _ = (bytesToNat (ByteArray.mk (Array.mk (List.replicate (32 - s.len) 0xFF))) * (2 ^ b) + unsigned) % 2 ^ b := by rw [h_256_eq_2b]
      _ = unsigned := h_mod
  have h_masked : bytesToNat ((intToBytes v' s.len).extract 0 32) % 2 ^ (s.len * 8) = unsigned := by simpa [b] using h_val
  have h_half_ge : ¬ unsigned < 2 ^ (s.len * 8 - 1) := by
    have h_eq : 2 ^ (s.len * 8 - 1) = 2 ^ (b - 1) := by simp [b]
    have h_ge : 2 ^ (b - 1) ≤ unsigned := h_unsigned_ge
    omega
  have h_decode_val : -(Int.ofNat (2 ^ b - unsigned)) = v' := by
    have h_unsigned_add : unsigned + (-v').toNat = 2 ^ b := by
      have ha_nonneg : 0 ≤ (2 ^ b : Int) + v' := hun_nonneg
      have hb_nonneg : 0 ≤ -v' := by omega
      calc
        unsigned + (-v').toNat = ((2 ^ b : Int) + v').toNat + (-v').toNat := rfl
        _ = (((2 ^ b : Int) + v') + (-v')).toNat := by rw [Int.toNat_add ha_nonneg hb_nonneg]
        _ = (2 ^ b : Int).toNat := by simp
        _ = 2 ^ b := by simp [two_toNat_eq b]
    have h_sub : 2 ^ b - unsigned = (-v').toNat := by omega
    rw [h_sub]
    have h_nonneg : 0 ≤ -v' := by omega
    simp [Int.toNat_of_nonneg h_nonneg]
  have h_not_lt : ¬ bytesToNat ((intToBytes v' s.len).extract 0 32) % 2 ^ (s.len * 8) < 2 ^ (s.len * 8 - 1) := by
    simpa [h_masked] using h_half_ge
  rw [hsize32, h_masked]
  simp [h_half_ge]
  simpa [hsize32, b] using h_decode_val

theorem decode_intToBytes (s : ByteSize) (v' : Int)
    (hrange : -(2 ^ (s.len * 8 - 1) : Int) ≤ v' ∧ v' < (2 ^ (s.len * 8 - 1) : Int)) :
    decode (.int s) (intToBytes v' s.len) 0 = Except.ok (ABIValue.int v', (intToBytes v' s.len).size) := by
  have hbits256 : s.len * 8 ≤ 256 := by have := s.h.right; omega
  rcases hrange with ⟨hle, hlt⟩; by_cases hv_nonneg : v' ≥ 0
  · exact intToBytes_decode_nonneg s v' hv_nonneg hlt hbits256
  · exact intToBytes_decode_neg s v' hv_nonneg hle hbits256

theorem roundtrip_int (s : ByteSize) (v' : Int) (data : ByteArray)
    (henc : encode (.int s) (ABIValue.int v') = Except.ok data) : decode (.int s) data 0 = Except.ok (ABIValue.int v', data.size) := by
  unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc; simp at henc
  by_cases h1 : v' < -(2 ^ (s.len * 8 - 1) : Int)
  · simp [h1] at henc
  · by_cases h2 : v' ≥ (2 ^ (s.len * 8 - 1) : Int)
    · simp [h2] at henc
    · simp [h1, h2] at henc
      have hd : intToBytes v' s.len = data := henc
      rw [hd.symm]
      unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
      have hrange : -(2 ^ (s.len * 8 - 1) : Int) ≤ v' ∧ v' < (2 ^ (s.len * 8 - 1) : Int) := by omega
      have h_decode := decode_intToBytes s v' hrange
      unfold decode at h_decode; unfold foldABIType at h_decode; delta instABIVisitorDecoderEntry at h_decode; dsimp at h_decode
      simpa using h_decode

/-! ## ABIVisitor instance -/

instance : ABIVisitor RoundtripVisitor where
  onUint s := ⟨roundtrip_uint s⟩
  onInt s := ⟨λ v data henc => by
    cases v with
    | int v' => exact roundtrip_int s v' data henc
    | uint n =>
      have h_wrong : encode (.int s) (ABIValue.uint n) = Except.error .typeValueMismatch := by
        unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
      rw [h_wrong] at henc; simp at henc
    | bool b =>
      have h_wrong : encode (.int s) (ABIValue.bool b) = Except.error .typeValueMismatch := by
        unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
      rw [h_wrong] at henc; simp at henc
    | address a =>
      have h_wrong : encode (.int s) (ABIValue.address a) = Except.error .typeValueMismatch := by
        unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
      rw [h_wrong] at henc; simp at henc
    | bytes b =>
      have h_wrong : encode (.int s) (ABIValue.bytes b) = Except.error .typeValueMismatch := by
        unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
      rw [h_wrong] at henc; simp at henc
    | string s' =>
      have h_wrong : encode (.int s) (ABIValue.string s') = Except.error .typeValueMismatch := by
        unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
      rw [h_wrong] at henc; simp at henc
    | array arr =>
      have h_wrong : encode (.int s) (ABIValue.array arr) = Except.error .typeValueMismatch := by
        unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
      rw [h_wrong] at henc; simp at henc
    | tuple tup =>
      have h_wrong : encode (.int s) (ABIValue.tuple tup) = Except.error .typeValueMismatch := by
        unfold encode; unfold foldABIType; delta instABIVisitorEncoderEntry; dsimp
      rw [h_wrong] at henc; simp at henc⟩
  onBool := ⟨roundtrip_bool⟩
  onAddress := ⟨roundtrip_address⟩
  onFixedBytes s := ⟨roundtrip_fixedBytes s⟩
  onBytes := ⟨roundtrip_bytes⟩
  onString := ⟨roundtrip_string⟩
  onArray {e} ih := ⟨λ v data henc => by sorry⟩
  onFixedArray n {e} ih := ⟨λ v data henc => by sorry⟩
  onTuple {ts} all := ⟨λ v data henc => by sorry⟩

theorem roundtrip (t : ABIType) (v : ABIValue) (data : ByteArray)
    (henc : encode t v = Except.ok data) : decode t data 0 = Except.ok (v, data.size) :=
  (foldABIType RoundtripVisitor t).roundtrip v data henc
