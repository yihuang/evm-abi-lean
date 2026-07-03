/-
# ABI encode/decode roundtrip proofs

Static roundtrips are unconditional; dynamic-element containers (arrays, tuples) roundtrip under
a well-formedness bound (`enc.size < 2^256`) — see `roundtrip_{array,fixedArray,tuple}_wf`. The
composable `wfFactsWF` visitor lifts these to every well-formed type (nested structs included),
and `roundtrip_wf` / `roundtrip_args_wff` are the top-level results. No `sorry`.
-/

import EvmAbi.LemmaUtils
open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode
set_option autoImplicit false

/-- Discharge a wrong-`ABIValue`-constructor case: the `encode … = ok` hypothesis is false. -/
local macro "badVal" h:ident : tactic =>
  `(tactic| first
    | exact absurd $h (by simp)
    | exact absurd $h (by unfold encode foldABIType; simp)
    | exact absurd $h (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp))

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

theorem roundtrip_uint (s : ByteSize) (v : ABIValue) (data : ByteArray)
    (henc : encode (.uint s) v = Except.ok data) : decode (.uint s) data 0 = Except.ok (v, data.size) := by
  cases v with
  | uint v' =>
    unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    by_cases hm : v' < 2 ^ (s.len * 8)
    · simp [hm] at henc
      have hd : uint256ToBytes v' = data := henc
      rw [hd.symm]
      unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
      have hv256 : v' < 2 ^ 256 := by
        have hbits256 : s.len * 8 ≤ 256 := by have := s.h.right; omega
        have hp : 2 ^ (s.len * 8) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) hbits256; omega
      have hsize32 : (uint256ToBytes v').size = 32 := uint256ToBytes_size v' (natToBytes_size_bound v' hv256)
      have h_val : bytesToNat ((uint256ToBytes v').extract 0 32) = v' := by
        calc
          bytesToNat ((uint256ToBytes v').extract 0 32) = bytesToNat (uint256ToBytes v') := by rw [← hsize32, extract_self]
          _ = v' := bytesToNat_uint256ToBytes v'
      simp [hsize32, h_val, hm]
    · simp [hm] at henc
  | _ => badVal henc

theorem roundtrip_bool (v : ABIValue) (data : ByteArray)
    (henc : encode .bool v = Except.ok data) : decode .bool data 0 = Except.ok (v, data.size) := by
  cases v with
  | bool v' =>
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
  | _ => badVal henc

theorem roundtrip_address (v : ABIValue) (data : ByteArray)
    (henc : encode .address v = Except.ok data) : decode .address data 0 = Except.ok (v, data.size) := by
  cases v with
  | address v' =>
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
      simp [h_extract, h_sz]
  | _ => badVal henc

theorem roundtrip_fixedBytes (s : ByteSize) (v : ABIValue) (data : ByteArray)
    (henc : encode (.fixedBytes s) v = Except.ok data) : decode (.fixedBytes s) data 0 = Except.ok (v, data.size) := by
  cases v with
  | bytes v' =>
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
  | _ => badVal henc

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
  have h_nonneg_int : (v'.toNat : ℤ) = v' := by exact_mod_cast Int.toNat_of_nonneg hv_nonneg
  have h_val_int : (bytesToNat ((intToBytes v' s.len).extract 0 32) : ℤ) % ((2 : ℤ) ^ (s.len * 8)) = (v'.toNat : ℤ) := by
    exact_mod_cast h_val
  simp [hsize32, h_val, h_val_int, hv_lt_nat, h_nonneg_int]

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
    have h_ge : 2 ^ (b - 1) ≤ unsigned := h_unsigned_ge; omega
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

/-! ## Offset-generalized roundtrip -/

lemma not_gt_of_extract_eq (data : ByteArray) (off n : Nat) (h : (data.extract off (off + n)).size = n) (hn : n ≠ 0) : off + n ≤ data.size := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  by_contra! H
  rw [ByteArray.size_extract] at h
  have hmin : min (off + n) data.size = data.size := Nat.min_eq_right (by omega)
  rw [hmin] at h
  -- h: data.size - off = n
  have h_sub_lt : data.size - off < n := by
    by_cases h_off_le : off ≤ data.size
    · calc
        data.size - off < (off + n) - off := Nat.sub_lt_sub_right h_off_le (by omega)
        _ = n := by omega
    · omega
  rw [h] at h_sub_lt; omega

/-- roundtrip_uint generalized to any offset. -/
theorem roundtrip_offset_uint (s : ByteSize) (v' : Nat) (enc data : ByteArray) (off : Nat)
    (henc : encode (.uint s) (.uint v') = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.uint s) data off = Except.ok (.uint v', off + enc.size) := by
  unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
  by_cases hm : v' < 2 ^ (s.len * 8)
  · simp [hm] at henc
    have h_enc_eq : uint256ToBytes v' = enc := henc
    subst h_enc_eq
    have hsize32 : (uint256ToBytes v').size = 32 := by
      have hv256 : v' < 2 ^ 256 := by
        have hbits256 : s.len * 8 ≤ 256 := by have := s.h.right; omega
        have hp : 2 ^ (s.len * 8) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) hbits256; omega
      exact uint256ToBytes_size v' (natToBytes_size_bound v' hv256)
    have hdata' : data.extract off (off + 32) = uint256ToBytes v' := by
      simpa [hsize32] using hdata
    unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
    have h_not_too_short : off + 32 ≤ data.size :=
      not_gt_of_extract_eq data off 32 (by rw [hdata', hsize32]) (by omega)
    by_cases hshort : off + 32 > data.size
    · exfalso; omega
    · simp [hshort, hdata']
      have h_val : bytesToNat (uint256ToBytes v') = v' := bytesToNat_uint256ToBytes v'
      have h_not_ge : ¬ v' ≥ 2 ^ (s.len * 8) := by omega
      simp [h_val, h_not_ge, hsize32]
  · simp [hm] at henc

/-- roundtrip_address generalized to any offset. -/
theorem roundtrip_offset_address (v' : ByteArray) (enc data : ByteArray) (off : Nat)
    (henc : encode .address (.address v') = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode .address data off = Except.ok (.address v', off + enc.size) := by
  unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
  by_cases hsize : v'.size ≠ 20
  · simp [hsize] at henc
  · have hsize20 : v'.size = 20 := by omega
    simp [hsize20] at henc
    have h_enc_eq : padLeft v' 32 = enc := henc
    subst h_enc_eq
    have hsize32 : (padLeft v' 32).size = 32 := by
      unfold padLeft; simp [hsize20, zeros_size]
    have hdata' : data.extract off (off + 32) = padLeft v' 32 := by
      simpa [hsize32] using hdata
    have h_not_too_short : off + 32 ≤ data.size :=
      not_gt_of_extract_eq data off 32 (by rw [hdata', hsize32]) (by omega)
    by_cases hshort : off + 32 > data.size
    · exfalso; omega
    · have h_not_gt : ¬ off + 32 > data.size := by omega
      unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
      rw [if_neg h_not_gt]
      have h_extract_v' : data.extract (off + 12) (off + 32) = v' := by
        calc
          data.extract (off + 12) (off + 32) = data.extract (off + 12) (min (off + 32) (off + 32)) := by
            simp
          _ = (data.extract off (off + 32)).extract 12 32 := by rw [ByteArray.extract_extract]
          _ = (padLeft v' 32).extract 12 32 := by rw [hdata']
          _ = v' := padLeft_extract_address v' hsize20
      simp [h_extract_v', hsize32]

/-- roundtrip_bool generalized to any offset. -/
theorem roundtrip_offset_bool (v' : Bool) (enc data : ByteArray) (off : Nat)
    (henc : encode .bool (.bool v') = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode .bool data off = Except.ok (.bool v', off + enc.size) := by
  unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
  simp at henc
  have h_enc_eq : uint256ToBytes (if v' then 1 else 0) = enc := henc
  subst h_enc_eq
  have hsize32 : (uint256ToBytes (if v' then 1 else 0)).size = 32 := by
    have hbits : (if v' then 1 else 0) < 2 ^ 256 := by split <;> omega
    exact uint256ToBytes_size (if v' then 1 else 0) (natToBytes_size_bound (if v' then 1 else 0) hbits)
  have hdata' : data.extract off (off + 32) = uint256ToBytes (if v' then 1 else 0) := by
    simpa [hsize32] using hdata
  have h_not_too_short : off + 32 ≤ data.size :=
    not_gt_of_extract_eq data off 32 (by rw [hdata', hsize32]) (by omega)
  by_cases hshort : off + 32 > data.size
  · exfalso; omega
  · have h_not_gt : ¬ off + 32 > data.size := by omega
    rw [hsize32]
    unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
    simp [h_not_gt, hdata']
    have h_val : bytesToNat (uint256ToBytes (if v' then 1 else 0)) = (if v' then 1 else 0) :=
      bytesToNat_uint256ToBytes (if v' then 1 else 0)
    simp [h_val]; cases v' <;> simp
/-- roundtrip_fixedBytes generalized to any offset. -/
theorem roundtrip_offset_fixedBytes (s : ByteSize) (v' : ByteArray) (enc data : ByteArray) (off : Nat)
    (henc : encode (.fixedBytes s) (.bytes v') = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.fixedBytes s) data off = Except.ok (.bytes v', off + enc.size) := by
  unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
  by_cases hsz : v'.size = s.len
  · simp [hsz] at henc
    have h_enc_eq : padRight v' 32 = enc := henc; subst h_enc_eq
    have hsize32 : (padRight v' 32).size = 32 := padRight_size_32 v' (by rw [hsz]; exact s.h.right)
    rw [hsize32]
    have hdata' : data.extract off (off + 32) = padRight v' 32 := by
      simpa [hsize32] using hdata
    have h_not_too_short : off + 32 ≤ data.size :=
      not_gt_of_extract_eq data off 32 (by rw [hdata', hsize32]) (by omega)
    by_cases hshort : off + 32 > data.size
    · exfalso; omega
    · have h_not_gt : ¬ off + 32 > data.size := by omega
      unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
      rw [if_neg h_not_gt]
      have h_extract_v' : data.extract off (off + s.len) = v' := by
        calc
          data.extract off (off + s.len) = data.extract off (min (off + s.len) (off + 32)) := by
            simp [show min (off + s.len) (off + 32) = off + s.len from by
              have hs32 : s.len ≤ 32 := s.h.right; omega]
          _ = (data.extract off (off + 32)).extract 0 s.len := by
            rw [ByteArray.extract_extract, add_zero]
          _ = (padRight v' 32).extract 0 s.len := by rw [hdata']
          _ = v' := padRight_extract_eq v' s.len hsz
      simp [h_extract_v']
  · simp [hsz] at henc

/-- roundtrip_int generalized to any offset. -/
theorem roundtrip_offset_int (s : ByteSize) (v' : Int) (enc data : ByteArray) (off : Nat)
    (henc : encode (.int s) (.int v') = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.int s) data off = Except.ok (.int v', off + enc.size) := by
  unfold encode at henc; unfold foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc; simp at henc
  by_cases h1 : v' < -(2 ^ (s.len * 8 - 1) : Int); · simp [h1] at henc
  · by_cases h2 : v' ≥ (2 ^ (s.len * 8 - 1) : Int); · simp [h2] at henc
    · simp [h1, h2] at henc
      have h_enc_eq : intToBytes v' s.len = enc := henc; subst h_enc_eq
      have hsize32 : (intToBytes v' s.len).size = 32 := by
        have hbits256 : s.len * 8 ≤ 256 := by have := s.h.right; omega
        by_cases hv_nonneg : v' ≥ 0
        · have hv_lt_nat : v'.toNat < 2 ^ (s.len * 8 - 1) := by
            apply Int.ofNat_lt.mp; calc
              (v'.toNat : ℤ) = v' := by exact_mod_cast Int.toNat_of_nonneg hv_nonneg
              _ < (2 ^ (s.len * 8 - 1) : ℤ) := by omega
          have hv_lt_256 : v'.toNat < 2 ^ 256 := by
            have h_pow : 2 ^ (s.len * 8 - 1) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by omega); omega
          calc (intToBytes v' s.len).size = (uint256ToBytes v'.toNat).size := by simp [intToBytes, uint256ToBytes, hv_nonneg]
          _ = 32 := uint256ToBytes_size v'.toNat (natToBytes_size_bound v'.toNat hv_lt_256)
        · have h_bounded : ((2 : Int) ^ (s.len * 8) + v').toNat < 2 ^ 256 := by
            have h_range : -(2 ^ (s.len * 8 - 1) : Int) ≤ v' ∧ v' < (2 ^ (s.len * 8 - 1) : Int) := by
              exact ⟨by omega, by omega⟩
            have h_add_lt : (2 : ℤ) ^ (s.len * 8) + v' < (2 : ℤ) ^ (s.len * 8) := by omega
            have h_add_nonneg : 0 ≤ (2 : ℤ) ^ (s.len * 8) + v' := by
              have h_lb : -(2 ^ (s.len * 8 - 1) : Int) ≤ v' := h_range.left
              have hbpos : 0 < s.len * 8 := by have : 0 < s.len := s.h.left; omega
              have h_diff : (2 : ℤ) ^ (s.len * 8) - (2 : ℤ) ^ (s.len * 8 - 1) = (2 : ℤ) ^ (s.len * 8 - 1) :=
                two_pow_succ_sub (s.len * 8) hbpos
              calc 0 ≤ (2 : ℤ) ^ (s.len * 8 - 1) := by positivity
                _ = (2 : ℤ) ^ (s.len * 8) - (2 : ℤ) ^ (s.len * 8 - 1) := by rw [h_diff]
                _ ≤ (2 : ℤ) ^ (s.len * 8) + v' := by omega
            have h_toNat_lt : ((2 : ℤ) ^ (s.len * 8) + v').toNat < ((2 : ℤ) ^ (s.len * 8)).toNat :=
              (Int.toNat_lt_toNat (by positivity : 0 < (2 : ℤ) ^ (s.len * 8))).mpr h_add_lt
            have h_pow : 2 ^ (s.len * 8) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by omega)
            have h_toNat_eq : ((2 : ℤ) ^ (s.len * 8)).toNat = 2 ^ (s.len * 8) := by
              have h_nonneg : 0 ≤ (2 : ℤ) ^ (s.len * 8) := by positivity
              have h := Int.toNat_of_nonneg h_nonneg
              apply (Nat.cast_inj (R := ℤ)).mp; simp
            rw [h_toNat_eq] at h_toNat_lt
            exact lt_of_lt_of_le h_toNat_lt h_pow
          exact intToBytes_neg_size v' s.len (by omega) h_bounded
      rw [hsize32]
      have hdata' : data.extract off (off + 32) = intToBytes v' s.len := by
        simpa [hsize32] using hdata
      have h_not_too_short : off + 32 ≤ data.size :=
        not_gt_of_extract_eq data off 32 (by rw [hdata', hsize32]) (by omega)
      by_cases hshort : off + 32 > data.size
      · exfalso; omega
      · have h_not_gt : ¬ off + 32 > data.size := by omega
        unfold decode; unfold foldABIType; delta instABIVisitorDecoderEntry; dsimp
        rw [if_neg h_not_gt, hdata']
        have h_range : -(2 ^ (s.len * 8 - 1) : Int) ≤ v' ∧ v' < (2 ^ (s.len * 8 - 1) : Int) := by
          exact ⟨by omega, by omega⟩
        have h_at_0 : decode (.int s) (intToBytes v' s.len) 0 = Except.ok (ABIValue.int v', 32) := by
          have h := decode_intToBytes s v' h_range
          simpa [hsize32] using h
        unfold decode at h_at_0; unfold foldABIType at h_at_0; delta instABIVisitorDecoderEntry at h_at_0; dsimp at h_at_0
        have h_not_short : ¬ (intToBytes v' s.len).size < 32 := by rw [hsize32]; omega
        rw [if_neg h_not_short] at h_at_0
        have h_ext : (intToBytes v' s.len).extract 0 32 = intToBytes v' s.len := by rw [← hsize32, extract_self]
        rw [h_ext] at h_at_0
        by_cases h_cond : bytesToNat (intToBytes v' s.len) % 2 ^ (s.len * 8) < 2 ^ (s.len * 8 - 1)
        · rw [if_pos h_cond] at h_at_0
          rw [if_pos h_cond]
          injection h_at_0 with h_pair
          injection h_pair with h_val h_nat
          simp [h_val]
        · rw [if_neg h_cond] at h_at_0
          rw [if_neg h_cond]
          injection h_at_0 with h_pair
          injection h_pair with h_val h_nat
          simp [h_val]
/-! ## Offset-general dynamic bytes/string cores -/

/-- `decodeDynamicBytes` recovers the value at an arbitrary offset, provided the
    buffer contains the encoding as the slice `[off, off + enc.size)`. -/
private lemma decodeDynamicBytes_roundtrip_off (v' : ByteArray) (hv256 : v'.size < 2 ^ 256)
    (enc data : ByteArray) (off : Nat)
    (henc : enc = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size))
    (hdata : data.extract off (off + enc.size) = enc) :
    decodeDynamicBytes data off = Except.ok (.bytes v', off + enc.size) := by
  subst henc
  rcases dynamicRoundtrip_preamble v' hv256 with ⟨ha_sz, _h_pad_sz, h_roundUp_ge, h_size, _h_len, h_extract_val⟩
  set A := uint256ToBytes v'.size with hA
  set P := padRight v' (roundUp32 v'.size) with hP
  have hn0 : (A ++ P).size ≠ 0 := by rw [h_size]; omega
  have hbound_all : off + (A ++ P).size ≤ data.size :=
    not_gt_of_extract_eq data off (A ++ P).size (by rw [hdata]) hn0
  have h_bound32 : ¬ (off + 32 > data.size) := by rw [h_size] at hbound_all; omega
  have h_bound2 : ¬ (off + 32 + v'.size > data.size) := by rw [h_size] at hbound_all; omega
  have hmin1 : min (off + 32) (off + (A ++ P).size) = off + 32 := by rw [h_size]; omega
  have hmin2 : min (off + (32 + v'.size)) (off + (A ++ P).size) = off + 32 + v'.size := by rw [h_size]; omega
  have e1 : (data.extract off (off + (A ++ P).size)).extract 0 32 = data.extract off (off + 32) := by
    rw [ByteArray.extract_extract, Nat.add_zero, hmin1]
  have h_ext32 : data.extract off (off + 32) = A := by
    rw [← e1, hdata, ← ha_sz]; exact extract_first_n _ _
  have hlen : bytesToNat (data.extract off (off + 32)) = v'.size := by
    rw [h_ext32]; exact bytesToNat_uint256ToBytes v'.size
  have e2 : (data.extract off (off + (A ++ P).size)).extract 32 (32 + v'.size)
      = data.extract (off + 32) (off + 32 + v'.size) := by
    rw [ByteArray.extract_extract, hmin2]
  have h_ext_val : data.extract (off + 32) (off + 32 + v'.size) = v' := by
    rw [← e2, hdata]; exact h_extract_val
  unfold decodeDynamicBytes
  simp [h_bound32, hlen, h_bound2, h_ext_val, h_size]

/-- `decodeDynamicString` recovers the value at an arbitrary offset. -/
private lemma decodeDynamicString_roundtrip_off (v' : String) (hv256 : v'.toUTF8.size < 2 ^ 256)
    (enc data : ByteArray) (off : Nat)
    (henc : enc = uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size))
    (hdata : data.extract off (off + enc.size) = enc) :
    decodeDynamicString data off = Except.ok (.string v', off + enc.size) := by
  rw [decodeDynamicString, decodeDynamicBytes_roundtrip_off v'.toUTF8 hv256 enc data off henc hdata]
  simp [Except.map]; have h : v'.toByteArray = v'.toUTF8 := rfl; rw [h, fromUTF8!_toUTF8 v']

/-! ## Offset-general atomic full wrappers (handle any `ABIValue`) -/

/-- Uniform "wrong constructor ⇒ encode errors" contradiction for atomic encoders. -/
private theorem roundtrip_off_uint (s : ByteSize) (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode (.uint s) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.uint s) data off = Except.ok (v, off + enc.size) := by
  rcases v with v'|i|b|ba|str|addr|arr|tup
  · exact roundtrip_offset_uint s v' enc data off henc hdata
  all_goals badVal henc

private theorem roundtrip_off_int (s : ByteSize) (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode (.int s) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.int s) data off = Except.ok (v, off + enc.size) := by
  rcases v with v'|i|b|ba|str|addr|arr|tup
  · badVal henc
  · exact roundtrip_offset_int s i enc data off henc hdata
  all_goals badVal henc

private theorem roundtrip_off_bool (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode .bool v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode .bool data off = Except.ok (v, off + enc.size) := by
  rcases v with v'|i|b|ba|str|addr|arr|tup
  · badVal henc
  · badVal henc
  · exact roundtrip_offset_bool b enc data off henc hdata
  all_goals badVal henc

private theorem roundtrip_off_address (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode .address v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode .address data off = Except.ok (v, off + enc.size) := by
  cases v
  case address addr => exact roundtrip_offset_address addr enc data off henc hdata
  all_goals badVal henc

private theorem roundtrip_off_fixedBytes (s : ByteSize) (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode (.fixedBytes s) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.fixedBytes s) data off = Except.ok (v, off + enc.size) := by
  cases v
  case bytes ba => exact roundtrip_offset_fixedBytes s ba enc data off henc hdata
  all_goals badVal henc

theorem roundtrip_off_bytes (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode .bytes v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode .bytes data off = Except.ok (v, off + enc.size) := by
  have h256_eq : (2 : ℕ) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by native_decide
  cases v
  case bytes v' =>
    by_cases hv256 : v'.size < 2 ^ 256
    · have hval : encode .bytes (ABIValue.bytes v') = Except.ok (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)) := by
        unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simpa [h256_eq, hv256]
      have hd : enc = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size) := by
        injection hval.symm.trans henc; symm; assumption
      unfold decode foldABIType; delta instABIVisitorDecoderEntry; dsimp
      exact decodeDynamicBytes_roundtrip_off v' hv256 enc data off hd hdata
    · exact absurd henc (by
        unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp
        have h_ge : ¬ v'.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
          rw [← h256_eq]; exact hv256
        simp [h_ge])
  all_goals badVal henc

theorem roundtrip_off_string (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode .string v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode .string data off = Except.ok (v, off + enc.size) := by
  have h256_eq : (2 : ℕ) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by native_decide
  cases v
  case string v' =>
    by_cases huv256 : v'.toUTF8.size < 2 ^ 256
    · have hval : encode .string (ABIValue.string v') = Except.ok (uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size)) := by
        unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simpa [h256_eq, huv256]
      have hd : enc = uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size) := by
        injection hval.symm.trans henc; symm; assumption
      unfold decode foldABIType; delta instABIVisitorDecoderEntry; dsimp
      exact decodeDynamicString_roundtrip_off v' huv256 enc data off hd hdata
    · exact absurd henc (by
        unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp
        have h_ge : ¬ v'.toUTF8.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
          rw [← h256_eq]; exact huv256
        have h_ge' : ¬ v'.utf8ByteSize < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
          simpa using h_ge
        simp [h_ge'])
  all_goals badVal henc

/-! ## Array/tuple packing helpers -/

/-- The encoder's dynamic flag agrees with `isDynamic`. -/
theorem tuple_any_isDynamic (ts : List ABIType) : (ts.map isDynamic).any id = isDynamic (.tuple ts) := by
  induction ts with
  | nil => simp [isDynamic]
  | cons t ts ih => simp only [List.map_cons, List.any_cons, id_eq, ih]; simp [isDynamic]

theorem enc_fst_eq_isDynamic (e : ABIType) : (foldABIType EncoderEntry e).1 = isDynamic e := by
  match e with
  | .uint s => simp only [foldABIType]; delta instABIVisitorEncoderEntry; dsimp; simp [isDynamic]
  | .int s => simp only [foldABIType]; delta instABIVisitorEncoderEntry; dsimp; simp [isDynamic]
  | .bool => simp only [foldABIType]; delta instABIVisitorEncoderEntry; dsimp; simp [isDynamic]
  | .address => simp only [foldABIType]; delta instABIVisitorEncoderEntry; dsimp; simp [isDynamic]
  | .bytes => simp only [foldABIType]; delta instABIVisitorEncoderEntry; dsimp; simp [isDynamic]
  | .fixedBytes s => simp only [foldABIType]; delta instABIVisitorEncoderEntry; dsimp; simp [isDynamic]
  | .string => simp only [foldABIType]; delta instABIVisitorEncoderEntry; dsimp; simp [isDynamic]
  | .array e' =>
    simp only [foldABIType]; delta instABIVisitorEncoderEntry
    rcases foldABIType EncoderEntry e' with ⟨d, f⟩
    dsimp; simp [isDynamic]
  | .fixedArray n e' =>
    have ih := enc_fst_eq_isDynamic e'
    simp only [foldABIType]; delta instABIVisitorEncoderEntry
    rcases hfe : foldABIType EncoderEntry e' with ⟨d, f⟩
    rw [hfe] at ih; dsimp
    rw [show isDynamic (ABIType.fixedArray n e') = isDynamic e' from by simp [isDynamic]]
    simpa using ih
  | .tuple ts =>
    simp only [foldABIType]; delta instABIVisitorEncoderEntry; dsimp
    exact tuple_any_isDynamic ts
termination_by sizeOf e
decreasing_by simp

/-- Left fold of `++` with a nonempty seed factors the seed out to the front. -/
theorem ba_foldl_init (init : ByteArray) (xs : List ByteArray) :
    xs.foldl (·++·) init = init ++ xs.foldl (·++·) ByteArray.empty := by
  induction xs generalizing init with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, ByteArray.empty_append]
    rw [ih (init ++ y), ih y, ByteArray.append_assoc]

theorem ba_foldl_cons (x : ByteArray) (xs : List ByteArray) :
    (x :: xs).foldl (·++·) ByteArray.empty = x ++ xs.foldl (·++·) ByteArray.empty := by
  simp only [List.foldl_cons, ByteArray.empty_append]; exact ba_foldl_init x xs

/-- Invert a successful `encodeListElems` on a cons. -/
theorem encodeListElems_cons_ok (e : ABIType) (v : ABIValue) (rest : List ABIValue) (encd : List ByteArray)
    (henc : encodeListElems (encode e) (v :: rest) = Except.ok encd) :
    ∃ ev er, encode e v = .ok ev ∧ encodeListElems (encode e) rest = .ok er ∧ encd = ev :: er := by
  rw [encodeListElems] at henc
  cases hev : encode e v with
  | error x => rw [hev] at henc; exact absurd (show Except.error x = Except.ok encd from henc) (by simp)
  | ok ev =>
    cases her : encodeListElems (encode e) rest with
    | error x => rw [hev, her] at henc; exact absurd (show Except.error x = Except.ok encd from henc) (by simp)
    | ok er =>
      rw [hev, her] at henc
      exact ⟨ev, er, rfl, rfl, (Except.ok.inj (show Except.ok (ev :: er) = Except.ok encd from henc)).symm⟩

/-- Decoding the contiguous concatenation of statically-packed element encodings recovers the values. -/
lemma decodeStaticElemsGo_concat (e : ABIType)
    (data : ByteArray)
    (dec : ByteArray → Nat → Except Error (ABIValue × Nat))
    (hdec : ∀ (v : ABIValue) (ev : ByteArray) (off : Nat),
      encode e v = Except.ok ev → data.extract off (off + ev.size) = ev →
      dec data off = Except.ok (v, off + ev.size)) :
    ∀ (vals : List ABIValue) (encd : List ByteArray) (i n pos : Nat) (acc : List ABIValue),
      n = i + vals.length →
      encodeListElems (encode e) vals = Except.ok encd →
      data.extract pos (pos + (encd.foldl (·++·) ByteArray.empty).size) = encd.foldl (·++·) ByteArray.empty →
      decodeStaticElemsGo dec n i pos data acc
        = Except.ok (acc.reverse ++ vals, pos + (encd.foldl (·++·) ByteArray.empty).size) := by
  intro vals
  induction vals with
  | nil =>
    intro encd i n pos acc hn henc hslice
    simp only [encodeListElems, Except.ok.injEq] at henc
    subst henc
    simp only [List.foldl_nil, ByteArray.size_empty, Nat.add_zero, List.append_nil]
    unfold decodeStaticElemsGo
    have hni : ¬ i < n := by simp only [List.length_nil, Nat.add_zero] at hn; omega
    simp [hni]
  | cons v rest ih =>
    intro encd i n pos acc hn henc hslice
    obtain ⟨ev, er, hev, her, rfl⟩ := encodeListElems_cons_ok e v rest encd henc
    rw [ba_foldl_cons] at hslice ⊢
    have hsz : (ev ++ er.foldl (·++·) ByteArray.empty).size = ev.size + (er.foldl (·++·) ByteArray.empty).size := ByteArray.size_append
    have hm1 : min (pos + ev.size) (pos + (ev ++ er.foldl (·++·) ByteArray.empty).size) = pos + ev.size := by rw [hsz]; omega
    have hm2 : min (pos + (ev.size + (er.foldl (·++·) ByteArray.empty).size)) (pos + (ev ++ er.foldl (·++·) ByteArray.empty).size) = pos + ev.size + (er.foldl (·++·) ByteArray.empty).size := by rw [hsz]; omega
    have hslice_ev : data.extract pos (pos + ev.size) = ev := by
      have e0 : (data.extract pos (pos + (ev ++ er.foldl (·++·) ByteArray.empty).size)).extract 0 ev.size = data.extract pos (pos + ev.size) := by
        rw [ByteArray.extract_extract, Nat.add_zero, hm1]
      rw [← e0, hslice, ByteArray.extract_append_eq_left rfl]
    have hslice_rest : data.extract (pos + ev.size) (pos + ev.size + (er.foldl (·++·) ByteArray.empty).size) = er.foldl (·++·) ByteArray.empty := by
      have e0 : (data.extract pos (pos + (ev ++ er.foldl (·++·) ByteArray.empty).size)).extract ev.size (ev.size + (er.foldl (·++·) ByteArray.empty).size) = data.extract (pos + ev.size) (pos + ev.size + (er.foldl (·++·) ByteArray.empty).size) := by
        rw [ByteArray.extract_extract, hm2]
      rw [← e0, hslice]; exact ByteArray.extract_append_eq_right rfl rfl
    unfold decodeStaticElemsGo
    have hni : i < n := by simp only [List.length_cons] at hn; omega
    rw [dif_pos hni, hdec v ev pos hev hslice_ev]
    show decodeStaticElemsGo dec n (i + 1) (pos + ev.size) data (v :: acc) = _
    rw [ih er (i + 1) n (pos + ev.size) (v :: acc) (by simp only [List.length_cons] at hn ⊢; omega) her hslice_rest]
    have h1 : (v :: acc).reverse ++ rest = acc.reverse ++ v :: rest := by simp
    have h2 : pos + ev.size + (er.foldl (·++·) ByteArray.empty).size = pos + (ev ++ er.foldl (·++·) ByteArray.empty).size := by rw [hsz]; omega
    rw [h1, h2]

/-! ## Static encoding size = headSize -/

theorem concat_size_uniform (encd : List ByteArray) (k : Nat) (h : ∀ b ∈ encd, b.size = k) :
    (encd.foldl (·++·) ByteArray.empty).size = encd.length * k := by
  induction encd with
  | nil => simp
  | cons x xs ih =>
    rw [ba_foldl_cons, ByteArray.size_append, h x (by simp),
        ih (fun b hb => h b (by simp [hb]))]
    simp [List.length_cons, Nat.succ_mul]; ring

theorem encodeListElems_length (e : ABIType) (vals : List ABIValue) (encd : List ByteArray)
    (h : encodeListElems (encode e) vals = Except.ok encd) : encd.length = vals.length := by
  induction vals generalizing encd with
  | nil => simp only [encodeListElems, Except.ok.injEq] at h; subst h; simp
  | cons v rest ih =>
    obtain ⟨ev, er, hev, her, rfl⟩ := encodeListElems_cons_ok e v rest encd h
    simp [ih er her]

theorem encodeListElems_mem (e : ABIType) (vals : List ABIValue) (encd : List ByteArray)
    (h : encodeListElems (encode e) vals = Except.ok encd) (b : ByteArray) (hb : b ∈ encd) :
    ∃ v, encode e v = Except.ok b := by
  induction vals generalizing encd with
  | nil => simp only [encodeListElems, Except.ok.injEq] at h; subst h; simp at hb
  | cons v rest ih =>
    obtain ⟨ev, er, hev, her, rfl⟩ := encodeListElems_cons_ok e v rest encd h
    rcases List.mem_cons.mp hb with h1 | h2
    · exact ⟨v, by rw [h1]; exact hev⟩
    · exact ih er her h2

theorem intToBytes_size32 (s : ByteSize) (v' : Int)
    (hrange : -(2 ^ (s.len * 8 - 1) : Int) ≤ v' ∧ v' < (2 ^ (s.len * 8 - 1) : Int)) :
    (intToBytes v' s.len).size = 32 := by
  have hbits256 : s.len * 8 ≤ 256 := by have := s.h.right; omega
  by_cases hv_nonneg : v' ≥ 0
  · have hv_lt_nat : v'.toNat < 2 ^ (s.len * 8 - 1) := by
      apply Int.ofNat_lt.mp; calc
        (v'.toNat : ℤ) = v' := by exact_mod_cast Int.toNat_of_nonneg hv_nonneg
        _ < (2 ^ (s.len * 8 - 1) : ℤ) := hrange.right
    have hv_lt_256 : v'.toNat < 2 ^ 256 := by
      have h_pow : 2 ^ (s.len * 8 - 1) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by omega); omega
    calc (intToBytes v' s.len).size = (uint256ToBytes v'.toNat).size := by simp [intToBytes, uint256ToBytes, hv_nonneg]
    _ = 32 := uint256ToBytes_size v'.toNat (natToBytes_size_bound v'.toNat hv_lt_256)
  · have h_bounded : ((2 : Int) ^ (s.len * 8) + v').toNat < 2 ^ 256 := by
      have h_add_lt : (2 : ℤ) ^ (s.len * 8) + v' < (2 : ℤ) ^ (s.len * 8) := by omega
      have hbpos : 0 < s.len * 8 := by have : 0 < s.len := s.h.left; omega
      have h_diff : (2 : ℤ) ^ (s.len * 8) - (2 : ℤ) ^ (s.len * 8 - 1) = (2 : ℤ) ^ (s.len * 8 - 1) :=
        two_pow_succ_sub (s.len * 8) hbpos
      have h_add_nonneg : 0 ≤ (2 : ℤ) ^ (s.len * 8) + v' := by
        have h_lb : -(2 ^ (s.len * 8 - 1) : Int) ≤ v' := hrange.left
        calc 0 ≤ (2 : ℤ) ^ (s.len * 8 - 1) := by positivity
          _ = (2 : ℤ) ^ (s.len * 8) - (2 : ℤ) ^ (s.len * 8 - 1) := by rw [h_diff]
          _ ≤ (2 : ℤ) ^ (s.len * 8) + v' := by omega
      have h_toNat_lt : ((2 : ℤ) ^ (s.len * 8) + v').toNat < ((2 : ℤ) ^ (s.len * 8)).toNat :=
        (Int.toNat_lt_toNat (by positivity : 0 < (2 : ℤ) ^ (s.len * 8))).mpr h_add_lt
      have h_pow : 2 ^ (s.len * 8) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) (by omega)
      have h_toNat_eq : ((2 : ℤ) ^ (s.len * 8)).toNat = 2 ^ (s.len * 8) := by
        have h := Int.toNat_of_nonneg (by positivity : 0 ≤ (2 : ℤ) ^ (s.len * 8))
        apply (Nat.cast_inj (R := ℤ)).mp; simp
      rw [h_toNat_eq] at h_toNat_lt; exact lt_of_lt_of_le h_toNat_lt h_pow
    exact intToBytes_neg_size v' s.len (by omega) h_bounded

theorem size_eq_uint (s : ByteSize) (v : ABIValue) (ev : ByteArray) (henc : encode (.uint s) v = Except.ok ev) : ev.size = headSize (.uint s) := by
  cases v with
  | uint v' =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    split at henc
    · rename_i hb
      have hev := Except.ok.inj henc
      have hv256 : v' < 2 ^ 256 := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by have := s.h.right; omega))
      simp only [headSize, isDynamic]; rw [← hev]; exact uint256ToBytes_size v' (natToBytes_size_bound v' hv256)
    · exact absurd (show Except.error _ = Except.ok ev from henc) (by simp)
  | _ => badVal henc

theorem size_eq_int (s : ByteSize) (v : ABIValue) (ev : ByteArray) (henc : encode (.int s) v = Except.ok ev) : ev.size = headSize (.int s) := by
  cases v with
  | int v' =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    simp only [Bool.or_eq_true, decide_eq_true_eq] at henc
    split at henc
    · exact absurd (show Except.error _ = Except.ok ev from henc) (by simp)
    · rename_i hcond
      have hev := Except.ok.inj henc
      push Not at hcond
      simp only [headSize, isDynamic]; rw [← hev]; exact intToBytes_size32 s v' ⟨by omega, by omega⟩
  | _ => badVal henc

theorem size_eq_bool (v : ABIValue) (ev : ByteArray) (henc : encode .bool v = Except.ok ev) : ev.size = headSize .bool := by
  cases v with
  | bool v' =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    have hev := Except.ok.inj henc
    have hbits : (if v' then 1 else 0) < 2 ^ 256 := by split <;> omega
    simp only [headSize, isDynamic]; rw [← hev]; exact uint256ToBytes_size _ (natToBytes_size_bound _ hbits)
  | _ => badVal henc

theorem size_eq_address (v : ABIValue) (ev : ByteArray) (henc : encode .address v = Except.ok ev) : ev.size = headSize .address := by
  cases v with
  | address v' =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    split at henc
    · rename_i h20
      have hev := Except.ok.inj henc
      simp only [headSize, isDynamic]; rw [← hev]; unfold padLeft; simp [h20, zeros_size]
    · exact absurd (show Except.error _ = Except.ok ev from henc) (by simp)
  | _ => badVal henc

theorem size_eq_fixedBytes (s : ByteSize) (v : ABIValue) (ev : ByteArray) (henc : encode (.fixedBytes s) v = Except.ok ev) : ev.size = headSize (.fixedBytes s) := by
  cases v with
  | bytes v' =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    split at henc
    · rename_i hsz
      have hev := Except.ok.inj henc
      simp only [headSize, isDynamic]; rw [← hev]; exact padRight_size_32 v' (by rw [hsz]; exact s.h.right)
    · exact absurd (show Except.error _ = Except.ok ev from henc) (by simp)
  | _ => badVal henc

/-! ## Tuple encode (`go`) / `tuplePack` reduction helpers -/

theorem go_nil_nil : instABIVisitorEncoderEntry.go [] All.nil [] = Except.ok [] := rfl

theorem go_cons {t : ABIType} {ts' : List ABIType} (dyn : Bool) (enc : ABIValue → Except Error ByteArray)
    (rest : All EncoderEntry ts') (v : ABIValue) (vs' : List ABIValue) :
    instABIVisitorEncoderEntry.go (t :: ts') (All.cons (dyn, enc) rest) (v :: vs')
      = (enc v >>= fun bytes => instABIVisitorEncoderEntry.go ts' rest vs' >>= fun tail => Except.ok ((dyn, bytes) :: tail)) := rfl

theorem go_cons_ok {t : ABIType} {ts' : List ABIType} (dyn : Bool) (enc : ABIValue → Except Error ByteArray)
    (rest : All EncoderEntry ts') (vs : List ABIValue) (encd : List (Bool × ByteArray))
    (h : instABIVisitorEncoderEntry.go (t :: ts') (All.cons (dyn, enc) rest) vs = Except.ok encd) :
    ∃ v vs' b tail, vs = v :: vs' ∧ enc v = Except.ok b ∧
      instABIVisitorEncoderEntry.go ts' rest vs' = Except.ok tail ∧ encd = (dyn, b) :: tail := by
  cases vs with
  | nil => exact absurd (show Except.error Error.typeValueMismatch = Except.ok encd from h) (by simp)
  | cons v vs' =>
    rw [go_cons] at h
    cases hb : enc v with
    | error x => rw [hb] at h; exact absurd (show Except.error x = Except.ok encd from h) (by simp)
    | ok b =>
      cases ht : instABIVisitorEncoderEntry.go ts' rest vs' with
      | error x => rw [hb, ht] at h; exact absurd (show Except.error x = Except.ok encd from h) (by simp)
      | ok tail =>
        have h' : (Except.ok ((dyn, b) :: tail) : Except Error _) = Except.ok encd := by rw [hb, ht] at h; exact h
        exact ⟨v, vs', b, tail, rfl, hb, ht, (Except.ok.inj h').symm⟩

theorem tuplePack_static (headSizes : List Nat) (dynamics : List Bool) (encd : List (Bool × ByteArray))
    (hd : dynamics.any id = false) :
    tuplePack headSizes dynamics encd = encd.foldl (fun acc x => acc ++ x.2) ByteArray.empty := by
  unfold tuplePack; simp only [hd, Bool.not_false, if_true]

theorem isDynamic_tuple_cons_split (t : ABIType) (ts : List ABIType) (h : isDynamic (.tuple (t :: ts)) = false) :
    isDynamic t = false ∧ isDynamic (.tuple ts) = false := by
  have he : isDynamic (.tuple (t :: ts)) = (isDynamic t || isDynamic (.tuple ts)) := by conv_lhs => rw [isDynamic]
  rw [he] at h
  cases ht : isDynamic t <;> cases hts : isDynamic (.tuple ts) <;> simp_all

theorem isDynamic_tuple_of_all_static (ts : List ABIType) (h : ∀ t ∈ ts, isDynamic t = false) :
    isDynamic (.tuple ts) = false := by
  induction ts with
  | nil => simp [isDynamic]
  | cons t ts ih =>
    have he : isDynamic (.tuple (t :: ts)) = (isDynamic t || isDynamic (.tuple ts)) := by conv_lhs => rw [isDynamic]
    rw [he, h t (by simp), ih (fun t' ht' => h t' (by simp [ht'])), Bool.or_self]

/-- Head size of a static tuple splits over the cons (false for dynamic tuples: their head is 32). -/
theorem headSize_tuple_cons (t : ABIType) (ts : List ABIType) (hstat : isDynamic (.tuple (t :: ts)) = false) :
    headSize (.tuple (t :: ts)) = headSize t + headSize (.tuple ts) := by
  conv_lhs => rw [headSize]
  simp only [hstat, Bool.false_eq_true, if_false]

theorem ba_foldl_snd_init (init : ByteArray) (xs : List (Bool × ByteArray)) :
    xs.foldl (fun acc x => acc ++ x.2) init = init ++ xs.foldl (fun acc x => acc ++ x.2) ByteArray.empty := by
  induction xs generalizing init with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, ByteArray.empty_append]
    rw [ih (init ++ y.2), ih (y.2), ByteArray.append_assoc]

theorem ba_foldl_snd_cons (x : Bool × ByteArray) (xs : List (Bool × ByteArray)) :
    (x :: xs).foldl (fun acc x => acc ++ x.2) ByteArray.empty = x.2 ++ xs.foldl (fun acc x => acc ++ x.2) ByteArray.empty := by
  simp only [List.foldl_cons, ByteArray.empty_append]; exact ba_foldl_snd_init x.2 xs

/-- Static fixed-array encoding size = `headSize`, given the element size fact and staticity. -/
theorem size_eq_fixedArray_core (n : Nat) (e : ABIType)
    (hsize_e : ∀ v ev, encode e v = Except.ok ev → ev.size = headSize e)
    (hstat_e : isDynamic e = false)
    (v : ABIValue) (ev : ByteArray) (henc : encode (.fixedArray n e) v = Except.ok ev) :
    ev.size = headSize (.fixedArray n e) := by
  cases v with
  | array vals =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc
    rcases hentry : foldABIType EncoderEntry e with ⟨elemDyn, elemEnc⟩
    rw [hentry] at henc; dsimp at henc
    have helem : elemEnc = encode e := by unfold encode; rw [hentry]
    by_cases hlen : vals.length = n
    · rw [if_neg (not_not_intro hlen)] at henc
      cases hEL : encodeListElems elemEnc vals with
      | error x => rw [hEL] at henc; exact absurd (show Except.error x = Except.ok ev from henc) (by simp)
      | ok encd =>
        rw [hEL] at henc
        have hpack : ev = arrayPack elemDyn encd :=
          (Except.ok.inj (show Except.ok (arrayPack elemDyn encd) = Except.ok ev from henc)).symm
        have helemF : elemDyn = false := by
          have h := enc_fst_eq_isDynamic e; rw [hentry] at h; simp only [] at h; rw [h, hstat_e]
        rw [helemF] at hpack
        rw [show arrayPack false encd = encd.foldl (·++·) ByteArray.empty from by simp [arrayPack]] at hpack
        have hall : ∀ b ∈ encd, b.size = headSize e := fun b hb => by
          obtain ⟨w, hw⟩ := encodeListElems_mem e vals encd (by rw [← helem]; exact hEL) b hb
          exact hsize_e w b hw
        rw [hpack, concat_size_uniform encd (headSize e) hall,
            encodeListElems_length e vals encd (by rw [← helem]; exact hEL), hlen]
        simp only [headSize, isDynamic, hstat_e, Bool.false_eq_true, if_false]
    · rw [if_pos (by simpa using hlen)] at henc
      exact absurd (show Except.error (Error.arrayElemCount n vals.length) = Except.ok ev from henc) (by simp)
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | tuple _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)

/-- If a tuple type is static, every element type is static. -/
theorem tuple_static_elems (ts : List ABIType) (h : isDynamic (.tuple ts) = false) :
    ∀ t ∈ ts, isDynamic t = false := by
  have h2 : (ts.map isDynamic).any id = false := by rw [tuple_any_isDynamic]; exact h
  intro t ht
  by_contra hc
  have hd : isDynamic t = true := by cases hh : isDynamic t <;> simp_all
  have : (ts.map isDynamic).any id = true := by
    rw [List.any_eq_true]; exact ⟨isDynamic t, List.mem_map.mpr ⟨t, ht, rfl⟩, by simp [hd]⟩
  rw [this] at h2; exact absurd h2 (by simp)

/-! ## Static tuple decode + headSize helpers -/

theorem headSize_foldl_shift (init : Nat) (ts : List ABIType) :
    ts.foldl (fun acc t => acc + headSize t) init = init + ts.foldl (fun acc t => acc + headSize t) 0 := by
  induction ts generalizing init with
  | nil => simp
  | cons t ts ih => simp only [List.foldl_cons]; rw [ih (init + headSize t), ih (0 + headSize t)]; omega

theorem headSize_tuple_foldl (ts : List ABIType) (hstat : isDynamic (.tuple ts) = false) :
    ts.foldl (fun acc t => acc + headSize t) 0 = headSize (.tuple ts) := by
  induction ts with
  | nil => simp [headSize, isDynamic]
  | cons t ts ih =>
    obtain ⟨hst, hsts⟩ := isDynamic_tuple_cons_split t ts hstat
    rw [List.foldl_cons, headSize_foldl_shift, ih hsts, headSize_tuple_cons t ts hstat]; omega

theorem decodeTupleStatic_nil (data : ByteArray) (off : Nat) (acc : List ABIValue) :
    decodeTupleStatic (All.nil : All DecoderEntry []) data off acc = Except.ok (acc.reverse, off) := rfl

theorem decodeTupleStatic_cons {t : ABIType} {ts' : List ABIType} (dec' : DecoderEntry t)
    (rest : All DecoderEntry ts') (data : ByteArray) (off : Nat) (acc : List ABIValue) :
    decodeTupleStatic (All.cons dec' rest) data off acc
      = (dec' data off >>= fun x => decodeTupleStatic rest data x.2 (x.1 :: acc)) := rfl

/-! ## Dynamic-element groundwork (for the well-formedness-conditioned roundtrip)

The dynamic-element roundtrips (dyn array/fixedArray/tuple) hold only under a well-formedness
bound (`enc.size < 2^256`, so every offset fits in 32 bytes): without it an encode can succeed
while producing head pointers `≥ 2^256`, which `uint256ToBytes` renders as >32-byte heads,
corrupting the layout the decoder relies on — so the *unconditional* statement is genuinely
false, not merely unproven, and this file carries no unconditional dynamic-element roundtrip.
The lemmas below are the verified core of the WF-conditioned argument — in particular
`ddeg_concat`, which shows `decodeDynamicElemsGo` recovers the values from the head/tail layout.
They are assembled into `roundtrip_{array,fixedArray,tuple}_wf` and the `wfFactsWF` visitor
(nested structs included), all sorry-free. -/

theorem roundUp32_dvd (n : Nat) : 32 ∣ roundUp32 n := ⟨(n+31)/32, by unfold roundUp32; ring⟩

theorem roundUp32_eq_of_dvd (n : Nat) (h : 32 ∣ n) : roundUp32 n = n := by
  obtain ⟨k, rfl⟩ := h; unfold roundUp32; rw [show (32*k+31)/32 = k from by omega]; ring

theorem uint256ToBytes_size32 (v : Nat) (hv : v < 2 ^ 256) : (uint256ToBytes v).size = 32 :=
  uint256ToBytes_size v (natToBytes_size_bound v hv)

/-- The running head-pointer offsets written by `arrayPack` for a dynamic array. -/
def dynHeadsFrom (off : Nat) : List ByteArray → List ByteArray
  | [] => []
  | e :: es => uint256ToBytes off :: dynHeadsFrom (off + roundUp32 e.size) es

theorem dynHeadsFrom_cons (off : Nat) (e : ByteArray) (es : List ByteArray) :
    dynHeadsFrom off (e :: es) = uint256ToBytes off :: dynHeadsFrom (off + roundUp32 e.size) es := rfl

theorem concat_size_dvd (encd : List ByteArray) (h : ∀ b ∈ encd, 32 ∣ b.size) :
    32 ∣ (encd.foldl (·++·) ByteArray.empty).size := by
  induction encd with
  | nil => simp
  | cons x xs ih =>
    rw [ba_foldl_cons, ByteArray.size_append]
    exact Nat.dvd_add (h x (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem dynHeadsFrom_size (l : List ByteArray) :
    ∀ (off : Nat), off + (l.foldl (·++·) ByteArray.empty).size < 2^256 → (∀ b ∈ l, 32 ∣ b.size) →
    ((dynHeadsFrom off l).foldl (·++·) ByteArray.empty).size = 32 * l.length := by
  induction l with
  | nil => intro off _ _; simp [dynHeadsFrom]
  | cons e es ih =>
    intro off hb halign
    rw [dynHeadsFrom_cons, ba_foldl_cons, ByteArray.size_append]
    have hofflt : off < 2^256 := by rw [ba_foldl_cons, ByteArray.size_append] at hb; omega
    rw [uint256ToBytes_size32 off hofflt]
    have hru : roundUp32 e.size = e.size := roundUp32_eq_of_dvd e.size (halign e (by simp))
    have hb' : (off + e.size) + (es.foldl (·++·) ByteArray.empty).size < 2^256 := by
      rw [ba_foldl_cons, ByteArray.size_append] at hb; omega
    rw [hru, ih (off + e.size) hb' (fun b hbm => halign b (by simp [hbm]))]
    simp [List.length_cons]; ring

/-- Core dynamic-element decode: `decodeDynamicElemsGo` recovers the values, given that the head
    region (a grid of 32-byte pointers) and the contiguous tail region are present in `data` and
    all offsets fit in 32 bytes (`curTail + tails.size < 2^256`). -/
theorem ddeg_concat (e : ABIType) (data : ByteArray)
    (hrt : ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 → encode e v = Except.ok ev →
      data.extract o (o + ev.size) = ev → (foldABIType DecoderEntry e) data o = Except.ok (v, o + ev.size))
    (_hdvd : ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode e v = Except.ok ev → 32 ∣ ev.size) :
    ∀ (vs : List ABIValue) (encd : List ByteArray) (i n off curTail maxEnd : Nat) (vals : List ABIValue),
      encodeListElems (encode e) vs = Except.ok encd →
      n = i + vs.length →
      maxEnd = off + curTail →
      curTail + (encd.foldl (·++·) ByteArray.empty).size < 2^256 →
      (∀ b ∈ encd, 32 ∣ b.size) →
      off + n * 32 ≤ data.size →
      data.extract (off + i * 32) (off + i * 32 + 32 * encd.length) = (dynHeadsFrom curTail encd).foldl (·++·) ByteArray.empty →
      data.extract (off + curTail) (off + curTail + (encd.foldl (·++·) ByteArray.empty).size) = encd.foldl (·++·) ByteArray.empty →
      decodeDynamicElemsGo (foldABIType DecoderEntry e) n i off data vals maxEnd
        = Except.ok (vals.reverse ++ vs, off + curTail + (encd.foldl (·++·) ByteArray.empty).size) := by
  intro vs
  induction vs with
  | nil =>
    intro encd i n off curTail maxEnd vals henc hn hmax _ _ _ _ _
    simp only [encodeListElems, Except.ok.injEq] at henc; subst henc
    simp only [List.foldl_nil, ByteArray.size_empty, Nat.add_zero, List.append_nil]
    unfold decodeDynamicElemsGo
    have hni : ¬ i < n := by simp only [List.length_nil, Nat.add_zero] at hn; omega
    rw [dif_neg hni, hmax]
  | cons v rest ih =>
    intro encd i n off curTail maxEnd vals henc hn hmax hbound halign hsize hheads htails
    obtain ⟨ev, er, hev, her, rfl⟩ := encodeListElems_cons_ok e v rest encd henc
    have hru_ev : roundUp32 ev.size = ev.size := roundUp32_eq_of_dvd ev.size (halign ev (by simp))
    have hcurTail_lt : curTail < 2^256 := by rw [ba_foldl_cons, ByteArray.size_append] at hbound; omega
    have hev_lt : ev.size < 2^256 := by rw [ba_foldl_cons, ByteArray.size_append] at hbound; omega
    have hP32 : (uint256ToBytes curTail).size = 32 := uint256ToBytes_size32 curTail hcurTail_lt
    have hlen1 : ((ev :: er).length : Nat) = er.length + 1 := by simp
    have hni : i < n := by simp only [List.length_cons] at hn; omega
    have hheads_exp : (dynHeadsFrom curTail (ev :: er)).foldl (·++·) ByteArray.empty
        = uint256ToBytes curTail ++ (dynHeadsFrom (curTail + ev.size) er).foldl (·++·) ByteArray.empty := by
      rw [dynHeadsFrom_cons, ba_foldl_cons, hru_ev]
    rw [hlen1] at hheads
    rw [hheads_exp] at hheads
    have hheadchunk : data.extract (off + i * 32) (off + i * 32 + 32) = uint256ToBytes curTail := by
      have e0 : (data.extract (off + i * 32) (off + i * 32 + 32 * (er.length + 1))).extract 0 32
          = data.extract (off + i * 32) (off + i * 32 + 32) := by
        rw [ByteArray.extract_extract, Nat.add_zero,
            show min (off + i * 32 + 32) (off + i * 32 + 32 * (er.length + 1)) = off + i * 32 + 32 from by omega]
      rw [← e0, hheads, ← hP32]; exact ByteArray.extract_append_eq_left rfl
    have htails_exp : (ev :: er).foldl (·++·) ByteArray.empty = ev ++ er.foldl (·++·) ByteArray.empty := ba_foldl_cons ev er
    rw [htails_exp] at htails
    have htailchunk : data.extract (off + curTail) (off + curTail + ev.size) = ev := by
      have e0 : (data.extract (off + curTail) (off + curTail + (ev ++ er.foldl (·++·) ByteArray.empty).size)).extract 0 ev.size
          = data.extract (off + curTail) (off + curTail + ev.size) := by
        rw [ByteArray.extract_extract, Nat.add_zero,
            show min (off + curTail + ev.size) (off + curTail + (ev ++ er.foldl (·++·) ByteArray.empty).size) = off + curTail + ev.size from by rw [ByteArray.size_append]; omega]
      rw [← e0, htails, ByteArray.extract_append_eq_left rfl]
    have hdec_v : (foldABIType DecoderEntry e) data (off + curTail) = Except.ok (v, off + curTail + ev.size) :=
      hrt v ev (off + curTail) hev_lt hev htailchunk
    unfold decodeDynamicElemsGo
    rw [dif_pos hni]
    have hheadbound : ¬ (off + i * 32 + 32 > data.size) := by omega
    rw [if_neg hheadbound]
    simp only [hheadchunk, bytesToNat_uint256ToBytes]
    rw [hdec_v]
    show decodeDynamicElemsGo (foldABIType DecoderEntry e) n (i + 1) off data (v :: vals) (max (off + curTail + ev.size) maxEnd) = _
    rw [show max (off + curTail + ev.size) maxEnd = off + (curTail + ev.size) from by rw [hmax]; omega]
    have hbound' : (curTail + ev.size) + (er.foldl (·++·) ByteArray.empty).size < 2^256 := by
      rw [ba_foldl_cons, ByteArray.size_append] at hbound; omega
    have hheads' : data.extract (off + (i + 1) * 32) (off + (i + 1) * 32 + 32 * er.length) = (dynHeadsFrom (curTail + ev.size) er).foldl (·++·) ByteArray.empty := by
      have hYsz : ((dynHeadsFrom (curTail + ev.size) er).foldl (·++·) ByteArray.empty).size = 32 * er.length :=
        dynHeadsFrom_size er (curTail + ev.size) (by rw [ba_foldl_cons] at hbound; omega) (fun b hb => halign b (by simp [hb]))
      have e0 : (data.extract (off + i * 32) (off + i * 32 + 32 * (er.length + 1))).extract 32 (32 + 32 * er.length)
          = data.extract (off + (i + 1) * 32) (off + (i + 1) * 32 + 32 * er.length) := by
        rw [ByteArray.extract_extract,
            show min (off + i * 32 + (32 + 32 * er.length)) (off + i * 32 + 32 * (er.length + 1)) = off + (i + 1) * 32 + 32 * er.length from by omega,
            show off + i * 32 + 32 = off + (i + 1) * 32 from by omega]
      rw [← e0, hheads]
      exact ByteArray.extract_append_eq_right hP32.symm (by rw [hP32, hYsz])
    have htails' : data.extract (off + (curTail + ev.size)) (off + (curTail + ev.size) + (er.foldl (·++·) ByteArray.empty).size) = er.foldl (·++·) ByteArray.empty := by
      have e0 : (data.extract (off + curTail) (off + curTail + (ev ++ er.foldl (·++·) ByteArray.empty).size)).extract ev.size (ev.size + (er.foldl (·++·) ByteArray.empty).size)
          = data.extract (off + (curTail + ev.size)) (off + (curTail + ev.size) + (er.foldl (·++·) ByteArray.empty).size) := by
        rw [ByteArray.extract_extract,
            show min (off + curTail + (ev.size + (er.foldl (·++·) ByteArray.empty).size)) (off + curTail + (ev ++ er.foldl (·++·) ByteArray.empty).size) = off + (curTail + ev.size) + (er.foldl (·++·) ByteArray.empty).size from by rw [ByteArray.size_append]; omega,
            show off + curTail + ev.size = off + (curTail + ev.size) from by omega]
      rw [← e0, htails]; exact ByteArray.extract_append_eq_right rfl rfl
    rw [ih er (i + 1) n off (curTail + ev.size) (off + (curTail + ev.size)) (v :: vals) her (by simp only [List.length_cons] at hn ⊢; omega) rfl hbound' (fun b hb => halign b (by simp [hb])) hsize hheads' htails']
    have h1 : (v :: vals).reverse ++ rest = vals.reverse ++ v :: rest := by simp
    have h2 : off + (curTail + ev.size) + (er.foldl (·++·) ByteArray.empty).size = off + curTail + ((ev :: er).foldl (·++·) ByteArray.empty).size := by
      rw [ba_foldl_cons, ByteArray.size_append]; omega
    rw [h1, h2]

/-! ### arrayPack characterization + size divisibility (dynamic groundwork, cont.) -/

/-- The fold step used by `arrayPack` for a dynamic array (defeq to its destructuring lambda). -/
abbrev packStep : Nat × ByteArray × ByteArray → ByteArray → Nat × ByteArray × ByteArray :=
  fun acc enc => (acc.1 + roundUp32 enc.size, acc.2.1 ++ uint256ToBytes acc.1, acc.2.2 ++ enc)

theorem packStep_fold (encd : List ByteArray) (startOff : Nat) (h0 t0 : ByteArray) :
    encd.foldl packStep (startOff, h0, t0)
      = (startOff + (encd.map (fun e => roundUp32 e.size)).sum,
         h0 ++ (dynHeadsFrom startOff encd).foldl (·++·) ByteArray.empty,
         t0 ++ encd.foldl (·++·) ByteArray.empty) := by
  induction encd generalizing startOff h0 t0 with
  | nil => simp [dynHeadsFrom]
  | cons e es ih =>
    rw [List.foldl_cons]
    show es.foldl packStep (startOff + roundUp32 e.size, h0 ++ uint256ToBytes startOff, t0 ++ e) = _
    rw [ih (startOff + roundUp32 e.size) (h0 ++ uint256ToBytes startOff) (t0 ++ e), dynHeadsFrom_cons,
        ba_foldl_cons (uint256ToBytes startOff) (dynHeadsFrom (startOff + roundUp32 e.size) es),
        ba_foldl_cons e es]
    simp only [List.map_cons, List.sum_cons, ByteArray.append_assoc, Nat.add_assoc]

/-- `arrayPack` for a dynamic array is the head-pointer grid followed by the concatenated tails. -/
theorem arrayPack_dyn (encd : List ByteArray) :
    arrayPack true encd
      = (dynHeadsFrom (if encd.length = 0 then 32 else encd.length * 32) encd).foldl (·++·) ByteArray.empty
        ++ encd.foldl (·++·) ByteArray.empty := by
  unfold arrayPack
  simp only [Bool.not_true]
  rw [show (List.foldl packStep (if encd.length = 0 then 32 else encd.length * 32, ByteArray.empty, ByteArray.empty) encd) = _ from packStep_fold encd _ ByteArray.empty ByteArray.empty]
  simp [ByteArray.empty_append]

theorem uint256ToBytes_size_ge (v : Nat) : 32 ≤ (uint256ToBytes v).size := by
  unfold uint256ToBytes padLeft; split
  · omega
  · rename_i h; simp only [ByteArray.size_append, zeros_size]; omega

theorem dynHeadsFrom_size_ge (l : List ByteArray) : ∀ (off : Nat), 32 * l.length ≤ ((dynHeadsFrom off l).foldl (·++·) ByteArray.empty).size := by
  induction l with
  | nil => intro off; simp [dynHeadsFrom]
  | cons e es ih =>
    intro off
    rw [dynHeadsFrom_cons, ba_foldl_cons, ByteArray.size_append]
    have := uint256ToBytes_size_ge off
    have := ih (off + roundUp32 e.size)
    simp only [List.length_cons]; omega

/-- Under the well-formedness bound, a dynamic array's packing is 32-aligned. -/
theorem arrayPack_size_dvd (elemDyn : Bool) (encd : List ByteArray)
    (hbound : (arrayPack elemDyn encd).size < 2^256) (halign : ∀ b ∈ encd, 32 ∣ b.size) :
    32 ∣ (arrayPack elemDyn encd).size := by
  cases elemDyn with
  | false =>
    have : arrayPack false encd = encd.foldl (·++·) ByteArray.empty := by simp [arrayPack]
    rw [this]; exact concat_size_dvd encd halign
  | true =>
    by_cases hemp : encd = []
    · subst hemp; rw [arrayPack_dyn]; simp [dynHeadsFrom]
    · have hne0 : encd.length ≠ 0 := fun h => hemp (List.eq_nil_of_length_eq_zero h)
      rw [arrayPack_dyn] at hbound ⊢
      rw [ByteArray.size_append] at hbound ⊢
      rw [show (if encd.length = 0 then 32 else encd.length * 32) = encd.length * 32 from by rw [if_neg hne0]] at hbound ⊢
      have htails_dvd : 32 ∣ (encd.foldl (·++·) ByteArray.empty).size := concat_size_dvd encd halign
      have hge : 32 * encd.length ≤ ((dynHeadsFrom (encd.length * 32) encd).foldl (·++·) ByteArray.empty).size := dynHeadsFrom_size_ge encd (encd.length * 32)
      have hbnd : encd.length * 32 + (encd.foldl (·++·) ByteArray.empty).size < 2^256 := by omega
      rw [dynHeadsFrom_size encd (encd.length * 32) hbnd halign]
      exact Nat.dvd_add ⟨encd.length, rfl⟩ htails_dvd

/-! ### WF-conditioned dynamic array roundtrip -/

theorem mem_size_le_concat (encd : List ByteArray) (b : ByteArray) (hb : b ∈ encd) :
    b.size ≤ (encd.foldl (·++·) ByteArray.empty).size := by
  induction encd with
  | nil => simp at hb
  | cons x xs ih =>
    rw [ba_foldl_cons, ByteArray.size_append]
    rcases List.mem_cons.mp hb with h | h
    · subst h; omega
    · have := ih h; omega

theorem concat_le_arrayPack (elemDyn : Bool) (encd : List ByteArray) :
    (encd.foldl (·++·) ByteArray.empty).size ≤ (arrayPack elemDyn encd).size := by
  cases elemDyn with
  | false => rw [show arrayPack false encd = encd.foldl (·++·) ByteArray.empty from by simp [arrayPack]]
  | true => rw [arrayPack_dyn, ByteArray.size_append]; omega

theorem decodeStaticElemsGo_concat_wf (e : ABIType) (data : ByteArray)
    (dec : ByteArray → Nat → Except Error (ABIValue × Nat))
    (hdec : ∀ (v : ABIValue) (ev : ByteArray) (off : Nat), ev.size < 2^256 → encode e v = Except.ok ev →
      data.extract off (off + ev.size) = ev → dec data off = Except.ok (v, off + ev.size)) :
    ∀ (vs : List ABIValue) (encd : List ByteArray) (i n pos : Nat) (acc : List ABIValue),
      n = i + vs.length →
      encodeListElems (encode e) vs = Except.ok encd →
      (encd.foldl (·++·) ByteArray.empty).size < 2^256 →
      data.extract pos (pos + (encd.foldl (·++·) ByteArray.empty).size) = encd.foldl (·++·) ByteArray.empty →
      decodeStaticElemsGo dec n i pos data acc
        = Except.ok (acc.reverse ++ vs, pos + (encd.foldl (·++·) ByteArray.empty).size) := by
  intro vs
  induction vs with
  | nil =>
    intro encd i n pos acc hn henc _ _
    simp only [encodeListElems, Except.ok.injEq] at henc; subst henc
    simp only [List.foldl_nil, ByteArray.size_empty, Nat.add_zero, List.append_nil]
    unfold decodeStaticElemsGo
    have hni : ¬ i < n := by simp only [List.length_nil, Nat.add_zero] at hn; omega
    simp [hni]
  | cons v rest ih =>
    intro encd i n pos acc hn henc hbound hslice
    obtain ⟨ev, er, hev, her, rfl⟩ := encodeListElems_cons_ok e v rest encd henc
    rw [ba_foldl_cons] at hslice hbound ⊢
    have hsz : (ev ++ er.foldl (·++·) ByteArray.empty).size = ev.size + (er.foldl (·++·) ByteArray.empty).size := ByteArray.size_append
    have hev_lt : ev.size < 2^256 := by rw [hsz] at hbound; omega
    have hm1 : min (pos + ev.size) (pos + (ev ++ er.foldl (·++·) ByteArray.empty).size) = pos + ev.size := by rw [hsz]; omega
    have hm2 : min (pos + (ev.size + (er.foldl (·++·) ByteArray.empty).size)) (pos + (ev ++ er.foldl (·++·) ByteArray.empty).size) = pos + ev.size + (er.foldl (·++·) ByteArray.empty).size := by rw [hsz]; omega
    have hslice_ev : data.extract pos (pos + ev.size) = ev := by
      have e0 : (data.extract pos (pos + (ev ++ er.foldl (·++·) ByteArray.empty).size)).extract 0 ev.size = data.extract pos (pos + ev.size) := by
        rw [ByteArray.extract_extract, Nat.add_zero, hm1]
      rw [← e0, hslice, ByteArray.extract_append_eq_left rfl]
    have hslice_rest : data.extract (pos + ev.size) (pos + ev.size + (er.foldl (·++·) ByteArray.empty).size) = er.foldl (·++·) ByteArray.empty := by
      have e0 : (data.extract pos (pos + (ev ++ er.foldl (·++·) ByteArray.empty).size)).extract ev.size (ev.size + (er.foldl (·++·) ByteArray.empty).size) = data.extract (pos + ev.size) (pos + ev.size + (er.foldl (·++·) ByteArray.empty).size) := by
        rw [ByteArray.extract_extract, hm2]
      rw [← e0, hslice]; exact ByteArray.extract_append_eq_right rfl rfl
    unfold decodeStaticElemsGo
    have hni : i < n := by simp only [List.length_cons] at hn; omega
    rw [dif_pos hni, hdec v ev pos hev_lt hev hslice_ev]
    show decodeStaticElemsGo dec n (i + 1) (pos + ev.size) data (v :: acc) = _
    have hbound' : (er.foldl (·++·) ByteArray.empty).size < 2^256 := by rw [hsz] at hbound; omega
    rw [ih er (i + 1) n (pos + ev.size) (v :: acc) (by simp only [List.length_cons] at hn ⊢; omega) her hbound' hslice_rest]
    have h1 : (v :: acc).reverse ++ rest = acc.reverse ++ v :: rest := by simp
    have h2 : pos + ev.size + (er.foldl (·++·) ByteArray.empty).size = pos + (ev ++ er.foldl (·++·) ByteArray.empty).size := by rw [hsz]; omega
    rw [h1, h2]


theorem roundtrip_array_wf (e : ABIType) (data : ByteArray)
    (hrt : ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 → encode e v = Except.ok ev →
      data.extract o (o + ev.size) = ev → decode e data o = Except.ok (v, o + ev.size))
    (hdvd : ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode e v = Except.ok ev → 32 ∣ ev.size)
    (v : ABIValue) (enc : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256)
    (henc : encode (.array e) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.array e) data off = Except.ok (v, off + enc.size) := by
  cases v with
  | array vals =>
    unfold encode foldABIType at henc
    delta instABIVisitorEncoderEntry at henc
    rcases hentry : foldABIType EncoderEntry e with ⟨elemDyn, elemEnc⟩
    rw [hentry] at henc; dsimp at henc
    have helem : elemEnc = encode e := by unfold encode; rw [hentry]
    split at henc
    · rename_i hlt
      cases hEL : encodeListElems elemEnc vals with
      | error x => rw [hEL] at henc; exact absurd (show Except.error x = Except.ok enc from henc) (by simp)
      | ok encd =>
        rw [hEL] at henc
        have hEL' : encodeListElems (encode e) vals = Except.ok encd := by rw [← helem]; exact hEL
        have hpack : enc = uint256ToBytes vals.length ++ arrayPack elemDyn encd :=
          (Except.ok.inj (show Except.ok (uint256ToBytes vals.length ++ arrayPack elemDyn encd) = Except.ok enc from henc)).symm
        have hPsz : (uint256ToBytes vals.length).size = 32 :=
          uint256ToBytes_size vals.length (natToBytes_size_bound vals.length hlt)
        set packed := arrayPack elemDyn encd with hpk
        have hencsz : enc.size = 32 + packed.size := by rw [hpack, ByteArray.size_append, hPsz]
        have hpk_lt : packed.size < 2^256 := by rw [hencsz] at hwf; omega
        have hbound_all : off + enc.size ≤ data.size :=
          not_gt_of_extract_eq data off enc.size (by rw [hdata]) (by rw [hencsz]; omega)
        have hb32 : ¬ (off + 32 > data.size) := by rw [hencsz] at hbound_all; omega
        have hm1 : min (off + 32) (off + enc.size) = off + 32 := by rw [hencsz]; omega
        have hprefix : data.extract off (off + 32) = uint256ToBytes vals.length := by
          have e0 : (data.extract off (off + enc.size)).extract 0 32 = data.extract off (off + 32) := by
            rw [ByteArray.extract_extract, Nat.add_zero, hm1]
          rw [← e0, hdata, hpack, ← hPsz]; exact ByteArray.extract_append_eq_left rfl
        have hlen : bytesToNat (data.extract off (off + 32)) = vals.length := by
          rw [hprefix]; exact bytesToNat_uint256ToBytes vals.length
        have hm2 : min (off + (32 + packed.size)) (off + enc.size) = off + 32 + packed.size := by rw [hencsz]; omega
        have hsuffix : data.extract (off + 32) (off + 32 + packed.size) = packed := by
          have e0 : (data.extract off (off + enc.size)).extract 32 (32 + packed.size) = data.extract (off + 32) (off + 32 + packed.size) := by
            rw [ByteArray.extract_extract, hm2]
          rw [← e0, hdata, hpack]; exact ByteArray.extract_append_eq_right hPsz.symm (by rw [hPsz])
        have halign : ∀ b ∈ encd, 32 ∣ b.size := fun b hb => by
          obtain ⟨w, hw⟩ := encodeListElems_mem e vals encd hEL' b hb
          have hble : b.size ≤ packed.size := le_trans (mem_size_le_concat encd b hb) (by rw [hpk]; exact concat_le_arrayPack elemDyn encd)
          exact hdvd w b (by omega) hw
        unfold decode foldABIType
        delta instABIVisitorDecoderEntry
        dsimp
        rw [if_neg hb32]
        simp only [hlen]
        cases hdyn : isDynamic e with
        | false =>
          have helemF : elemDyn = false := by
            have h := enc_fst_eq_isDynamic e; rw [hentry] at h; simp only [] at h; rw [h, hdyn]
          have hpackc : packed = encd.foldl (·++·) ByteArray.empty := by rw [hpk, helemF]; simp [arrayPack]
          simp only [decodeArrayElems, decodeStaticElems, Bool.false_eq_true, if_false]
          have hslice' : data.extract (off + 32) ((off + 32) + (encd.foldl (·++·) ByteArray.empty).size) = encd.foldl (·++·) ByteArray.empty := by
            rw [← hpackc]; exact hsuffix
          rw [decodeStaticElemsGo_concat_wf e data (foldABIType DecoderEntry e)
                (fun w ev o h1 h2 h3 => hrt w ev o h1 h2 h3) vals encd 0 vals.length (off + 32) []
                (by omega) hEL' (by rw [← hpackc]; exact hpk_lt) hslice']
          rw [show (off + 32) + (encd.foldl (·++·) ByteArray.empty).size = off + enc.size from by rw [← hpackc, hencsz]; omega]
          rfl
        | true =>
          have helemT : elemDyn = true := by
            have h := enc_fst_eq_isDynamic e; rw [hentry] at h; simp only [] at h; rw [h, hdyn]
          simp only [decodeArrayElems, if_true, decodeDynamicElems]
          by_cases hvemp : vals = []
          · subst hvemp
            simp only [encodeListElems, Except.ok.injEq] at hEL'; subst hEL'
            have hpe : packed = ByteArray.empty := by rw [hpk, helemT, arrayPack_dyn]; simp [dynHeadsFrom]
            simp only [List.length_nil]
            unfold decodeDynamicElemsGo
            simp only [Nat.lt_irrefl, ↓reduceDIte, List.reverse_nil]
            rw [show off + enc.size = off + 32 from by rw [hencsz, hpe, ByteArray.size_empty]]
            rfl
          · have hlenv : encd.length = vals.length := encodeListElems_length e vals encd hEL'
            have hne0 : encd.length ≠ 0 := by rw [hlenv]; exact fun h => hvemp (List.eq_nil_of_length_eq_zero h)
            set heads := (dynHeadsFrom (vals.length * 32) encd).foldl (·++·) ByteArray.empty with hh
            set tails := encd.foldl (·++·) ByteArray.empty with ht
            have hpackht : packed = heads ++ tails := by
              rw [hh, ht, hpk, helemT, arrayPack_dyn, if_neg hne0, hlenv]
            have hpsz : packed.size = heads.size + tails.size := by rw [hpackht, ByteArray.size_append]
            have hge : vals.length * 32 ≤ heads.size := by
              rw [hh]; have := dynHeadsFrom_size_ge encd (vals.length * 32); rw [hlenv] at this; omega
            have hbnd : vals.length * 32 + tails.size < 2^256 := by omega
            have hheads_size : heads.size = vals.length * 32 := by
              rw [hh]; have := dynHeadsFrom_size encd (vals.length * 32) (by rw [← ht]; omega) halign; rw [hlenv] at this; omega
            have hsuffix' : data.extract (off + 32) (off + 32 + (heads ++ tails).size) = heads ++ tails := by rw [← hpackht]; exact hsuffix
            have hheads_ex : data.extract (off + 32) (off + 32 + heads.size) = heads := by
              have e0 : (data.extract (off + 32) (off + 32 + (heads ++ tails).size)).extract 0 heads.size = data.extract (off + 32) (off + 32 + heads.size) := by
                rw [ByteArray.extract_extract, Nat.add_zero, show min (off + 32 + heads.size) (off + 32 + (heads ++ tails).size) = off + 32 + heads.size from by rw [ByteArray.size_append]; omega]
              rw [← e0, hsuffix', ByteArray.extract_append_eq_left rfl]
            have htails_ex : data.extract (off + 32 + heads.size) (off + 32 + heads.size + tails.size) = tails := by
              have e0 : (data.extract (off + 32) (off + 32 + (heads ++ tails).size)).extract heads.size (heads.size + tails.size) = data.extract (off + 32 + heads.size) (off + 32 + heads.size + tails.size) := by
                rw [ByteArray.extract_extract, show min (off + 32 + (heads.size + tails.size)) (off + 32 + (heads ++ tails).size) = off + 32 + heads.size + tails.size from by rw [ByteArray.size_append]; omega]
              rw [← e0, hsuffix']; exact ByteArray.extract_append_eq_right rfl rfl
            have hheadseq : data.extract (off + 32 + 0 * 32) (off + 32 + 0 * 32 + 32 * encd.length) = (dynHeadsFrom (vals.length * 32) encd).foldl (·++·) ByteArray.empty := by
              simp only [Nat.zero_mul, Nat.add_zero]
              rw [show 32 * encd.length = heads.size from by rw [hheads_size, hlenv]; ring, ← hh]; exact hheads_ex
            have htailseq : data.extract (off + 32 + vals.length * 32) (off + 32 + vals.length * 32 + tails.size) = tails := by
              rw [← hheads_size]; exact htails_ex
            rw [ddeg_concat e data hrt hdvd vals encd 0 vals.length (off + 32) (vals.length * 32) (off + 32 + vals.length * 32) []
                  hEL' (by omega) rfl (by rw [← ht]; omega) halign (by omega) hheadseq htailseq]
            rw [List.reverse_nil, List.nil_append,
                show off + 32 + vals.length * 32 + tails.size = off + enc.size from by rw [hencsz, hpsz, hheads_size]; omega]
            rfl

    · exact absurd (show Except.error (Error.arrayLengthOverflow vals.length) = Except.ok enc from henc) (by simp)
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | tuple _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)

/-! ### Concrete WF roundtrips for the common dynamic-element arrays -/

theorem szdvd_bytes (v : ABIValue) (ev : ByteArray) (_hsz : ev.size < 2^256) (henc : encode .bytes v = Except.ok ev) : 32 ∣ ev.size := by
  cases v with
  | bytes v' =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    split at henc
    · rename_i hlt
      have hev := Except.ok.inj henc
      rw [← hev, ByteArray.size_append]
      have hPsz : (uint256ToBytes v'.size).size = 32 := uint256ToBytes_size v'.size (natToBytes_size_bound v'.size (by assumption))
      have hpad : (padRight v' (roundUp32 v'.size)).size = roundUp32 v'.size := by
        unfold padRight; split
        · have : v'.size ≤ roundUp32 v'.size := by unfold roundUp32; omega
          omega
        · simp [zeros_size]; unfold roundUp32; omega
      rw [hPsz, hpad]; exact Nat.dvd_add (by norm_num) (roundUp32_dvd v'.size)
    · exact absurd (show Except.error _ = Except.ok ev from henc) (by simp)
  | _ => badVal henc

theorem szdvd_string (v : ABIValue) (ev : ByteArray) (_hsz : ev.size < 2^256) (henc : encode .string v = Except.ok ev) : 32 ∣ ev.size := by
  cases v with
  | string v' =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    split at henc
    · rename_i hlt
      have hev := Except.ok.inj henc
      rw [← hev, ByteArray.size_append]
      have hPsz : (uint256ToBytes v'.toUTF8.size).size = 32 := uint256ToBytes_size v'.toUTF8.size (natToBytes_size_bound v'.toUTF8.size (by assumption))
      have hpad : (padRight v'.toUTF8 (roundUp32 v'.toUTF8.size)).size = roundUp32 v'.toUTF8.size := by
        unfold padRight; split
        · have : v'.toUTF8.size ≤ roundUp32 v'.toUTF8.size := by unfold roundUp32; omega
          omega
        · simp [zeros_size]; unfold roundUp32; omega
      rw [hPsz, hpad]; exact Nat.dvd_add (by norm_num) (roundUp32_dvd v'.toUTF8.size)
    · exact absurd (show Except.error _ = Except.ok ev from henc) (by simp)
  | _ => badVal henc

/-- `bytes[]` roundtrips under the well-formedness bound (`enc.size < 2^256`). -/
theorem roundtrip_bytes_array_wf (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256) (henc : encode (.array .bytes) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.array .bytes) data off = Except.ok (v, off + enc.size) :=
  roundtrip_array_wf .bytes data
    (fun v ev o _ h2 h3 => roundtrip_off_bytes v ev data o h2 h3) szdvd_bytes v enc off hwf henc hdata

/-- `string[]` roundtrips under the well-formedness bound (`enc.size < 2^256`). -/
theorem roundtrip_string_array_wf (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256) (henc : encode (.array .string) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.array .string) data off = Except.ok (v, off + enc.size) :=
  roundtrip_array_wf .string data
    (fun v ev o _ h2 h3 => roundtrip_off_string v ev data o h2 h3) szdvd_string v enc off hwf henc hdata

/-! ### WF-conditioned dynamic fixed-array roundtrip -/
theorem decodeArrayElems_zero (dec : ByteArray → Nat → Except Error (ABIValue × Nat)) (isDyn : Bool) (data : ByteArray) (off : Nat) :
    decodeArrayElems dec isDyn 0 data off = Except.ok ([], off) := by
  unfold decodeArrayElems
  cases isDyn with
  | false => simp only [Bool.false_eq_true, if_false]; unfold decodeStaticElems decodeStaticElemsGo; simp
  | true => simp only [if_true]; unfold decodeDynamicElems decodeDynamicElemsGo; simp

theorem roundtrip_fixedArray_wf (n : Nat) (e : ABIType) (data : ByteArray)
    (hrt : ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 → encode e v = Except.ok ev →
      data.extract o (o + ev.size) = ev → decode e data o = Except.ok (v, o + ev.size))
    (hdvd : ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode e v = Except.ok ev → 32 ∣ ev.size)
    (v : ABIValue) (enc : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256)
    (henc : encode (.fixedArray n e) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.fixedArray n e) data off = Except.ok (v, off + enc.size) := by
  cases v with
  | array vals =>
    unfold encode foldABIType at henc
    delta instABIVisitorEncoderEntry at henc
    rcases hentry : foldABIType EncoderEntry e with ⟨elemDyn, elemEnc⟩
    rw [hentry] at henc; dsimp at henc
    have helem : elemEnc = encode e := by unfold encode; rw [hentry]
    by_cases hlen : vals.length = n
    · rw [if_neg (not_not_intro hlen)] at henc
      cases hEL : encodeListElems elemEnc vals with
      | error x => rw [hEL] at henc; exact absurd (show Except.error x = Except.ok enc from henc) (by simp)
      | ok encd =>
        rw [hEL] at henc
        have hEL' : encodeListElems (encode e) vals = Except.ok encd := by rw [← helem]; exact hEL
        have hpack : enc = arrayPack elemDyn encd :=
          (Except.ok.inj (show Except.ok (arrayPack elemDyn encd) = Except.ok enc from henc)).symm
        have halign : ∀ b ∈ encd, 32 ∣ b.size := fun b hb => by
          obtain ⟨w, hw⟩ := encodeListElems_mem e vals encd hEL' b hb
          have hble : b.size ≤ enc.size := by rw [hpack]; exact le_trans (mem_size_le_concat encd b hb) (concat_le_arrayPack elemDyn encd)
          exact hdvd w b (by omega) hw
        unfold decode foldABIType
        delta instABIVisitorDecoderEntry
        dsimp
        cases hdyn : isDynamic e with
        | false =>
          have helemF : elemDyn = false := by
            have h := enc_fst_eq_isDynamic e; rw [hentry] at h; simp only [] at h; rw [h, hdyn]
          have hpackc : enc = encd.foldl (·++·) ByteArray.empty := by rw [hpack, helemF]; simp [arrayPack]
          simp only [decodeArrayElems, decodeStaticElems, Bool.false_eq_true, if_false]
          rw [decodeStaticElemsGo_concat_wf e data (foldABIType DecoderEntry e)
                (fun w ev o h1 h2 h3 => hrt w ev o h1 h2 h3) vals encd 0 n off []
                (by omega) hEL' (by rw [← hpackc]; exact hwf) (by rw [← hpackc]; exact hdata)]
          rw [show off + (encd.foldl (·++·) ByteArray.empty).size = off + enc.size from by rw [← hpackc]]
          rfl
        | true =>
          have helemT : elemDyn = true := by
            have h := enc_fst_eq_isDynamic e; rw [hentry] at h; simp only [] at h; rw [h, hdyn]
          by_cases hvemp : vals = []
          · subst hvemp
            simp only [encodeListElems, Except.ok.injEq] at hEL'; subst hEL'
            have hn0 : n = 0 := by simpa using hlen.symm
            subst hn0
            have hee : enc.size = 0 := by rw [hpack, helemT, arrayPack_dyn]; simp [dynHeadsFrom]
            rw [decodeArrayElems_zero, show off + enc.size = off from by omega]
            rfl
          · simp only [decodeArrayElems, if_true, decodeDynamicElems]
            have hlenv : encd.length = vals.length := encodeListElems_length e vals encd hEL'
            have hne0 : encd.length ≠ 0 := by rw [hlenv]; exact fun h => hvemp (List.eq_nil_of_length_eq_zero h)
            set heads := (dynHeadsFrom (vals.length * 32) encd).foldl (·++·) ByteArray.empty with hh
            set tails := encd.foldl (·++·) ByteArray.empty with ht
            have hpackht : enc = heads ++ tails := by
              rw [hh, ht, hpack, helemT, arrayPack_dyn, if_neg hne0, hlenv]
            have hpsz : enc.size = heads.size + tails.size := by rw [hpackht, ByteArray.size_append]
            have hge : vals.length * 32 ≤ heads.size := by
              rw [hh]; have := dynHeadsFrom_size_ge encd (vals.length * 32); rw [hlenv] at this; omega
            have hbnd : vals.length * 32 + tails.size < 2^256 := by omega
            have hheads_size : heads.size = vals.length * 32 := by
              rw [hh]; have := dynHeadsFrom_size encd (vals.length * 32) (by rw [← ht]; omega) halign; rw [hlenv] at this; omega
            have hsuffix' : data.extract off (off + (heads ++ tails).size) = heads ++ tails := by rw [← hpackht]; exact hdata
            have hheads_ex : data.extract off (off + heads.size) = heads := by
              have e0 : (data.extract off (off + (heads ++ tails).size)).extract 0 heads.size = data.extract off (off + heads.size) := by
                rw [ByteArray.extract_extract, Nat.add_zero, show min (off + heads.size) (off + (heads ++ tails).size) = off + heads.size from by rw [ByteArray.size_append]; omega]
              rw [← e0, hsuffix', ByteArray.extract_append_eq_left rfl]
            have htails_ex : data.extract (off + heads.size) (off + heads.size + tails.size) = tails := by
              have e0 : (data.extract off (off + (heads ++ tails).size)).extract heads.size (heads.size + tails.size) = data.extract (off + heads.size) (off + heads.size + tails.size) := by
                rw [ByteArray.extract_extract, show min (off + (heads.size + tails.size)) (off + (heads ++ tails).size) = off + heads.size + tails.size from by rw [ByteArray.size_append]; omega]
              rw [← e0, hsuffix']; exact ByteArray.extract_append_eq_right rfl rfl
            have hheadseq : data.extract (off + 0 * 32) (off + 0 * 32 + 32 * encd.length) = (dynHeadsFrom (vals.length * 32) encd).foldl (·++·) ByteArray.empty := by
              simp only [Nat.zero_mul, Nat.add_zero]
              rw [show 32 * encd.length = heads.size from by rw [hheads_size, hlenv]; ring, ← hh]; exact hheads_ex
            have htailseq : data.extract (off + vals.length * 32) (off + vals.length * 32 + tails.size) = tails := by
              rw [← hheads_size]; exact htails_ex
            have hvpos : vals.length ≠ 0 := by rw [← hlenv]; exact hne0
            have hbound_all : off + enc.size ≤ data.size :=
              not_gt_of_extract_eq data off enc.size (by rw [hdata]) (by omega)
            rw [show n = vals.length from hlen.symm]
            rw [ddeg_concat e data hrt hdvd vals encd 0 vals.length off (vals.length * 32) (off + vals.length * 32) []
                  hEL' (by omega) rfl (by rw [← ht]; omega) halign (by omega) hheadseq htailseq]
            rw [List.reverse_nil, List.nil_append,
                show off + vals.length * 32 + tails.size = off + enc.size from by rw [hpsz, hheads_size]; omega]
            rfl
    · rw [if_pos (by simpa using hlen)] at henc
      exact absurd (show Except.error (Error.arrayElemCount n vals.length) = Except.ok enc from henc) (by simp)
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | tuple _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)

/-! ### General array szdvd + nested composition demo -/
-- general array szdvd, given element alignment
theorem szdvd_array (e : ABIType)
    (hdvd_e : ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode e v = Except.ok ev → 32 ∣ ev.size)
    (v : ABIValue) (ev : ByteArray) (hsz : ev.size < 2^256) (henc : encode (.array e) v = Except.ok ev) :
    32 ∣ ev.size := by
  cases v with
  | array vals =>
    unfold encode foldABIType at henc
    delta instABIVisitorEncoderEntry at henc
    rcases hentry : foldABIType EncoderEntry e with ⟨elemDyn, elemEnc⟩
    rw [hentry] at henc; dsimp at henc
    have helem : elemEnc = encode e := by unfold encode; rw [hentry]
    split at henc
    · rename_i hlt
      cases hEL : encodeListElems elemEnc vals with
      | error x => rw [hEL] at henc; exact absurd (show Except.error x = Except.ok ev from henc) (by simp)
      | ok encd =>
        rw [hEL] at henc
        have hEL' : encodeListElems (encode e) vals = Except.ok encd := by rw [← helem]; exact hEL
        have hpack : ev = uint256ToBytes vals.length ++ arrayPack elemDyn encd :=
          (Except.ok.inj (show Except.ok (uint256ToBytes vals.length ++ arrayPack elemDyn encd) = Except.ok ev from henc)).symm
        have hPsz : (uint256ToBytes vals.length).size = 32 :=
          uint256ToBytes_size vals.length (natToBytes_size_bound vals.length hlt)
        have hencsz : ev.size = 32 + (arrayPack elemDyn encd).size := by rw [hpack, ByteArray.size_append, hPsz]
        have halign : ∀ b ∈ encd, 32 ∣ b.size := fun b hb => by
          obtain ⟨w, hw⟩ := encodeListElems_mem e vals encd hEL' b hb
          have hble : b.size ≤ ev.size := by
            rw [hpack, ByteArray.size_append]
            have := le_trans (mem_size_le_concat encd b hb) (concat_le_arrayPack elemDyn encd)
            omega
          exact hdvd_e w b (by omega) hw
        rw [hencsz]
        exact Nat.dvd_add (by norm_num) (arrayPack_size_dvd elemDyn encd (by omega) halign)
    · exact absurd (show Except.error (Error.arrayLengthOverflow vals.length) = Except.ok ev from henc) (by simp)
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | tuple _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)

/-- Nested `bytes[][]` roundtrips under the bound — demonstrates the WF results compose. -/
theorem roundtrip_bytes_array_array_wf (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256) (henc : encode (.array (.array .bytes)) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.array (.array .bytes)) data off = Except.ok (v, off + enc.size) :=
  roundtrip_array_wf (.array .bytes) data
    (fun v ev o hsz h2 h3 => roundtrip_bytes_array_wf v ev data o hsz h2 h3)
    (szdvd_array .bytes szdvd_bytes) v enc off hwf henc hdata

/-! ### Dynamic tuple groundwork: tuplePack fold characterization -/

def tupleHeadsFrom (off : Nat) : List (Bool × ByteArray) → List ByteArray
  | [] => []
  | (isDyn, enc) :: rest => (if isDyn then uint256ToBytes off else enc) :: tupleHeadsFrom (if isDyn then off + roundUp32 enc.size else off) rest

def tupleTails : List (Bool × ByteArray) → ByteArray
  | [] => ByteArray.empty
  | (isDyn, enc) :: rest => (if isDyn then enc else ByteArray.empty) ++ tupleTails rest

theorem tupleHeadsFrom_cons (off : Nat) (isDyn : Bool) (enc : ByteArray) (rest : List (Bool × ByteArray)) :
    tupleHeadsFrom off ((isDyn, enc) :: rest)
      = (if isDyn then uint256ToBytes off else enc) :: tupleHeadsFrom (if isDyn then off + roundUp32 enc.size else off) rest := rfl

abbrev tupleStep : Nat × ByteArray × ByteArray → Bool × ByteArray → Nat × ByteArray × ByteArray :=
  fun acc p => if p.1 then (acc.1 + roundUp32 p.2.size, acc.2.1 ++ uint256ToBytes acc.1, acc.2.2 ++ p.2)
               else (acc.1, acc.2.1 ++ p.2, acc.2.2)

theorem tupleStep_fold (encoded : List (Bool × ByteArray)) (startOff : Nat) (h0 t0 : ByteArray) :
    encoded.foldl tupleStep (startOff, h0, t0)
      = (encoded.foldl (fun o p => if p.1 then o + roundUp32 p.2.size else o) startOff,
         h0 ++ (tupleHeadsFrom startOff encoded).foldl (·++·) ByteArray.empty,
         t0 ++ tupleTails encoded) := by
  induction encoded generalizing startOff h0 t0 with
  | nil => simp [tupleHeadsFrom, tupleTails]
  | cons p rest ih =>
    obtain ⟨isDyn, enc⟩ := p
    cases isDyn with
    | true =>
      show rest.foldl tupleStep (startOff + roundUp32 enc.size, h0 ++ uint256ToBytes startOff, t0 ++ enc) = _
      rw [ih (startOff + roundUp32 enc.size) (h0 ++ uint256ToBytes startOff) (t0 ++ enc)]
      have ho : ((true, enc) :: rest).foldl (fun o p => if p.1 then o + roundUp32 p.2.size else o) startOff
              = rest.foldl (fun o p => if p.1 then o + roundUp32 p.2.size else o) (startOff + roundUp32 enc.size) := by simp [List.foldl_cons]
      have hh : (tupleHeadsFrom startOff ((true, enc) :: rest)).foldl (·++·) ByteArray.empty
              = uint256ToBytes startOff ++ (tupleHeadsFrom (startOff + roundUp32 enc.size) rest).foldl (·++·) ByteArray.empty := by
        rw [tupleHeadsFrom_cons]; simp only [↓reduceIte]; rw [ba_foldl_cons]
      have ht : tupleTails ((true, enc) :: rest) = enc ++ tupleTails rest := by rw [tupleTails]; simp
      rw [ho, hh, ht, ByteArray.append_assoc, ByteArray.append_assoc]
    | false =>
      show rest.foldl tupleStep (startOff, h0 ++ enc, t0) = _
      rw [ih startOff (h0 ++ enc) t0]
      have ho : ((false, enc) :: rest).foldl (fun o p => if p.1 then o + roundUp32 p.2.size else o) startOff
              = rest.foldl (fun o p => if p.1 then o + roundUp32 p.2.size else o) startOff := by simp [List.foldl_cons]
      have hh : (tupleHeadsFrom startOff ((false, enc) :: rest)).foldl (·++·) ByteArray.empty
              = enc ++ (tupleHeadsFrom startOff rest).foldl (·++·) ByteArray.empty := by
        rw [tupleHeadsFrom_cons]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [ba_foldl_cons]
      have ht : tupleTails ((false, enc) :: rest) = tupleTails rest := by rw [tupleTails]; simp
      rw [ho, hh, ht, ByteArray.append_assoc]

/-- `tuplePack` for a dynamic tuple is the interleaved head region followed by the dynamic tails. -/
theorem tuplePack_dyn (headSizes : List Nat) (dynamics : List Bool) (encoded : List (Bool × ByteArray))
    (hd : dynamics.any id = true) :
    tuplePack headSizes dynamics encoded
      = (tupleHeadsFrom (headSizes.foldl (·+·) 0) encoded).foldl (·++·) ByteArray.empty ++ tupleTails encoded := by
  unfold tuplePack
  simp only [hd, Bool.not_true, Bool.false_eq_true, if_false]
  rw [show (List.foldl tupleStep (headSizes.foldl (·+·) 0, ByteArray.empty, ByteArray.empty) encoded)
        = _ from tupleStep_fold encoded _ ByteArray.empty ByteArray.empty]
  simp [ByteArray.empty_append]

/-! ### Dynamic tuple decode (decodeTupleDynamic) -/
theorem headSize_dynamic (t : ABIType) (h : isDynamic t = true) : headSize t = 32 := by
  cases t with
  | bytes => simp [headSize]
  | string => simp [headSize]
  | array e => simp [headSize]
  | fixedArray n e => rw [headSize, if_pos h]
  | tuple ts => cases ts with
    | nil => simp [isDynamic] at h
    | cons t' ts' => rw [headSize, if_pos h]
  | uint s => simp [isDynamic] at h
  | int s => simp [isDynamic] at h
  | bool => simp [isDynamic] at h
  | address => simp [isDynamic] at h
  | fixedBytes s => simp [isDynamic] at h

theorem headSize_mem_le (l : List ABIType) (t : ABIType) (h : t ∈ l) :
    headSize t ≤ l.foldl (fun a t => a + headSize t) 0 := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
    rw [List.foldl_cons, headSize_foldl_shift]
    rcases List.mem_cons.mp h with h1 | h2
    · subst h1; omega
    · have := ih h2; omega

theorem foldl_append_ge (processed ts : List ABIType) :
    processed.foldl (fun a t => a + headSize t) 0 ≤ (processed ++ ts).foldl (fun a t => a + headSize t) 0 := by
  rw [List.foldl_append, headSize_foldl_shift _ ts]; omega

theorem foldl_snoc (processed : List ABIType) (t : ABIType) :
    (processed ++ [t]).foldl (fun a t => a + headSize t) 0 = processed.foldl (fun a t => a + headSize t) 0 + headSize t := by
  rw [List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil]

theorem tupleTails_dyn (b : ByteArray) (tail : List (Bool × ByteArray)) :
    tupleTails ((true, b) :: tail) = b ++ tupleTails tail := by rw [tupleTails]; simp
theorem tupleTails_stat (b : ByteArray) (tail : List (Bool × ByteArray)) :
    tupleTails ((false, b) :: tail) = tupleTails tail := by rw [tupleTails]; simp
theorem tupleHeadsFrom_stat (off : Nat) (b : ByteArray) (tail : List (Bool × ByteArray)) :
    tupleHeadsFrom off ((false, b) :: tail) = b :: tupleHeadsFrom off tail := by rw [tupleHeadsFrom]; simp
theorem tupleHeadsFrom_dyn (off : Nat) (b : ByteArray) (tail : List (Bool × ByteArray)) :
    tupleHeadsFrom off ((true, b) :: tail) = uint256ToBytes off :: tupleHeadsFrom (off + roundUp32 b.size) tail := by rw [tupleHeadsFrom]; simp

theorem dtd_nil (fullTs : List ABIType) (data : ByteArray) (offset i : Nat) (acc : List ABIValue) (maxEnd : Nat) :
    decodeTupleDynamic (All.nil : All DecoderEntry []) fullTs [] data offset i acc maxEnd = Except.ok (acc.reverse, maxEnd) := rfl

theorem dtd_cons {t : ABIType} {ts'' : List ABIType} (dec' : DecoderEntry t) (rest : All DecoderEntry ts'')
    (fullTs : List ABIType) (data : ByteArray) (offset i : Nat) (acc : List ABIValue) (maxEnd : Nat) :
    decodeTupleDynamic (All.cons dec' rest) fullTs (t :: ts'') data offset i acc maxEnd
      = (let headOff := offset + (fullTs.take i).foldl (fun acc t => acc + headSize t) 0
         if headOff + 32 > data.size then .error (.dataTooShortForHead headOff)
         else if isDynamic t then
           (dec' data (offset + bytesToNat (data.extract headOff (headOff + 32))) >>= fun x =>
             decodeTupleDynamic rest fullTs ts'' data offset (i + 1) (x.1 :: acc) (max maxEnd x.2))
         else
           (dec' data headOff >>= fun x =>
             decodeTupleDynamic rest fullTs ts'' data offset (i + 1) (x.1 :: acc) maxEnd)) := rfl

theorem dtd_concat (fullTs : List ABIType) (data : ByteArray) (offset : Nat)
    (hbd : offset + fullTs.foldl (fun a t => a + headSize t) 0 + 32 ≤ data.size)
    (hrt : ∀ t ∈ fullTs, ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 →
      encode t v = Except.ok ev → data.extract o (o + ev.size) = ev → decode t data o = Except.ok (v, o + ev.size))
    (hsize : ∀ t ∈ fullTs, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdvd : ∀ t ∈ fullTs, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size)
    (hHA : fullTs.foldl (fun a t => a + headSize t) 0 < 2^256) :
    ∀ (processed ts : List ABIType) (vs : List ABIValue) (encoded : List (Bool × ByteArray))
      (tailCur maxEnd : Nat) (acc : List ABIValue),
      fullTs = processed ++ ts →
      instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encoded →
      maxEnd = offset + tailCur →
      tailCur + (tupleTails encoded).size < 2^256 →
      data.extract (offset + processed.foldl (fun a t => a + headSize t) 0)
        (offset + processed.foldl (fun a t => a + headSize t) 0 + ((tupleHeadsFrom tailCur encoded).foldl (·++·) ByteArray.empty).size)
        = (tupleHeadsFrom tailCur encoded).foldl (·++·) ByteArray.empty →
      data.extract (offset + tailCur) (offset + tailCur + (tupleTails encoded).size) = tupleTails encoded →
      decodeTupleDynamic (foldAll DecoderEntry ts) fullTs ts data offset processed.length acc maxEnd
        = Except.ok (acc.reverse ++ vs, offset + tailCur + (tupleTails encoded).size) := by
  intro processed ts
  induction ts generalizing processed with
  | nil =>
    intro vs encoded tailCur maxEnd acc hsplit hgo hmax _ _ _
    simp only [foldAll] at hgo ⊢
    cases vs with
    | nil =>
      rw [show encoded = [] from (Except.ok.inj (show Except.ok [] = Except.ok encoded from hgo)).symm]
      simp only [tupleTails, ByteArray.size_empty, Nat.add_zero, List.append_nil]
      rw [dtd_nil, hmax]
    | cons v vs => exact absurd (show Except.error Error.typeValueMismatch = Except.ok encoded from hgo) (by simp)
  | cons t ts' ih =>
    intro vs encoded tailCur maxEnd acc hsplit hgo hmax htbound hheads htails
    have hmemt : t ∈ fullTs := by rw [hsplit]; simp
    simp only [foldAll] at hgo
    rcases hentry : foldABIType EncoderEntry t with ⟨dyn, enc⟩
    rw [hentry] at hgo
    obtain ⟨v, vs', b, tail, rfl, hb, htail, rfl⟩ := go_cons_ok dyn enc (foldAll EncoderEntry ts') vs encoded hgo
    have henc_t : enc = encode t := by unfold encode; rw [hentry]
    have hdyneq : dyn = isDynamic t := by have := enc_fst_eq_isDynamic t; rw [hentry] at this; simp only [] at this; exact this
    have hb_enc : encode t v = Except.ok b := by rw [← henc_t]; exact hb
    -- head offset
    have hhp : (fullTs.take processed.length).foldl (fun acc t => acc + headSize t) 0 = processed.foldl (fun acc t => acc + headSize t) 0 := by
      rw [hsplit, List.take_left]
    have hhp_le : processed.foldl (fun a t => a + headSize t) 0 ≤ fullTs.foldl (fun a t => a + headSize t) 0 := by
      rw [hsplit]; exact foldl_append_ge processed (t :: ts')
    rw [foldAll]
    rw [dtd_cons]
    simp only [hhp]
    have hheadle : ¬ (offset + processed.foldl (fun a t => a + headSize t) 0 + 32 > data.size) := by omega
    rw [if_neg hheadle]
    set hp := processed.foldl (fun a t => a + headSize t) 0 with hpdef
    have hlen1 : processed.length + 1 = (processed ++ [t]).length := by simp
    have hpsnoc : (processed ++ [t]).foldl (fun a t => a + headSize t) 0 = hp + headSize t := by rw [hpdef]; exact foldl_snoc processed t
    have hsplit' : fullTs = (processed ++ [t]) ++ ts' := by rw [hsplit]; simp
    cases hd : isDynamic t with
    | false =>
      have hdynf : dyn = false := hdyneq.trans hd
      subst hdynf
      rw [tupleHeadsFrom_stat, ba_foldl_cons] at hheads
      have hbeq : b.size = headSize t := hsize t hmemt hd v b hb_enc
      have hb_lt : b.size < 2^256 := by have := headSize_mem_le fullTs t hmemt; omega
      set P := (tupleHeadsFrom tailCur tail).foldl (·++·) ByteArray.empty with hPdef
      have hchunk : data.extract (offset + hp) (offset + hp + b.size) = b := by
        have e0 : (data.extract (offset + hp) (offset + hp + (b ++ P).size)).extract 0 b.size = data.extract (offset + hp) (offset + hp + b.size) := by
          rw [ByteArray.extract_extract, Nat.add_zero, show min (offset + hp + b.size) (offset + hp + (b ++ P).size) = offset + hp + b.size from by rw [ByteArray.size_append]; omega]
        rw [← e0, hheads, ByteArray.extract_append_eq_left rfl]
      have hslice_suffix : data.extract (offset + hp + b.size) (offset + hp + b.size + P.size) = P := by
        have e0 : (data.extract (offset + hp) (offset + hp + (b ++ P).size)).extract b.size (b.size + P.size) = data.extract (offset + hp + b.size) (offset + hp + b.size + P.size) := by
          rw [ByteArray.extract_extract, show min (offset + hp + (b.size + P.size)) (offset + hp + (b ++ P).size) = offset + hp + b.size + P.size from by rw [ByteArray.size_append]; omega]
        rw [← e0, hheads]; exact ByteArray.extract_append_eq_right rfl rfl
      have hdec : (foldABIType DecoderEntry t) data (offset + hp) = Except.ok (v, offset + hp + b.size) := hrt t hmemt v b _ hb_lt hb_enc hchunk
      rw [hdec]
      show decodeTupleDynamic (foldAll DecoderEntry ts') fullTs ts' data offset (processed.length + 1) (v :: acc) maxEnd = _
      rw [hlen1]
      have hheads' : data.extract (offset + (processed ++ [t]).foldl (fun a t => a + headSize t) 0) (offset + (processed ++ [t]).foldl (fun a t => a + headSize t) 0 + P.size) = P := by
        rw [show offset + (processed ++ [t]).foldl (fun a t => a + headSize t) 0 = offset + hp + b.size from by rw [hpsnoc]; omega]; exact hslice_suffix
      have htails' : data.extract (offset + tailCur) (offset + tailCur + (tupleTails tail).size) = tupleTails tail := by rw [← tupleTails_stat b]; exact htails
      rw [ih (processed ++ [t]) vs' tail tailCur maxEnd (v :: acc) hsplit' htail hmax (by rw [tupleTails_stat] at htbound; exact htbound) hheads' htails']
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append, tupleTails_stat]
    | true =>
      have hdynt : dyn = true := hdyneq.trans hd
      subst hdynt
      rw [tupleTails_dyn] at htails htbound
      have htc_lt : tailCur < 2^256 := by rw [ByteArray.size_append] at htbound; omega
      have hb_lt : b.size < 2^256 := by rw [ByteArray.size_append] at htbound; omega
      have hru : roundUp32 b.size = b.size := roundUp32_eq_of_dvd b.size (hdvd t hmemt v b hb_lt hb_enc)
      have hP32 : (uint256ToBytes tailCur).size = 32 := uint256ToBytes_size32 tailCur htc_lt
      rw [tupleHeadsFrom_dyn, hru, ba_foldl_cons] at hheads
      set P := (tupleHeadsFrom (tailCur + b.size) tail).foldl (·++·) ByteArray.empty with hPdef
      have hchunk : data.extract (offset + hp) (offset + hp + 32) = uint256ToBytes tailCur := by
        have e0 : (data.extract (offset + hp) (offset + hp + (uint256ToBytes tailCur ++ P).size)).extract 0 32 = data.extract (offset + hp) (offset + hp + 32) := by
          rw [ByteArray.extract_extract, Nat.add_zero, show min (offset + hp + 32) (offset + hp + (uint256ToBytes tailCur ++ P).size) = offset + hp + 32 from by rw [ByteArray.size_append, hP32]; omega]
        rw [← e0, hheads, ← hP32]; exact ByteArray.extract_append_eq_left rfl
      have htchunk : data.extract (offset + tailCur) (offset + tailCur + b.size) = b := by
        have e0 : (data.extract (offset + tailCur) (offset + tailCur + (b ++ tupleTails tail).size)).extract 0 b.size = data.extract (offset + tailCur) (offset + tailCur + b.size) := by
          rw [ByteArray.extract_extract, Nat.add_zero, show min (offset + tailCur + b.size) (offset + tailCur + (b ++ tupleTails tail).size) = offset + tailCur + b.size from by rw [ByteArray.size_append]; omega]
        rw [← e0, htails, ByteArray.extract_append_eq_left rfl]
      have hslice_suffix : data.extract (offset + hp + 32) (offset + hp + 32 + P.size) = P := by
        have e0 : (data.extract (offset + hp) (offset + hp + (uint256ToBytes tailCur ++ P).size)).extract 32 (32 + P.size) = data.extract (offset + hp + 32) (offset + hp + 32 + P.size) := by
          rw [ByteArray.extract_extract, show min (offset + hp + (32 + P.size)) (offset + hp + (uint256ToBytes tailCur ++ P).size) = offset + hp + 32 + P.size from by rw [ByteArray.size_append, hP32]; omega]
        rw [← e0, hheads]; exact ByteArray.extract_append_eq_right hP32.symm (by rw [hP32])
      have htslice_suffix : data.extract (offset + (tailCur + b.size)) (offset + (tailCur + b.size) + (tupleTails tail).size) = tupleTails tail := by
        have e0 : (data.extract (offset + tailCur) (offset + tailCur + (b ++ tupleTails tail).size)).extract b.size (b.size + (tupleTails tail).size) = data.extract (offset + tailCur + b.size) (offset + tailCur + b.size + (tupleTails tail).size) := by
          rw [ByteArray.extract_extract, show min (offset + tailCur + (b.size + (tupleTails tail).size)) (offset + tailCur + (b ++ tupleTails tail).size) = offset + tailCur + b.size + (tupleTails tail).size from by rw [ByteArray.size_append]; omega]
        rw [show offset + (tailCur + b.size) = offset + tailCur + b.size from by omega, ← e0, htails]
        exact ByteArray.extract_append_eq_right rfl rfl
      rw [hchunk, bytesToNat_uint256ToBytes]
      have hdec : (foldABIType DecoderEntry t) data (offset + tailCur) = Except.ok (v, offset + tailCur + b.size) := hrt t hmemt v b _ hb_lt hb_enc htchunk
      rw [hdec]
      show decodeTupleDynamic (foldAll DecoderEntry ts') fullTs ts' data offset (processed.length + 1) (v :: acc) (max maxEnd (offset + tailCur + b.size)) = _
      rw [hlen1, show max maxEnd (offset + tailCur + b.size) = offset + (tailCur + b.size) from by rw [hmax]; omega]
      have hheads' : data.extract (offset + (processed ++ [t]).foldl (fun a t => a + headSize t) 0) (offset + (processed ++ [t]).foldl (fun a t => a + headSize t) 0 + P.size) = P := by
        rw [show offset + (processed ++ [t]).foldl (fun a t => a + headSize t) 0 = offset + hp + 32 from by rw [hpsnoc]; have := headSize_dynamic t hd; omega]; exact hslice_suffix
      rw [ih (processed ++ [t]) vs' tail (tailCur + b.size) (offset + (tailCur + b.size)) (v :: acc) hsplit' htail rfl (by rw [ByteArray.size_append] at htbound; omega) hheads' htslice_suffix]
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append, tupleTails_dyn, ByteArray.size_append]
      rw [show offset + (tailCur + b.size) + (tupleTails tail).size = offset + tailCur + (b.size + (tupleTails tail).size) from by omega]

/-! ### Dynamic tuple roundtrip under the well-formedness bound `enc.size < 2 ^ 256` -/

theorem tupleHeadsFrom_size (ts : List ABIType)
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdvd : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size) :
    ∀ (vs : List ABIValue) (encoded : List (Bool × ByteArray)) (off : Nat),
      instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encoded →
      off + (tupleTails encoded).size < 2^256 →
      ((tupleHeadsFrom off encoded).foldl (·++·) ByteArray.empty).size = ts.foldl (fun a t => a + headSize t) 0 := by
  induction ts with
  | nil =>
    intro vs encoded off hgo _
    simp only [foldAll] at hgo
    cases vs with
    | nil => rw [show encoded = [] from (Except.ok.inj (show Except.ok [] = Except.ok encoded from hgo)).symm]; simp [tupleHeadsFrom]
    | cons v vs => exact absurd (show Except.error Error.typeValueMismatch = Except.ok encoded from hgo) (by simp)
  | cons t ts' ih =>
    intro vs encoded off hgo hbnd
    have hmemt : t ∈ (t :: ts') := by simp
    simp only [foldAll] at hgo
    rcases hentry : foldABIType EncoderEntry t with ⟨dyn, enc⟩
    rw [hentry] at hgo
    obtain ⟨v, vs', b, tail, rfl, hb, htail, rfl⟩ := go_cons_ok dyn enc (foldAll EncoderEntry ts') vs encoded hgo
    have henc_t : enc = encode t := by unfold encode; rw [hentry]
    have hb_enc : encode t v = Except.ok b := by rw [← henc_t]; exact hb
    have hdyneq : dyn = isDynamic t := by have := enc_fst_eq_isDynamic t; rw [hentry] at this; simp only [] at this; exact this
    have ihs : ∀ t' ∈ ts', isDynamic t' = false → ∀ (v : ABIValue) (ev : ByteArray), encode t' v = Except.ok ev → ev.size = headSize t' := fun t' ht' => hsize t' (by simp [ht'])
    have ihd : ∀ t' ∈ ts', ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t' v = Except.ok ev → 32 ∣ ev.size := fun t' ht' => hdvd t' (by simp [ht'])
    cases hd : isDynamic t with
    | false =>
      have hdynf : dyn = false := hdyneq.trans hd
      subst hdynf
      have hbeq : b.size = headSize t := hsize t hmemt hd v b hb_enc
      rw [tupleHeadsFrom_stat, ba_foldl_cons, ByteArray.size_append,
          ih ihs ihd vs' tail off htail (by rw [tupleTails_stat] at hbnd; exact hbnd),
          List.foldl_cons, headSize_foldl_shift (0 + headSize t) ts']
      omega
    | true =>
      have hdynt : dyn = true := hdyneq.trans hd
      subst hdynt
      rw [tupleTails_dyn] at hbnd
      have hbnd2 : off + b.size + (tupleTails tail).size < 2^256 := by rw [ByteArray.size_append] at hbnd; omega
      have hoff_lt : off < 2^256 := by omega
      have hb_lt : b.size < 2^256 := by omega
      have hru : roundUp32 b.size = b.size := roundUp32_eq_of_dvd b.size (hdvd t hmemt v b hb_lt hb_enc)
      have hP32 : (uint256ToBytes off).size = 32 := uint256ToBytes_size32 off hoff_lt
      rw [tupleHeadsFrom_dyn, hru, ba_foldl_cons, ByteArray.size_append, hP32,
          ih ihs ihd vs' tail (off + b.size) htail (by omega),
          List.foldl_cons, headSize_foldl_shift (0 + headSize t) ts', headSize_dynamic t hd]

theorem tupleHeadsFrom_size_ge (ts : List ABIType)
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t) :
    ∀ (vs : List ABIValue) (encoded : List (Bool × ByteArray)) (off : Nat),
      instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encoded →
      ts.foldl (fun a t => a + headSize t) 0 ≤ ((tupleHeadsFrom off encoded).foldl (·++·) ByteArray.empty).size := by
  induction ts with
  | nil => intro vs encoded off hgo; simp
  | cons t ts' ih =>
    intro vs encoded off hgo
    have hmemt : t ∈ (t :: ts') := by simp
    simp only [foldAll] at hgo
    rcases hentry : foldABIType EncoderEntry t with ⟨dyn, enc⟩
    rw [hentry] at hgo
    obtain ⟨v, vs', b, tail, rfl, hb, htail, rfl⟩ := go_cons_ok dyn enc (foldAll EncoderEntry ts') vs encoded hgo
    have henc_t : enc = encode t := by unfold encode; rw [hentry]
    have hb_enc : encode t v = Except.ok b := by rw [← henc_t]; exact hb
    have hdyneq : dyn = isDynamic t := by have := enc_fst_eq_isDynamic t; rw [hentry] at this; simp only [] at this; exact this
    have ihs : ∀ t' ∈ ts', isDynamic t' = false → ∀ (v : ABIValue) (ev : ByteArray), encode t' v = Except.ok ev → ev.size = headSize t' := fun t' ht' => hsize t' (by simp [ht'])
    rw [List.foldl_cons, headSize_foldl_shift (0 + headSize t) ts']
    cases hd : isDynamic t with
    | false =>
      have hdynf : dyn = false := hdyneq.trans hd
      subst hdynf
      have hbeq : b.size = headSize t := hsize t hmemt hd v b hb_enc
      rw [tupleHeadsFrom_stat, ba_foldl_cons, ByteArray.size_append]
      have := ih ihs vs' tail off htail; omega
    | true =>
      have hdynt : dyn = true := hdyneq.trans hd
      subst hdynt
      rw [tupleHeadsFrom_dyn, ba_foldl_cons, ByteArray.size_append]
      have hge := uint256ToBytes_size_ge off
      have := ih ihs vs' tail (off + roundUp32 b.size) htail
      have h32 : headSize t = 32 := headSize_dynamic t hd
      omega


theorem roundtrip_tuple_dyn_wf (ts : List ABIType) (data : ByteArray)
    (hrt : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 →
      encode t v = Except.ok ev → data.extract o (o + ev.size) = ev → decode t data o = Except.ok (v, o + ev.size))
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdvd : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size)
    (hdyn : ts.any isDynamic = true)
    (v : ABIValue) (enc : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256)
    (hbd : off + ts.foldl (fun a t => a + headSize t) 0 + 32 ≤ data.size)
    (henc : encode (.tuple ts) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.tuple ts) data off = Except.ok (v, off + enc.size) := by
  cases v with
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | array _ => badVal henc
  | tuple vs =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    cases hgo : instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs with
    | error x => rw [hgo] at henc; exact absurd (show Except.error x = Except.ok enc from henc) (by simp)
    | ok encd =>
      rw [hgo] at henc
      have hpack : enc = tuplePack (ts.map headSize) (ts.map isDynamic) encd :=
        (Except.ok.inj (show Except.ok (tuplePack (ts.map headSize) (ts.map isDynamic) encd) = Except.ok enc from henc)).symm
      have hany : (ts.map isDynamic).any id = true := by simpa using hdyn
      set HA := ts.foldl (fun a t => a + headSize t) 0 with hHAdef
      have hHAeq : (ts.map headSize).foldl (· + ·) 0 = HA := by rw [hHAdef, List.foldl_map]
      set heads := (tupleHeadsFrom HA encd).foldl (·++·) ByteArray.empty with hh
      set tails := tupleTails encd with ht
      have hpackht : enc = heads ++ tails := by rw [hpack, tuplePack_dyn _ _ _ hany, hHAeq]
      have hpsz : enc.size = heads.size + tails.size := by rw [hpackht, ByteArray.size_append]
      have hge : HA ≤ heads.size := by rw [hh]; exact tupleHeadsFrom_size_ge ts hsize vs encd HA hgo
      have htb : HA + tails.size < 2^256 := by omega
      have hheadsz : heads.size = HA := by rw [hh]; exact tupleHeadsFrom_size ts hsize hdvd vs encd HA hgo (by rw [← ht]; omega)
      -- slices
      have hslice_heads : data.extract off (off + heads.size) = heads := by
        have e0 : (data.extract off (off + (heads ++ tails).size)).extract 0 heads.size = data.extract off (off + heads.size) := by
          rw [ByteArray.extract_extract, Nat.add_zero, show min (off + heads.size) (off + (heads ++ tails).size) = off + heads.size from by rw [ByteArray.size_append]; omega]
        rw [← e0, ← hpackht, hdata, hpackht, ByteArray.extract_append_eq_left rfl]
      have hslice_tails : data.extract (off + heads.size) (off + heads.size + tails.size) = tails := by
        have e0 : (data.extract off (off + (heads ++ tails).size)).extract heads.size (heads.size + tails.size) = data.extract (off + heads.size) (off + heads.size + tails.size) := by
          rw [ByteArray.extract_extract, show min (off + (heads.size + tails.size)) (off + (heads ++ tails).size) = off + heads.size + tails.size from by rw [ByteArray.size_append]; omega]
        rw [← e0, ← hpackht, hdata, hpackht]; exact ByteArray.extract_append_eq_right rfl rfl
      have hh_heads : data.extract (off + ([] : List ABIType).foldl (fun a t => a + headSize t) 0) (off + ([] : List ABIType).foldl (fun a t => a + headSize t) 0 + ((tupleHeadsFrom HA encd).foldl (·++·) ByteArray.empty).size) = (tupleHeadsFrom HA encd).foldl (·++·) ByteArray.empty := by
        simp only [List.foldl_nil, Nat.add_zero]; rw [← hh]; exact hslice_heads
      have ht_tails : data.extract (off + HA) (off + HA + (tupleTails encd).size) = tupleTails encd := by
        rw [← ht, ← hheadsz]; exact hslice_tails
      have hdc := dtd_concat ts data off hbd hrt hsize hdvd (by omega) [] ts vs encd HA (off + HA) [] rfl hgo rfl (by rw [← ht]; omega) hh_heads ht_tails
      simp only [List.length_nil, List.reverse_nil, List.nil_append] at hdc
      unfold decode foldABIType; delta instABIVisitorDecoderEntry; dsimp
      rw [hdyn]
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      rw [show ts.foldl (fun acc t => acc + headSize t) 0 = HA from rfl, hdc]
      rw [show off + HA + (tupleTails encd).size = off + enc.size from by rw [← ht]; omega]
      rfl

/-! ### Tuple encoding is 32-byte aligned (szdvd_tuple), for composing tuples as fields/elements -/


theorem headSize_dvd_32 : (t : ABIType) → 32 ∣ headSize t
  | .uint _ => by simp [headSize, isDynamic]
  | .int _ => by simp [headSize, isDynamic]
  | .bool => by simp [headSize, isDynamic]
  | .address => by simp [headSize, isDynamic]
  | .bytes => by simp [headSize, isDynamic]
  | .fixedBytes _ => by simp [headSize, isDynamic]
  | .string => by simp [headSize, isDynamic]
  | .array _ => by simp [headSize, isDynamic]
  | .fixedArray n e => by
      rw [headSize]; split
      · simp
      · exact (headSize_dvd_32 e).mul_left n
  | .tuple [] => by simp [headSize, isDynamic]
  | .tuple (t' :: ts) => by
      rw [headSize]; split
      · simp
      · exact Nat.dvd_add (headSize_dvd_32 t') (headSize_dvd_32 (.tuple ts))
  termination_by t => sizeOf t

theorem foldl_headSize_dvd : ∀ (ts : List ABIType) (init : Nat), 32 ∣ init →
    32 ∣ ts.foldl (fun a t => a + headSize t) init
  | [], init, h => h
  | t :: ts, init, h => by
      rw [List.foldl_cons]; exact foldl_headSize_dvd ts (init + headSize t) (Nat.dvd_add h (headSize_dvd_32 t))

theorem concat_pairs_dvd : ∀ (encd : List (Bool × ByteArray)), (∀ b ∈ encd, 32 ∣ b.2.size) →
    32 ∣ (encd.foldl (fun acc x => acc ++ x.2) ByteArray.empty).size := by
  intro encd
  suffices h : ∀ (acc : ByteArray), 32 ∣ acc.size → (∀ b ∈ encd, 32 ∣ b.2.size) →
      32 ∣ (encd.foldl (fun acc x => acc ++ x.2) acc).size by
    intro hall; exact h ByteArray.empty (by simp) hall
  induction encd with
  | nil => intro acc hacc _; exact hacc
  | cons x xs ih =>
    intro acc hacc hall
    rw [List.foldl_cons]
    exact ih (acc ++ x.2) (by rw [ByteArray.size_append]; exact Nat.dvd_add hacc (hall x (by simp)))
      (fun b hb => hall b (List.mem_cons_of_mem _ hb))

theorem tupleTails_size_dvd : ∀ (encd : List (Bool × ByteArray)), (∀ b ∈ encd, b.1 = true → 32 ∣ b.2.size) →
    32 ∣ (tupleTails encd).size := by
  intro encd
  induction encd with
  | nil => intro _; simp [tupleTails]
  | cons x xs ih =>
    intro hall
    obtain ⟨isDyn, enc⟩ := x
    rw [tupleTails, ByteArray.size_append]
    refine Nat.dvd_add ?_ (ih (fun b hb => hall b (List.mem_cons_of_mem _ hb)))
    cases isDyn with
    | true => simpa using hall (true, enc) (by simp) rfl
    | false => simp

theorem tupleTails_mem_le : ∀ (encd : List (Bool × ByteArray)) (b : Bool × ByteArray),
    b ∈ encd → b.1 = true → b.2.size ≤ (tupleTails encd).size := by
  intro encd
  induction encd with
  | nil => intro b hb _; simp at hb
  | cons x xs ih =>
    obtain ⟨d, e⟩ := x
    intro b hb hdyn
    rw [tupleTails, ByteArray.size_append]
    rcases List.mem_cons.mp hb with h | h
    · subst h
      have hd : d = true := hdyn
      rw [hd]; simp only [if_true]; omega
    · exact le_trans (ih b h hdyn) (by omega)

-- static tuple: every encoded field is 32-aligned (size = headSize, structurally divisible)
theorem tuple_entries_static_dvd (ts : List ABIType)
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t) :
    ∀ (vs : List ABIValue) (encd : List (Bool × ByteArray)),
      instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd →
      (∀ t ∈ ts, isDynamic t = false) → ∀ b ∈ encd, 32 ∣ b.2.size := by
  induction ts with
  | nil =>
    intro vs encd hgo _ b hb
    simp only [foldAll] at hgo
    cases vs with
    | nil => rw [show encd = [] from (Except.ok.inj (show Except.ok [] = Except.ok encd from hgo)).symm] at hb; simp at hb
    | cons v vs => exact absurd (show Except.error Error.typeValueMismatch = Except.ok encd from hgo) (by simp)
  | cons t ts' ih =>
    intro vs encd hgo hstat b hb
    have hmemt : t ∈ (t :: ts') := by simp
    simp only [foldAll] at hgo
    rcases hentry : foldABIType EncoderEntry t with ⟨dyn, enc⟩
    rw [hentry] at hgo
    obtain ⟨v, vs', b0, tail, rfl, hb0, htail, rfl⟩ := go_cons_ok dyn enc (foldAll EncoderEntry ts') vs encd hgo
    have henc_t : enc = encode t := by unfold encode; rw [hentry]
    have hb_enc : encode t v = Except.ok b0 := by rw [← henc_t]; exact hb0
    have hstat_t : isDynamic t = false := hstat t hmemt
    have hb0sz : b0.size = headSize t := hsize t hmemt hstat_t v b0 hb_enc
    rcases List.mem_cons.mp hb with h | h
    · subst h; rw [hb0sz]; exact headSize_dvd_32 t
    · exact ih (fun t' ht' => hsize t' (by simp [ht'])) vs' tail htail (fun t' ht' => hstat t' (by simp [ht'])) b h

-- dynamic tuple: every dynamic encoded field is 32-aligned (via hdvd, under size bound)
theorem tuple_entries_dyn_dvd (ts : List ABIType)
    (hdvd : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size) :
    ∀ (vs : List ABIValue) (encd : List (Bool × ByteArray)),
      instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd →
      (∀ b ∈ encd, b.1 = true → b.2.size < 2^256) → ∀ b ∈ encd, b.1 = true → 32 ∣ b.2.size := by
  induction ts with
  | nil =>
    intro vs encd hgo _ b hb
    simp only [foldAll] at hgo
    cases vs with
    | nil => rw [show encd = [] from (Except.ok.inj (show Except.ok [] = Except.ok encd from hgo)).symm] at hb; simp at hb
    | cons v vs => exact absurd (show Except.error Error.typeValueMismatch = Except.ok encd from hgo) (by simp)
  | cons t ts' ih =>
    intro vs encd hgo hbnd b hb hdynb
    have hmemt : t ∈ (t :: ts') := by simp
    simp only [foldAll] at hgo
    rcases hentry : foldABIType EncoderEntry t with ⟨dyn, enc⟩
    rw [hentry] at hgo
    obtain ⟨v, vs', b0, tail, rfl, hb0, htail, rfl⟩ := go_cons_ok dyn enc (foldAll EncoderEntry ts') vs encd hgo
    have henc_t : enc = encode t := by unfold encode; rw [hentry]
    have hb_enc : encode t v = Except.ok b0 := by rw [← henc_t]; exact hb0
    rcases List.mem_cons.mp hb with h | h
    · subst h
      exact hdvd t hmemt v b0 (hbnd (dyn, b0) (by simp) hdynb) hb_enc
    · exact ih (fun t' ht' => hdvd t' (by simp [ht'])) vs' tail htail
        (fun b' hb' => hbnd b' (List.mem_cons_of_mem _ hb')) b h hdynb

-- 32-alignment of any tuple encoding, under the well-formedness bound
theorem szdvd_tuple (ts : List ABIType)
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdvd : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size)
    (v : ABIValue) (ev : ByteArray) (hsz : ev.size < 2^256) (henc : encode (.tuple ts) v = Except.ok ev) :
    32 ∣ ev.size := by
  cases v with
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | array _ => badVal henc
  | tuple vs =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    cases hgo : instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs with
    | error x => rw [hgo] at henc; exact absurd (show Except.error x = Except.ok ev from henc) (by simp)
    | ok encd =>
      rw [hgo] at henc
      have hpack : ev = tuplePack (ts.map headSize) (ts.map isDynamic) encd :=
        (Except.ok.inj (show Except.ok (tuplePack (ts.map headSize) (ts.map isDynamic) encd) = Except.ok ev from henc)).symm
      cases hdynb : (ts.map isDynamic).any id with
      | false =>
        rw [hpack, tuplePack_static _ _ _ hdynb]
        have hallstat : ∀ t ∈ ts, isDynamic t = false := by
          intro t ht
          rcases hb : isDynamic t with _ | _
          · rfl
          · exfalso
            have : (ts.map isDynamic).any id = true :=
              List.any_eq_true.mpr ⟨isDynamic t, List.mem_map_of_mem ht, by simpa using hb⟩
            rw [hdynb] at this; exact absurd this (by simp)
        exact concat_pairs_dvd encd (tuple_entries_static_dvd ts hsize vs encd hgo hallstat)
      | true =>
        have hHAeq : (ts.map headSize).foldl (· + ·) 0 = ts.foldl (fun a t => a + headSize t) 0 := by
          rw [List.foldl_map]
        have hpackht : ev = (tupleHeadsFrom (ts.foldl (fun a t => a + headSize t) 0) encd).foldl (·++·) ByteArray.empty ++ tupleTails encd := by
          rw [hpack, tuplePack_dyn _ _ _ hdynb, hHAeq]
        have hpsz : ev.size = ((tupleHeadsFrom (ts.foldl (fun a t => a + headSize t) 0) encd).foldl (·++·) ByteArray.empty).size + (tupleTails encd).size := by
          rw [hpackht, ByteArray.size_append]
        have hge : ts.foldl (fun a t => a + headSize t) 0 ≤ ((tupleHeadsFrom (ts.foldl (fun a t => a + headSize t) 0) encd).foldl (·++·) ByteArray.empty).size :=
          tupleHeadsFrom_size_ge ts hsize vs encd _ hgo
        have hheadsz : ((tupleHeadsFrom (ts.foldl (fun a t => a + headSize t) 0) encd).foldl (·++·) ByteArray.empty).size = ts.foldl (fun a t => a + headSize t) 0 :=
          tupleHeadsFrom_size ts hsize hdvd vs encd _ hgo (by omega)
        have hbnd_dyn : ∀ b ∈ encd, b.1 = true → b.2.size < 2^256 := by
          intro b hb hd
          have := tupleTails_mem_le encd b hb hd
          omega
        have htails : 32 ∣ (tupleTails encd).size :=
          tupleTails_size_dvd encd (tuple_entries_dyn_dvd ts hdvd vs encd hgo hbnd_dyn)
        have hheads : 32 ∣ ((tupleHeadsFrom (ts.foldl (fun a t => a + headSize t) 0) encd).foldl (·++·) ByteArray.empty).size := by
          rw [hheadsz]; exact foldl_headSize_dvd ts 0 (by simp)
        rw [hpsz]; exact Nat.dvd_add hheads htails

/-! ### Unified tuple roundtrip under WF (static + dynamic dispatch) -/


theorem decodeTupleStatic_concat_wf (ts : List ABIType) (data : ByteArray)
    (hrt : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 →
      encode t v = Except.ok ev → data.extract o (o + ev.size) = ev → decode t data o = Except.ok (v, o + ev.size)) :
    ∀ (vs : List ABIValue) (encd : List (Bool × ByteArray)) (off : Nat) (acc : List ABIValue),
    instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd →
    (encd.foldl (fun a x => a ++ x.2) ByteArray.empty).size < 2^256 →
    data.extract off (off + (encd.foldl (fun a x => a ++ x.2) ByteArray.empty).size) = encd.foldl (fun a x => a ++ x.2) ByteArray.empty →
    decodeTupleStatic (foldAll DecoderEntry ts) data off acc = Except.ok (acc.reverse ++ vs, off + (encd.foldl (fun a x => a ++ x.2) ByteArray.empty).size) := by
  induction ts with
  | nil =>
    intro vs encd off acc hgo _ hslice
    simp only [foldAll] at hgo ⊢
    cases vs with
    | nil =>
      rw [show encd = [] from (Except.ok.inj (show Except.ok [] = Except.ok encd from hgo)).symm]
      simp only [List.foldl_nil, ByteArray.size_empty, Nat.add_zero, List.append_nil]
      rw [decodeTupleStatic_nil]
    | cons v vs => exact absurd (show Except.error Error.typeValueMismatch = Except.ok encd from hgo) (by simp)
  | cons t ts' ih =>
    intro vs encd off acc hgo hbound hslice
    have hmemt : t ∈ (t :: ts') := by simp
    simp only [foldAll] at hgo
    rcases hentry : foldABIType EncoderEntry t with ⟨dyn, enc⟩
    rw [hentry] at hgo
    obtain ⟨v, vs', b, tail, rfl, hb, htail, rfl⟩ := go_cons_ok dyn enc (foldAll EncoderEntry ts') vs encd hgo
    have henc_t : enc = encode t := by unfold encode; rw [hentry]
    rw [ba_foldl_snd_cons] at hslice hbound ⊢
    simp only [] at hslice hbound ⊢
    have hsz : (b ++ tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size = b.size + (tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size := ByteArray.size_append
    have hb_lt : b.size < 2^256 := by rw [hsz] at hbound; omega
    have hbound' : (tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size < 2^256 := by rw [hsz] at hbound; omega
    have hm1 : min (off + b.size) (off + (b ++ tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size) = off + b.size := by rw [hsz]; omega
    have hm2 : min (off + (b.size + (tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size)) (off + (b ++ tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size) = off + b.size + (tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size := by rw [hsz]; omega
    have hslice_b : data.extract off (off + b.size) = b := by
      have e0 : (data.extract off (off + (b ++ tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size)).extract 0 b.size = data.extract off (off + b.size) := by
        rw [ByteArray.extract_extract, Nat.add_zero, hm1]
      rw [← e0, hslice, ByteArray.extract_append_eq_left rfl]
    have hslice_tail : data.extract (off + b.size) (off + b.size + (tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size) = tail.foldl (fun a x => a ++ x.2) ByteArray.empty := by
      have e0 : (data.extract off (off + (b ++ tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size)).extract b.size (b.size + (tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size) = data.extract (off + b.size) (off + b.size + (tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size) := by
        rw [ByteArray.extract_extract, hm2]
      rw [← e0, hslice]; exact ByteArray.extract_append_eq_right rfl rfl
    have hdec_t : (foldABIType DecoderEntry t) data off = Except.ok (v, off + b.size) :=
      hrt t hmemt v b off hb_lt (by rw [← henc_t]; exact hb) hslice_b
    simp only [foldAll]
    rw [decodeTupleStatic_cons, hdec_t]
    show decodeTupleStatic (foldAll DecoderEntry ts') data (off + b.size) (v :: acc) = _
    rw [ih (fun t' ht' => hrt t' (List.mem_cons_of_mem t ht')) vs' tail (off + b.size) (v :: acc) htail hbound' hslice_tail]
    simp [add_assoc]

-- static-tuple concat size = headSize (.tuple ts), from per-field size_eq (WF variant, no visitor)
theorem tuplePackStatic_size_wf (ts : List ABIType)
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hstat : ∀ t ∈ ts, isDynamic t = false) :
    ∀ (vs : List ABIValue) (encd : List (Bool × ByteArray)),
    instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd →
    (encd.foldl (fun acc x => acc ++ x.2) ByteArray.empty).size = headSize (.tuple ts) := by
  induction ts with
  | nil =>
    intro vs encd hgo
    simp only [foldAll] at hgo
    cases vs with
    | nil => rw [show encd = [] from (Except.ok.inj (show Except.ok [] = Except.ok encd from hgo)).symm]; simp [headSize, isDynamic]
    | cons v vs => exact absurd (show Except.error Error.typeValueMismatch = Except.ok encd from hgo) (by simp)
  | cons t ts' ih =>
    intro vs encd hgo
    have hmemt : t ∈ (t :: ts') := by simp
    simp only [foldAll] at hgo
    rcases hentry : foldABIType EncoderEntry t with ⟨dyn, enc⟩
    rw [hentry] at hgo
    obtain ⟨v, vs', b, tail, rfl, hb, htail, rfl⟩ := go_cons_ok dyn enc (foldAll EncoderEntry ts') vs encd hgo
    have henc_t : enc = encode t := by unfold encode; rw [hentry]
    have hbsz : b.size = headSize t := hsize t hmemt (hstat t hmemt) v b (by rw [← henc_t]; exact hb)
    rw [ba_foldl_snd_cons, ByteArray.size_append, hbsz,
        ih (fun t' ht' => hsize t' (by simp [ht'])) (fun t' ht' => hstat t' (List.mem_cons_of_mem t ht')) vs' tail htail,
        headSize_tuple_cons t ts' (isDynamic_tuple_of_all_static (t :: ts') hstat)]

-- static tuple roundtrip under WF (per-field bounded rt + size_eq)
theorem roundtrip_tuple_stat_wf (ts : List ABIType) (data : ByteArray)
    (hrt : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 →
      encode t v = Except.ok ev → data.extract o (o + ev.size) = ev → decode t data o = Except.ok (v, o + ev.size))
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hstat_tuple : isDynamic (.tuple ts) = false)
    (v : ABIValue) (enc : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256)
    (henc : encode (.tuple ts) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.tuple ts) data off = Except.ok (v, off + enc.size) := by
  have hany : (ts.map isDynamic).any id = false := by rw [tuple_any_isDynamic]; exact hstat_tuple
  have hany_ts : ts.any isDynamic = false := by simpa [List.any_map] using hany
  have hstat_all : ∀ t ∈ ts, isDynamic t = false := tuple_static_elems ts hstat_tuple
  cases v with
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | array _ => badVal henc
  | tuple vs =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    cases hgo : instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs with
    | error x => rw [hgo] at henc; exact absurd (show Except.error x = Except.ok enc from henc) (by simp)
    | ok encd =>
      rw [hgo] at henc
      have hpack : enc = tuplePack (ts.map headSize) (ts.map isDynamic) encd :=
        (Except.ok.inj (show Except.ok (tuplePack (ts.map headSize) (ts.map isDynamic) encd) = Except.ok enc from henc)).symm
      have hconcat : enc = encd.foldl (fun a x => a ++ x.2) ByteArray.empty := by rw [hpack, tuplePack_static _ _ _ hany]
      have hsize_eq : enc.size = headSize (.tuple ts) := by rw [hconcat]; exact tuplePackStatic_size_wf ts hsize hstat_all vs encd hgo
      have hoff : ts.foldl (fun acc t => acc + headSize t) 0 = enc.size := by rw [hsize_eq]; exact headSize_tuple_foldl ts hstat_tuple
      have hslice : data.extract off (off + (encd.foldl (fun a x => a ++ x.2) ByteArray.empty).size) = encd.foldl (fun a x => a ++ x.2) ByteArray.empty := by rw [← hconcat]; exact hdata
      unfold decode foldABIType; delta instABIVisitorDecoderEntry; dsimp
      rw [hany_ts]
      simp only [Bool.not_false, if_true]
      rw [decodeTupleStatic_concat_wf ts data hrt vs encd off [] hgo (by rw [← hconcat]; exact hwf) hslice]
      show Except.ok (ABIValue.tuple ([].reverse ++ vs), off + ts.foldl (fun acc t => acc + headSize t) 0) = Except.ok (ABIValue.tuple vs, off + enc.size)
      simp only [List.reverse_nil, List.nil_append, hoff]

-- unified tuple roundtrip under WF: dispatch static/dynamic
theorem roundtrip_tuple_wf (ts : List ABIType) (data : ByteArray)
    (hrt : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 →
      encode t v = Except.ok ev → data.extract o (o + ev.size) = ev → decode t data o = Except.ok (v, o + ev.size))
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdvd : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size)
    (v : ABIValue) (enc : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256)
    (hbd : off + ts.foldl (fun a t => a + headSize t) 0 + 32 ≤ data.size)
    (henc : encode (.tuple ts) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.tuple ts) data off = Except.ok (v, off + enc.size) := by
  cases hdyn : ts.any isDynamic with
  | true => exact roundtrip_tuple_dyn_wf ts data hrt hsize hdvd hdyn v enc off hwf hbd henc hdata
  | false =>
    have hstat_tuple : isDynamic (.tuple ts) = false := by rw [← tuple_any_isDynamic]; simpa [List.any_map] using hdyn
    exact roundtrip_tuple_stat_wf ts data hrt hsize hstat_tuple v enc off hwf henc hdata

/-! ### fixedArray encoding is 32-byte aligned (szdvd_fixedArray) -/


-- 32-alignment of a fixedArray encoding (arrayPack, no length prefix), under the bound
theorem szdvd_fixedArray (n : Nat) (e : ABIType)
    (hdvd_e : ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode e v = Except.ok ev → 32 ∣ ev.size)
    (v : ABIValue) (ev : ByteArray) (hsz : ev.size < 2^256) (henc : encode (.fixedArray n e) v = Except.ok ev) :
    32 ∣ ev.size := by
  cases v with
  | array vals =>
    unfold encode foldABIType at henc
    delta instABIVisitorEncoderEntry at henc
    rcases hentry : foldABIType EncoderEntry e with ⟨elemDyn, elemEnc⟩
    rw [hentry] at henc; dsimp at henc
    have helem : elemEnc = encode e := by unfold encode; rw [hentry]
    split at henc
    · exact absurd (show Except.error (Error.arrayElemCount n vals.length) = Except.ok ev from henc) (by simp)
    · cases hEL : encodeListElems elemEnc vals with
      | error x => rw [hEL] at henc; exact absurd (show Except.error x = Except.ok ev from henc) (by simp)
      | ok encd =>
        rw [hEL] at henc
        have hEL' : encodeListElems (encode e) vals = Except.ok encd := by rw [← helem]; exact hEL
        have hpack : ev = arrayPack elemDyn encd :=
          (Except.ok.inj (show Except.ok (arrayPack elemDyn encd) = Except.ok ev from henc)).symm
        have halign : ∀ b ∈ encd, 32 ∣ b.size := fun b hb => by
          obtain ⟨w, hw⟩ := encodeListElems_mem e vals encd hEL' b hb
          have hble : b.size ≤ ev.size := by
            rw [hpack]
            exact le_trans (mem_size_le_concat encd b hb) (concat_le_arrayPack elemDyn encd)
          exact hdvd_e w b (by omega) hw
        rw [hpack]
        exact arrayPack_size_dvd elemDyn encd (by rw [← hpack]; exact hsz) halign
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | tuple _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)

/-! ### ABI function-call level roundtrip: `encodeArgs` then `decodeArgs` -/

/-- The practical capstone: encoding function arguments then decoding them recovers the values.
    Reduces to the tuple roundtrip (`encodeArgs = encode (.tuple types)`,
    `decodeArgs = decode (.tuple types) >>= extract`). Carries the necessary WF preconditions
    (`data.size < 2^256` and the head-area bound the dynamic tuple decoder requires). -/
theorem roundtrip_args_wf (types : List ABIType) (data : ByteArray) (values : List ABIValue)
    (hrt : ∀ t ∈ types, ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 →
      encode t v = Except.ok ev → data.extract o (o + ev.size) = ev → decode t data o = Except.ok (v, o + ev.size))
    (hsize : ∀ t ∈ types, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdvd : ∀ t ∈ types, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size)
    (hwf : data.size < 2^256)
    (hbd : (types.foldl (fun a t => a + headSize t) 0) + 32 ≤ data.size)
    (henc : encodeArgs types values = Except.ok data) :
    decodeArgs types data 0 = Except.ok values := by
  unfold encodeArgs at henc
  split at henc
  · exact absurd henc (by simp)
  · have hrt_tuple : decode (.tuple types) data 0 = Except.ok (.tuple values, 0 + data.size) :=
      roundtrip_tuple_wf types data hrt hsize hdvd (.tuple values) data 0 hwf (by simpa using hbd) henc
        (by rw [Nat.zero_add, extract_self])
    unfold decodeArgs
    rw [hrt_tuple]
    rfl

/-! ### A clean recursive `roundtrip_wf` for tuple-free types

A fully general clean visitor is impossible: the dynamic-tuple decoder's unconditional
32-byte head-check (`Decode.lean:93`) makes a head-area bound *necessary*, and that bound
is not derivable for pathological nested tuples (e.g. a field `fixedArray 0 (array bytes)`
that encodes to 0 bytes). But over the **tuple-free** fragment (atomics, bytes, string, and
arbitrarily nested arrays / fixedArrays) everything composes with no residual bound — arrays
carry a length prefix the decoder reads within `off + enc.size`. `WFFacts` bundles the three
facts the composition needs, and `wfFacts` builds them by structural recursion. -/

/-- Types with no `tuple` anywhere in them. -/
def TupleFree : ABIType → Prop
  | .tuple _        => False
  | .array e        => TupleFree e
  | .fixedArray _ e => TupleFree e
  | _               => True

/-- The three facts a type contributes to a roundtrip composition: the offset-general
    WF roundtrip, the static size law, and 32-byte alignment. -/
structure WFFacts (t : ABIType) : Prop where
  rt : ∀ (v : ABIValue) (enc data : ByteArray) (off : Nat), enc.size < 2^256 →
    encode t v = Except.ok enc → data.extract off (off + enc.size) = enc →
    decode t data off = Except.ok (v, off + enc.size)
  size_eq : isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t
  szdvd : ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size

/-! Shared `WFFacts` component builders — the non-tuple cases, reused by both the tuple-free
    (`wfFacts`) and well-formed (`wfFactsWF`) recursions. -/

theorem WFFacts.uint (s : ByteSize) : WFFacts (.uint s) :=
  ⟨fun v enc data off _ he hd => roundtrip_off_uint s v enc data off he hd,
   fun _ v ev he => size_eq_uint s v ev he,
   fun v ev _ he => by rw [size_eq_uint s v ev he]; exact headSize_dvd_32 (.uint s)⟩
theorem WFFacts.int (s : ByteSize) : WFFacts (.int s) :=
  ⟨fun v enc data off _ he hd => roundtrip_off_int s v enc data off he hd,
   fun _ v ev he => size_eq_int s v ev he,
   fun v ev _ he => by rw [size_eq_int s v ev he]; exact headSize_dvd_32 (.int s)⟩
theorem WFFacts.bool : WFFacts .bool :=
  ⟨fun v enc data off _ he hd => roundtrip_off_bool v enc data off he hd,
   fun _ v ev he => size_eq_bool v ev he,
   fun v ev _ he => by rw [size_eq_bool v ev he]; exact headSize_dvd_32 .bool⟩
theorem WFFacts.address : WFFacts .address :=
  ⟨fun v enc data off _ he hd => roundtrip_off_address v enc data off he hd,
   fun _ v ev he => size_eq_address v ev he,
   fun v ev _ he => by rw [size_eq_address v ev he]; exact headSize_dvd_32 .address⟩
theorem WFFacts.fixedBytes (s : ByteSize) : WFFacts (.fixedBytes s) :=
  ⟨fun v enc data off _ he hd => roundtrip_off_fixedBytes s v enc data off he hd,
   fun _ v ev he => size_eq_fixedBytes s v ev he,
   fun v ev _ he => by rw [size_eq_fixedBytes s v ev he]; exact headSize_dvd_32 (.fixedBytes s)⟩
theorem WFFacts.bytes : WFFacts .bytes :=
  ⟨fun v enc data off _ he hd => roundtrip_off_bytes v enc data off he hd,
   fun h => absurd h (by simp [isDynamic]), szdvd_bytes⟩
theorem WFFacts.string : WFFacts .string :=
  ⟨fun v enc data off _ he hd => roundtrip_off_string v enc data off he hd,
   fun h => absurd h (by simp [isDynamic]), szdvd_string⟩
theorem WFFacts.array (e : ABIType) (ih : WFFacts e) : WFFacts (.array e) :=
  ⟨fun v enc data off hwf he hd =>
      roundtrip_array_wf e data (fun v' ev' o' hlt he' hd' => ih.rt v' ev' data o' hlt he' hd') ih.szdvd v enc off hwf he hd,
   fun h => absurd h (by simp [isDynamic]),
   fun v ev hwf he => szdvd_array e ih.szdvd v ev hwf he⟩
theorem WFFacts.fixedArray (n : Nat) (e : ABIType) (ih : WFFacts e) : WFFacts (.fixedArray n e) :=
  ⟨fun v enc data off hwf he hd =>
      roundtrip_fixedArray_wf n e data (fun v' ev' o' hlt he' hd' => ih.rt v' ev' data o' hlt he' hd') ih.szdvd v enc off hwf he hd,
   fun hstat v ev he => by
      have hstat_e : isDynamic e = false := by simpa [isDynamic] using hstat
      exact size_eq_fixedArray_core n e (ih.size_eq hstat_e) hstat_e v ev he,
   fun v ev hwf he => szdvd_fixedArray n e ih.szdvd v ev hwf he⟩

theorem wfFacts : (t : ABIType) → TupleFree t → WFFacts t
  | .uint s, _ => .uint s
  | .int s, _ => .int s
  | .bool, _ => .bool
  | .address, _ => .address
  | .fixedBytes s, _ => .fixedBytes s
  | .bytes, _ => .bytes
  | .string, _ => .string
  | .array e, htf => .array e (wfFacts e htf)
  | .fixedArray n e, htf => .fixedArray n e (wfFacts e htf)
  | .tuple _, htf => by simp [TupleFree] at htf
  termination_by t => sizeOf t

/-- Clean roundtrip (offset 0) for any tuple-free type, with no residual head-area bound. -/
theorem roundtrip_wf_tupleFree (t : ABIType) (htf : TupleFree t) (v : ABIValue) (data : ByteArray)
    (hwf : data.size < 2^256) (henc : encode t v = Except.ok data) :
    decode t data 0 = Except.ok (v, data.size) := by
  have h := (wfFacts t htf).rt v data data 0 hwf henc (by rw [Nat.zero_add, extract_self])
  simpa using h

/-- Function-call roundtrip for any tuple-free argument list — no per-signature proof needed. -/
theorem roundtrip_args_tupleFree_wf (types : List ABIType) (data : ByteArray) (values : List ABIValue)
    (htf : ∀ t ∈ types, TupleFree t)
    (hwf : data.size < 2^256)
    (hbd : (types.foldl (fun a t => a + headSize t) 0) + 32 ≤ data.size)
    (henc : encodeArgs types values = Except.ok data) :
    decodeArgs types data 0 = Except.ok values :=
  roundtrip_args_wf types data values
    (fun t ht v ev o hlt he hd => (wfFacts t (htf t ht)).rt v ev data o hlt he hd)
    (fun t ht => (wfFacts t (htf t ht)).size_eq)
    (fun t ht => (wfFacts t (htf t ht)).szdvd)
    hwf hbd henc

/-! ### Covering nested tuples (structs): the well-formed fragment

Excludes only the one pathology — an empty fixed-array of a dynamic element type
(`fixedArray 0 e`, `e` dynamic), which encodes to 0 bytes and genuinely fails to decode.
Over well-formed types every dynamic encoding is >= 32 bytes, so the dynamic tuple
decoder's head-area bound is derivable and tuples compose inside containers. -/


-- "no empty fixed-array of a dynamic element type, anywhere" (excludes the one pathology)
inductive WellFormedType : ABIType → Prop
  | uint (s : ByteSize) : WellFormedType (.uint s)
  | int (s : ByteSize) : WellFormedType (.int s)
  | bool : WellFormedType .bool
  | address : WellFormedType .address
  | bytes : WellFormedType .bytes
  | fixedBytes (s : ByteSize) : WellFormedType (.fixedBytes s)
  | string : WellFormedType .string
  | array (e : ABIType) : WellFormedType e → WellFormedType (.array e)
  | fixedArray (n : Nat) (e : ABIType) : (isDynamic e = true → 0 < n) → WellFormedType e → WellFormedType (.fixedArray n e)
  | tuple (ts : List ABIType) : (∀ t ∈ ts, WellFormedType t) → WellFormedType (.tuple ts)

theorem foldl_headSize_mono (ts : List ABIType) : ∀ (init : Nat), init ≤ ts.foldl (fun a t => a + headSize t) init := by
  induction ts with
  | nil => intro init; simp
  | cons t ts' ih => intro init; rw [List.foldl_cons]; exact le_trans (by omega) (ih (init + headSize t))

theorem foldl_headSize_init_le (ts : List ABIType) : ∀ i j, i ≤ j →
    ts.foldl (fun a t => a + headSize t) i ≤ ts.foldl (fun a t => a + headSize t) j := by
  induction ts with
  | nil => intro i j h; simpa
  | cons t ts' ih => intro i j h; rw [List.foldl_cons, List.foldl_cons]; exact ih _ _ (by omega)

theorem foldl_headSize_ge_of_dyn (ts : List ABIType) (h : ts.any isDynamic = true) :
    32 ≤ ts.foldl (fun a t => a + headSize t) 0 := by
  induction ts with
  | nil => simp at h
  | cons t ts' ih =>
    rw [List.foldl_cons, Nat.zero_add]
    by_cases hd : isDynamic t = true
    · have h32 : headSize t = 32 := headSize_dynamic t hd
      calc (32 : Nat) = headSize t := h32.symm
        _ ≤ ts'.foldl (fun a t => a + headSize t) (headSize t) := foldl_headSize_mono ts' (headSize t)
    · have hdf : isDynamic t = false := by cases hh : isDynamic t; rfl; exact absurd hh hd
      have h' : ts'.any isDynamic = true := by rw [List.any_cons, hdf, Bool.false_or] at h; exact h
      exact le_trans (ih h') (foldl_headSize_init_le ts' 0 (headSize t) (by omega))

theorem dyn_encoding_ge_32_bytes (v : ABIValue) (ev : ByteArray) (henc : encode .bytes v = Except.ok ev) : 32 ≤ ev.size := by
  cases v with
  | bytes v' =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    split at henc
    · have he : ev = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size) := (Except.ok.inj henc).symm
      rw [he, ByteArray.size_append]; have := uint256ToBytes_size_ge v'.size; omega
    · exact absurd henc (by simp)
  | uint _ | int _ | bool _ | string _ | address _ | array _ | tuple _ => badVal henc

theorem dyn_encoding_ge_32_string (v : ABIValue) (ev : ByteArray) (henc : encode .string v = Except.ok ev) : 32 ≤ ev.size := by
  cases v with
  | string v' =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    split at henc
    · have he : ev = uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size) := (Except.ok.inj henc).symm
      rw [he, ByteArray.size_append]; have := uint256ToBytes_size_ge v'.toUTF8.size; omega
    · exact absurd henc (by simp)
  | uint _ | int _ | bool _ | bytes _ | address _ | array _ | tuple _ => badVal henc

theorem dyn_encoding_ge_32_array (e : ABIType) (v : ABIValue) (ev : ByteArray) (henc : encode (.array e) v = Except.ok ev) : 32 ≤ ev.size := by
  cases v with
  | array vals =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc
    rcases hentry : foldABIType EncoderEntry e with ⟨elemDyn, elemEnc⟩
    rw [hentry] at henc; dsimp at henc
    split at henc
    · cases hEL : encodeListElems elemEnc vals with
      | error x => rw [hEL] at henc; exact absurd (show Except.error x = Except.ok ev from henc) (by simp)
      | ok encd =>
        rw [hEL] at henc
        have he : ev = uint256ToBytes vals.length ++ arrayPack elemDyn encd := (Except.ok.inj henc).symm
        rw [he, ByteArray.size_append]; have := uint256ToBytes_size_ge vals.length; omega
    · exact absurd henc (by simp)
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | tuple _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)

theorem dyn_encoding_ge_32_fixedArray (n : Nat) (e : ABIType) (hn : isDynamic e = true → 0 < n)
    (hdyn : isDynamic (.fixedArray n e) = true) (v : ABIValue) (ev : ByteArray)
    (henc : encode (.fixedArray n e) v = Except.ok ev) : 32 ≤ ev.size := by
  cases v with
  | array vals =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc
    rcases hentry : foldABIType EncoderEntry e with ⟨elemDyn, elemEnc⟩
    rw [hentry] at henc; dsimp at henc
    have helem : elemEnc = encode e := by unfold encode; rw [hentry]
    split at henc
    · exact absurd henc (by simp)
    · rename_i hlen
      cases hEL : encodeListElems elemEnc vals with
      | error x => rw [hEL] at henc; exact absurd (show Except.error x = Except.ok ev from henc) (by simp)
      | ok encd =>
        rw [hEL] at henc
        have he : ev = arrayPack elemDyn encd := (Except.ok.inj henc).symm
        have hisdyn_e : isDynamic e = true := by simpa [isDynamic] using hdyn
        have helemD : elemDyn = true := by
          have h := enc_fst_eq_isDynamic e; rw [hentry] at h; exact h.trans hisdyn_e
        have hlen_eq : encd.length = vals.length := encodeListElems_length e vals encd (by rw [← helem]; exact hEL)
        have hvn : vals.length = n := by simpa using hlen
        have hn' : 0 < n := hn hisdyn_e
        rw [he, helemD, arrayPack_dyn, ByteArray.size_append]
        have hge := dynHeadsFrom_size_ge encd (if encd.length = 0 then 32 else encd.length * 32)
        have : 0 < encd.length := by rw [hlen_eq, hvn]; exact hn'
        omega
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | tuple _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)

theorem tupleHeadsFrom_ge_32 : ∀ (encd : List (Bool × ByteArray)) (off : Nat), (∃ b ∈ encd, b.1 = true) →
    32 ≤ ((tupleHeadsFrom off encd).foldl (·++·) ByteArray.empty).size := by
  intro encd
  induction encd with
  | nil => intro off h; obtain ⟨b, hb, _⟩ := h; simp at hb
  | cons x xs ih =>
    intro off h
    obtain ⟨d, e⟩ := x
    rw [tupleHeadsFrom_cons, ba_foldl_cons, ByteArray.size_append]
    cases d with
    | true =>
      simp only [if_true]
      have := uint256ToBytes_size_ge off; omega
    | false =>
      simp only [Bool.false_eq_true, if_false]
      have hxs : ∃ b ∈ xs, b.1 = true := by
        obtain ⟨b, hb, hb1⟩ := h
        rcases List.mem_cons.mp hb with rfl | hb'
        · simp at hb1
        · exact ⟨b, hb', hb1⟩
      have := ih off hxs; omega

theorem go_has_dyn_entry (ts : List ABIType) :
    ∀ (vs : List ABIValue) (encd : List (Bool × ByteArray)),
      instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd →
      ts.any isDynamic = true → ∃ b ∈ encd, b.1 = true := by
  induction ts with
  | nil => intro vs encd _ h; simp at h
  | cons t ts' ih =>
    intro vs encd hgo h
    simp only [foldAll] at hgo
    rcases hentry : foldABIType EncoderEntry t with ⟨dyn, enc⟩
    rw [hentry] at hgo
    obtain ⟨v, vs', b, tail, rfl, hb, htail, rfl⟩ := go_cons_ok dyn enc (foldAll EncoderEntry ts') vs encd hgo
    have hdyneq : dyn = isDynamic t := by have h2 := enc_fst_eq_isDynamic t; rw [hentry] at h2; exact h2
    rw [List.any_cons] at h
    by_cases hd : isDynamic t = true
    · exact ⟨(dyn, b), by simp, by rw [hdyneq]; exact hd⟩
    · have hdf : isDynamic t = false := by cases hh : isDynamic t; rfl; exact absurd hh hd
      have h' : ts'.any isDynamic = true := by rw [hdf, Bool.false_or] at h; exact h
      obtain ⟨b', hb', hb'1⟩ := ih vs' tail htail h'
      exact ⟨b', List.mem_cons_of_mem _ hb', hb'1⟩

theorem dyn_encoding_ge_32_tuple (ts : List ABIType) (hdyn : isDynamic (.tuple ts) = true)
    (v : ABIValue) (ev : ByteArray) (henc : encode (.tuple ts) v = Except.ok ev) : 32 ≤ ev.size := by
  cases v with
  | tuple vs =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    cases hgo : instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs with
    | error x => rw [hgo] at henc; exact absurd (show Except.error x = Except.ok ev from henc) (by simp)
    | ok encd =>
      rw [hgo] at henc
      have hpack : ev = tuplePack (ts.map headSize) (ts.map isDynamic) encd :=
        (Except.ok.inj (show Except.ok (tuplePack (ts.map headSize) (ts.map isDynamic) encd) = Except.ok ev from henc)).symm
      have hany : (ts.map isDynamic).any id = true := by rw [tuple_any_isDynamic]; exact hdyn
      have hany_ts : ts.any isDynamic = true := by simpa [List.any_map] using hany
      have hHAeq : (ts.map headSize).foldl (· + ·) 0 = ts.foldl (fun a t => a + headSize t) 0 := by rw [List.foldl_map]
      rw [hpack, tuplePack_dyn _ _ _ hany, hHAeq, ByteArray.size_append]
      have hentry := go_has_dyn_entry ts vs encd hgo hany_ts
      have hheads := tupleHeadsFrom_ge_32 encd (ts.foldl (fun a t => a + headSize t) 0) hentry
      omega
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | array _ => badVal henc

theorem dyn_encoding_ge_32 (t : ABIType) (hwf : WellFormedType t) (hdyn : isDynamic t = true)
    (v : ABIValue) (ev : ByteArray) (henc : encode t v = Except.ok ev) : 32 ≤ ev.size := by
  cases t with
  | bytes => exact dyn_encoding_ge_32_bytes v ev henc
  | string => exact dyn_encoding_ge_32_string v ev henc
  | array e => exact dyn_encoding_ge_32_array e v ev henc
  | fixedArray n e => cases hwf with | fixedArray _ _ hn _ => exact dyn_encoding_ge_32_fixedArray n e hn hdyn v ev henc
  | tuple ts => exact dyn_encoding_ge_32_tuple ts hdyn v ev henc
  | uint s => exact absurd hdyn (by simp [isDynamic])
  | int s => exact absurd hdyn (by simp [isDynamic])
  | bool => exact absurd hdyn (by simp [isDynamic])
  | address => exact absurd hdyn (by simp [isDynamic])
  | fixedBytes s => exact absurd hdyn (by simp [isDynamic])

theorem go_has_big_dyn_entry (ts : List ABIType) (hwf : ∀ t ∈ ts, WellFormedType t) :
    ∀ (vs : List ABIValue) (encd : List (Bool × ByteArray)),
      instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd →
      ts.any isDynamic = true → (∀ b ∈ encd, b.1 = true → b.2.size < 2^256) →
      ∃ b ∈ encd, b.1 = true ∧ 32 ≤ b.2.size := by
  induction ts with
  | nil => intro vs encd _ h _; simp at h
  | cons t ts' ih =>
    intro vs encd hgo h hbnd
    have hmemt : t ∈ (t :: ts') := by simp
    simp only [foldAll] at hgo
    rcases hentry : foldABIType EncoderEntry t with ⟨dyn, enc⟩
    rw [hentry] at hgo
    obtain ⟨v, vs', b, tail, rfl, hb, htail, rfl⟩ := go_cons_ok dyn enc (foldAll EncoderEntry ts') vs encd hgo
    have hdyneq : dyn = isDynamic t := by have h2 := enc_fst_eq_isDynamic t; rw [hentry] at h2; exact h2
    have henc_t : enc = encode t := by unfold encode; rw [hentry]
    rw [List.any_cons] at h
    by_cases hd : isDynamic t = true
    · refine ⟨(dyn, b), by simp, by rw [hdyneq]; exact hd, ?_⟩
      have hbsz : b.size < 2^256 := hbnd (dyn, b) (by simp) (by rw [hdyneq]; exact hd)
      exact dyn_encoding_ge_32 t (hwf t hmemt) hd v b (by rw [← henc_t]; exact hb)
    · have hdf : isDynamic t = false := by cases hh : isDynamic t; rfl; exact absurd hh hd
      have h' : ts'.any isDynamic = true := by rw [hdf, Bool.false_or] at h; exact h
      obtain ⟨b', hb', hb'1, hb'sz⟩ := ih (fun t' ht' => hwf t' (List.mem_cons_of_mem t ht')) vs' tail htail h'
        (fun b'' hb'' => hbnd b'' (List.mem_cons_of_mem _ hb''))
      exact ⟨b', List.mem_cons_of_mem _ hb', hb'1, hb'sz⟩

theorem dyn_tuple_hbd (ts : List ABIType) (hwf : ∀ t ∈ ts, WellFormedType t)
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdyn : ts.any isDynamic = true) (v : ABIValue) (enc : ByteArray)
    (henc : encode (.tuple ts) v = Except.ok enc) (hsz : enc.size < 2^256) :
    ts.foldl (fun a t => a + headSize t) 0 + 32 ≤ enc.size := by
  cases v with
  | tuple vs =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    cases hgo : instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs with
    | error x => rw [hgo] at henc; exact absurd (show Except.error x = Except.ok enc from henc) (by simp)
    | ok encd =>
      rw [hgo] at henc
      have hpack : enc = tuplePack (ts.map headSize) (ts.map isDynamic) encd :=
        (Except.ok.inj (show Except.ok (tuplePack (ts.map headSize) (ts.map isDynamic) encd) = Except.ok enc from henc)).symm
      have hany : (ts.map isDynamic).any id = true := by simpa [List.any_map] using hdyn
      have hHAeq : (ts.map headSize).foldl (· + ·) 0 = ts.foldl (fun a t => a + headSize t) 0 := by rw [List.foldl_map]
      have hpackht : enc = (tupleHeadsFrom (ts.foldl (fun a t => a + headSize t) 0) encd).foldl (·++·) ByteArray.empty ++ tupleTails encd := by
        rw [hpack, tuplePack_dyn _ _ _ hany, hHAeq]
      have hpsz : enc.size = ((tupleHeadsFrom (ts.foldl (fun a t => a + headSize t) 0) encd).foldl (·++·) ByteArray.empty).size + (tupleTails encd).size := by
        rw [hpackht, ByteArray.size_append]
      have hge := tupleHeadsFrom_size_ge ts hsize vs encd (ts.foldl (fun a t => a + headSize t) 0) hgo
      have hbnd_dyn : ∀ b ∈ encd, b.1 = true → b.2.size < 2^256 := fun b hb hb1 => by
        have := tupleTails_mem_le encd b hb hb1; omega
      obtain ⟨b, hb, hb1, hbsize⟩ := go_has_big_dyn_entry ts hwf vs encd hgo hdyn hbnd_dyn
      have := tupleTails_mem_le encd b hb hb1
      omega
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | array _ => badVal henc

theorem size_eq_tuple_wf (ts : List ABIType)
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hstat : isDynamic (.tuple ts) = false) (v : ABIValue) (ev : ByteArray)
    (henc : encode (.tuple ts) v = Except.ok ev) : ev.size = headSize (.tuple ts) := by
  cases v with
  | tuple vs =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    cases hgo : instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs with
    | error x => rw [hgo] at henc; exact absurd (show Except.error x = Except.ok ev from henc) (by simp)
    | ok encd =>
      rw [hgo] at henc
      have hpack : ev = tuplePack (ts.map headSize) (ts.map isDynamic) encd :=
        (Except.ok.inj (show Except.ok (tuplePack (ts.map headSize) (ts.map isDynamic) encd) = Except.ok ev from henc)).symm
      have hany : (ts.map isDynamic).any id = false := by rw [tuple_any_isDynamic]; exact hstat
      rw [hpack, tuplePack_static _ _ _ hany]
      exact tuplePackStatic_size_wf ts hsize (tuple_static_elems ts hstat) vs encd hgo
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | array _ => badVal henc

/-- `WFFacts` for every well-formed type, INCLUDING tuples (structs). The dynamic-tuple `rt`
    discharges its head-area bound internally via `dyn_tuple_hbd`, so it stays bound-free and
    composes into arrays/tuples at every level. -/
theorem wfFactsWF : (t : ABIType) → WellFormedType t → WFFacts t
  | .uint s, _ => .uint s
  | .int s, _ => .int s
  | .bool, _ => .bool
  | .address, _ => .address
  | .fixedBytes s, _ => .fixedBytes s
  | .bytes, _ => .bytes
  | .string, _ => .string
  | .array e, hwf => .array e (wfFactsWF e (by cases hwf with | array _ h => exact h))
  | .fixedArray n e, hwf => .fixedArray n e (wfFactsWF e (by cases hwf with | fixedArray _ _ _ h => exact h))
  | .tuple ts, hwf =>
      have hfield : ∀ t' ∈ ts, WellFormedType t' := by cases hwf with | tuple _ h => exact h
      ⟨fun v enc data off hsz henc hdata => by
          cases hdyn : ts.any isDynamic with
          | false =>
            have hstat_tuple : isDynamic (.tuple ts) = false := by rw [← tuple_any_isDynamic]; simpa [List.any_map] using hdyn
            exact roundtrip_tuple_stat_wf ts data
              (fun t' ht' v' ev' o' hlt he' hd' => (wfFactsWF t' (hfield t' ht')).rt v' ev' data o' hlt he' hd')
              (fun t' ht' => (wfFactsWF t' (hfield t' ht')).size_eq)
              hstat_tuple v enc off hsz henc hdata
          | true =>
            have hhbd := dyn_tuple_hbd ts hfield (fun t' ht' => (wfFactsWF t' (hfield t' ht')).size_eq) hdyn v enc henc hsz
            have hle : off + enc.size ≤ data.size := not_gt_of_extract_eq data off enc.size (by rw [hdata]) (by omega)
            have hbd : off + ts.foldl (fun a t => a + headSize t) 0 + 32 ≤ data.size := by omega
            exact roundtrip_tuple_wf ts data
              (fun t' ht' v' ev' o' hlt he' hd' => (wfFactsWF t' (hfield t' ht')).rt v' ev' data o' hlt he' hd')
              (fun t' ht' => (wfFactsWF t' (hfield t' ht')).size_eq)
              (fun t' ht' => (wfFactsWF t' (hfield t' ht')).szdvd)
              v enc off hsz hbd henc hdata,
       fun hstat => size_eq_tuple_wf ts (fun t' ht' => (wfFactsWF t' (hfield t' ht')).size_eq) hstat,
       fun v ev hsz henc => szdvd_tuple ts
          (fun t' ht' => (wfFactsWF t' (hfield t' ht')).size_eq)
          (fun t' ht' => (wfFactsWF t' (hfield t' ht')).szdvd) v ev hsz henc⟩
  termination_by t => sizeOf t
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have hm := ‹_ ∈ _›; have := List.sizeOf_lt_of_mem hm; omega)

/-- Clean roundtrip (offset 0) for ANY well-formed type — atomics, bytes/string, nested
    arrays/fixedArrays, AND tuples/structs (nested to any depth). -/
theorem roundtrip_wf (t : ABIType) (hwf : WellFormedType t) (v : ABIValue) (data : ByteArray)
    (hsz : data.size < 2^256) (henc : encode t v = Except.ok data) :
    decode t data 0 = Except.ok (v, data.size) := by
  have h := (wfFactsWF t hwf).rt v data data 0 hsz henc (by rw [Nat.zero_add, extract_self])
  simpa using h

/-- Function-call roundtrip for ANY well-formed argument list, including struct arguments —
    no per-signature proof needed. -/
theorem roundtrip_args_wff (types : List ABIType) (data : ByteArray) (values : List ABIValue)
    (hwf : ∀ t ∈ types, WellFormedType t)
    (hsz : data.size < 2^256)
    (henc : encodeArgs types values = Except.ok data) :
    decodeArgs types data 0 = Except.ok values := by
  unfold encodeArgs at henc
  split at henc
  · exact absurd henc (by simp)
  · have hd : decode (.tuple types) data 0 = Except.ok (.tuple values, 0 + data.size) :=
      (wfFactsWF (.tuple types) (.tuple types hwf)).rt (.tuple values) data data 0 hsz henc
        (by rw [Nat.zero_add, extract_self])
    unfold decodeArgs; rw [hd]; rfl

/-! ### Concrete signatures, derived from the well-formed visitor

With `wfFactsWF` in hand the worked signatures are one-liners: the visitor supplies every
per-field fact and (for dynamic tuples) discharges the head-area bound internally, so these
carry only `enc.size < 2^256` — no manual dispatch, no `hbd`. -/

/-- `(bytes, uintN)` — a mixed dynamic+static tuple roundtrip. -/
theorem roundtrip_tuple_bytes_uint (s : ByteSize) (data : ByteArray)
    (v : ABIValue) (enc : ByteArray) (off : Nat) (hwf : enc.size < 2^256)
    (henc : encode (.tuple [.bytes, .uint s]) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.tuple [.bytes, .uint s]) data off = Except.ok (v, off + enc.size) :=
  (wfFactsWF (.tuple [.bytes, .uint s]) (.tuple _ (by intro t ht; fin_cases ht <;> constructor))).rt
    v enc data off hwf henc hdata

/-- ERC20-style `(bytes, uintN)` argument decode. -/
theorem roundtrip_args_bytes_uint (s : ByteSize) (data : ByteArray) (values : List ABIValue)
    (hwf : data.size < 2^256) (henc : encodeArgs [.bytes, .uint s] values = Except.ok data) :
    decodeArgs [.bytes, .uint s] data 0 = Except.ok values :=
  roundtrip_args_wff [.bytes, .uint s] data values (by intro t ht; fin_cases ht <;> constructor) hwf henc

/-- `(address, uintN)` — static tuple (ERC20 `transfer(to, amount)` arguments). -/
theorem roundtrip_tuple_addr_uint (s : ByteSize) (data : ByteArray)
    (v : ABIValue) (enc : ByteArray) (off : Nat) (hwf : enc.size < 2^256)
    (henc : encode (.tuple [.address, .uint s]) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.tuple [.address, .uint s]) data off = Except.ok (v, off + enc.size) :=
  (wfFactsWF (.tuple [.address, .uint s]) (.tuple _ (by intro t ht; fin_cases ht <;> constructor))).rt
    v enc data off hwf henc hdata

/-- ERC20 `transfer`-style argument decode. -/
theorem roundtrip_args_addr_uint (s : ByteSize) (data : ByteArray) (values : List ABIValue)
    (hwf : data.size < 2^256) (henc : encodeArgs [.address, .uint s] values = Except.ok data) :
    decodeArgs [.address, .uint s] data 0 = Except.ok values :=
  roundtrip_args_wff [.address, .uint s] data values (by intro t ht; fin_cases ht <;> constructor) hwf henc

/-- `(uintN, bytes)` — mixed static + dynamic tuple. -/
theorem roundtrip_tuple_uint_bytes (s : ByteSize) (data : ByteArray)
    (v : ABIValue) (enc : ByteArray) (off : Nat) (hwf : enc.size < 2^256)
    (henc : encode (.tuple [.uint s, .bytes]) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.tuple [.uint s, .bytes]) data off = Except.ok (v, off + enc.size) :=
  (wfFactsWF (.tuple [.uint s, .bytes]) (.tuple _ (by intro t ht; fin_cases ht <;> constructor))).rt
    v enc data off hwf henc hdata
