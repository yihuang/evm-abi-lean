import EvmAbi.Roundtrip.Basic

/-! Atomic/primitive-type roundtrips (uint/int/bool/address/fixedBytes/bytes/string), at offset 0 and offset-generalized. -/

open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode
set_option autoImplicit false

/-! ## Atomic proofs -/

theorem roundtrip_uint (s : ByteSize) (v : ABIValue) (data : ByteArray)
    (henc : encode (.uint s) v = Except.ok data) : decode (.uint s) data 0 = Except.ok (v, data.size) := by
  cases v with
  | uint v' =>
    openEnc henc
    by_cases hm : v' < 2 ^ (s.len * 8)
    · simp [hm] at henc
      have hd : uint256ToBytes v' = data := henc
      rw [hd.symm]
      openDec
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
    openEnc henc
    simp at henc
    have hd : uint256ToBytes (if v' then 1 else 0) = data := henc
    rw [hd.symm]
    openDec
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
    openEnc henc
    by_cases hsize : v'.size ≠ 20
    · simp [hsize] at henc
    · have hsize20 : v'.size = 20 := by omega
      simp [hsize20] at henc
      have hd : padLeft v' 32 = data := henc
      subst hd
      openDec
      have h_extract : (padLeft v' 32).extract 12 32 = v' := padLeft_extract_address v' hsize20
      have h_sz : (padLeft v' 32).size = 32 := by
        unfold padLeft; simp [hsize20, zeros_size]
      simp [h_extract, h_sz]
  | _ => badVal henc

theorem roundtrip_fixedBytes (s : ByteSize) (v : ABIValue) (data : ByteArray)
    (henc : encode (.fixedBytes s) v = Except.ok data) : decode (.fixedBytes s) data 0 = Except.ok (v, data.size) := by
  cases v with
  | bytes v' =>
    openEnc henc
    by_cases hsz : v'.size = s.len
    · simp [hsz] at henc
      have hd : padRight v' 32 = data := henc
      subst hd
      openDec
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
        openEncG; simpa [h256_eq, hv256]
      have hd : data = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size) := by
        injection hval.symm.trans henc; symm; assumption
      rw [hd]
      openDec
      exact decodeDynamicBytes_roundtrip v' hv256 (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)) rfl
    · have hval : encode .bytes (ABIValue.bytes v') = Except.error (.dataTooLong v'.size) := by
        openEncG
        have h_ge : ¬ v'.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
          rw [← h256_eq]; exact hv256
        simp [h_ge]
      rw [hval] at henc; simp at henc
  | uint n =>
    have h_wrong : encode .bytes (ABIValue.uint n) = Except.error .typeValueMismatch := by
      openEncG
    rw [h_wrong] at henc; simp at henc
  | bool b =>
    have h_wrong : encode .bytes (ABIValue.bool b) = Except.error .typeValueMismatch := by
      openEncG
    rw [h_wrong] at henc; simp at henc
  | address a =>
    have h_wrong : encode .bytes (ABIValue.address a) = Except.error .typeValueMismatch := by
      openEncG
    rw [h_wrong] at henc; simp at henc
  | int i =>
    have h_wrong : encode .bytes (ABIValue.int i) = Except.error .typeValueMismatch := by
      openEncG
    rw [h_wrong] at henc; simp at henc
  | string s =>
    have h_wrong : encode .bytes (ABIValue.string s) = Except.error .typeValueMismatch := by
      openEncG
    rw [h_wrong] at henc; simp at henc
  | array arr =>
    have h_wrong : encode .bytes (ABIValue.array arr) = Except.error .typeValueMismatch := by
      openEncG
    rw [h_wrong] at henc; simp at henc
  | tuple tup =>
    have h_wrong : encode .bytes (ABIValue.tuple tup) = Except.error .typeValueMismatch := by
      openEncG
    rw [h_wrong] at henc; simp at henc

theorem roundtrip_string (v : ABIValue) (data : ByteArray)
    (henc : encode .string v = Except.ok data) : decode .string data 0 = Except.ok (v, data.size) := by
  have h256_eq : (2 : ℕ) ^ 256 = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by native_decide
  cases v with
  | string v' =>
    by_cases huv256 : v'.toUTF8.size < 2 ^ 256
    · have hval : encode .string (ABIValue.string v') = Except.ok (uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size)) := by
        openEncG; simpa [h256_eq, huv256]
      have hd : data = uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size) := by
        injection hval.symm.trans henc; symm; assumption
      rw [hd]
      openDec
      exact decodeDynamicString_roundtrip v' huv256 (uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size)) rfl
    · have hval : encode .string (ABIValue.string v') = Except.error (.dataTooLong v'.toUTF8.size) := by
        openEncG
        have h_ge : ¬ v'.toUTF8.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
          rw [← h256_eq]; exact huv256
        have h_ge' : ¬ v'.utf8ByteSize < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
          simpa using h_ge
        simp [h_ge']
      rw [hval] at henc; simp at henc
  | uint n =>
    have h_wrong : encode .string (ABIValue.uint n) = Except.error .typeValueMismatch := by
      openEncG
    rw [h_wrong] at henc; simp at henc
  | bool b =>
    have h_wrong : encode .string (ABIValue.bool b) = Except.error .typeValueMismatch := by
      openEncG
    rw [h_wrong] at henc; simp at henc
  | address a =>
    have h_wrong : encode .string (ABIValue.address a) = Except.error .typeValueMismatch := by
      openEncG
    rw [h_wrong] at henc; simp at henc
  | int i =>
    have h_wrong : encode .string (ABIValue.int i) = Except.error .typeValueMismatch := by
      openEncG
    rw [h_wrong] at henc; simp at henc
  | bytes b =>
    have h_wrong : encode .string (ABIValue.bytes b) = Except.error .typeValueMismatch := by
      openEncG
    rw [h_wrong] at henc; simp at henc
  | array arr =>
    have h_wrong : encode .string (ABIValue.array arr) = Except.error .typeValueMismatch := by
      openEncG
    rw [h_wrong] at henc; simp at henc
  | tuple tup =>
    have h_wrong : encode .string (ABIValue.tuple tup) = Except.error .typeValueMismatch := by
      openEncG
    rw [h_wrong] at henc; simp at henc

/-! ## Int helper lemmas -/

theorem intToBytes_decode_nonneg (s : ByteSize) (v' : Int) (hv_nonneg : v' ≥ 0)
    (hrange : v' < (2 ^ (s.len * 8 - 1) : Int)) (hbits256 : s.len * 8 ≤ 256) :
    decode (.int s) (intToBytes v' s.len) 0 = Except.ok (ABIValue.int v', (intToBytes v' s.len).size) := by
  openDec
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

theorem intToBytes_decode_neg (s : ByteSize) (v' : Int) (hv_neg : ¬ v' ≥ 0)
    (hrange : -(2 ^ (s.len * 8 - 1) : Int) ≤ v') (hbits256 : s.len * 8 ≤ 256) :
    decode (.int s) (intToBytes v' s.len) 0 = Except.ok (ABIValue.int v', (intToBytes v' s.len).size) := by
  openDec
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

theorem roundtrip_int (s : ByteSize) (v' : Int) (data : ByteArray)
    (henc : encode (.int s) (ABIValue.int v') = Except.ok data) : decode (.int s) data 0 = Except.ok (ABIValue.int v', data.size) := by
  openEnc henc; simp at henc
  by_cases h1 : v' < -(2 ^ (s.len * 8 - 1) : Int)
  · simp [h1] at henc
  · by_cases h2 : v' ≥ (2 ^ (s.len * 8 - 1) : Int)
    · simp [h2] at henc
    · simp [h1, h2] at henc
      have hd : intToBytes v' s.len = data := henc
      rw [hd.symm]
      openDec
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
  openEnc henc
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
    openDec
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
  openEnc henc
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
      openDec
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
  openEnc henc
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
    openDec
    simp [h_not_gt, hdata']
    have h_val : bytesToNat (uint256ToBytes (if v' then 1 else 0)) = (if v' then 1 else 0) :=
      bytesToNat_uint256ToBytes (if v' then 1 else 0)
    simp [h_val]; cases v' <;> simp
/-- roundtrip_fixedBytes generalized to any offset. -/
theorem roundtrip_offset_fixedBytes (s : ByteSize) (v' : ByteArray) (enc data : ByteArray) (off : Nat)
    (henc : encode (.fixedBytes s) (.bytes v') = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.fixedBytes s) data off = Except.ok (.bytes v', off + enc.size) := by
  openEnc henc
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
      openDec
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
  openEnc henc; simp at henc
  by_cases h1 : v' < -(2 ^ (s.len * 8 - 1) : Int); · simp [h1] at henc
  · by_cases h2 : v' ≥ (2 ^ (s.len * 8 - 1) : Int); · simp [h2] at henc
    · simp [h1, h2] at henc
      subst henc
      have hsize32 : (intToBytes v' s.len).size = 32 := intToBytes_size32 s v' ⟨by omega, by omega⟩
      rw [hsize32]
      have hdata' : data.extract off (off + 32) = intToBytes v' s.len := by
        simpa [hsize32] using hdata
      have h_not_too_short : off + 32 ≤ data.size :=
        not_gt_of_extract_eq data off 32 (by rw [hdata', hsize32]) (by omega)
      by_cases hshort : off + 32 > data.size
      · exfalso; omega
      · have h_not_gt : ¬ off + 32 > data.size := by omega
        openDec
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
lemma decodeDynamicBytes_roundtrip_off (v' : ByteArray) (hv256 : v'.size < 2 ^ 256)
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
  have hmin2 : min (off + (32 + v'.size)) (off + (A ++ P).size) = off + 32 + v'.size := by rw [h_size]; omega
  have h_ext32 : data.extract off (off + 32) = A :=
    extract_head32 data off (off + (A ++ P).size) A P ha_sz (by rw [h_size]; omega) hdata
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
lemma decodeDynamicString_roundtrip_off (v' : String) (hv256 : v'.toUTF8.size < 2 ^ 256)
    (enc data : ByteArray) (off : Nat)
    (henc : enc = uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size))
    (hdata : data.extract off (off + enc.size) = enc) :
    decodeDynamicString data off = Except.ok (.string v', off + enc.size) := by
  rw [decodeDynamicString, decodeDynamicBytes_roundtrip_off v'.toUTF8 hv256 enc data off henc hdata]
  simp [Except.map]; have h : v'.toByteArray = v'.toUTF8 := rfl; rw [h, fromUTF8!_toUTF8 v']

/-! ## Offset-general atomic full wrappers (handle any `ABIValue`) -/

/-- Uniform "wrong constructor ⇒ encode errors" contradiction for atomic encoders. -/
theorem roundtrip_off_uint (s : ByteSize) (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode (.uint s) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.uint s) data off = Except.ok (v, off + enc.size) := by
  rcases v with v'|i|b|ba|str|addr|arr|tup
  · exact roundtrip_offset_uint s v' enc data off henc hdata
  all_goals badVal henc

theorem roundtrip_off_int (s : ByteSize) (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode (.int s) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.int s) data off = Except.ok (v, off + enc.size) := by
  rcases v with v'|i|b|ba|str|addr|arr|tup
  · badVal henc
  · exact roundtrip_offset_int s i enc data off henc hdata
  all_goals badVal henc

theorem roundtrip_off_bool (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode .bool v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode .bool data off = Except.ok (v, off + enc.size) := by
  rcases v with v'|i|b|ba|str|addr|arr|tup
  · badVal henc
  · badVal henc
  · exact roundtrip_offset_bool b enc data off henc hdata
  all_goals badVal henc

theorem roundtrip_off_address (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode .address v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode .address data off = Except.ok (v, off + enc.size) := by
  cases v
  case address addr => exact roundtrip_offset_address addr enc data off henc hdata
  all_goals badVal henc

theorem roundtrip_off_fixedBytes (s : ByteSize) (v : ABIValue) (enc data : ByteArray) (off : Nat)
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
      openDec
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
      openDec
      exact decodeDynamicString_roundtrip_off v' huv256 enc data off hd hdata
    · exact absurd henc (by
        unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp
        have h_ge : ¬ v'.toUTF8.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
          rw [← h256_eq]; exact huv256
        have h_ge' : ¬ v'.utf8ByteSize < 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
          simpa using h_ge
        simp [h_ge'])
  all_goals badVal henc
