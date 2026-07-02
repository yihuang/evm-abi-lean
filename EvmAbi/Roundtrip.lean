/-
# Universal Roundtrip Theorem via ABIVisitor
-/

import EvmAbi.LemmaUtils
open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode
set_option autoImplicit false

/-- Offset-generalized roundtrip property carried by the visitor.

    The offset-0 form (`roundtrip`) is recovered as a special case, but the
    generalized form is what array/tuple recursion needs: an element decoded at
    an arbitrary position `off` inside a larger buffer roundtrips, provided the
    buffer contains the element's encoding as the slice `[off, off + enc.size)`. -/
structure RoundtripVisitor (t : ABIType) : Type where
  roundtrip_off : ∀ (v : ABIValue) (enc data : ByteArray) (off : Nat),
    encode t v = Except.ok enc →
    data.extract off (off + enc.size) = enc →
    decode t data off = Except.ok (v, off + enc.size)
  /-- Static encodings have size exactly `headSize` — needed because the tuple
      decoder advances by `headSize`, not by the actual consumed length. -/
  size_eq : isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray),
    encode t v = Except.ok ev → ev.size = headSize t

/-- The offset-0 roundtrip is a special case of `roundtrip_off` (with `data = enc`, `off = 0`). -/
theorem RoundtripVisitor.roundtrip {t : ABIType} (rv : RoundtripVisitor t)
    (v : ABIValue) (data : ByteArray)
    (henc : encode t v = Except.ok data) : decode t data 0 = Except.ok (v, data.size) := by
  have h := rv.roundtrip_off v data data 0 henc (by rw [Nat.zero_add, extract_self])
  simpa using h

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
        have hp : 2 ^ (s.len * 8) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) hbits256; omega
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
          have hp : 2 ^ (s.len * 8) ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) hbits256; omega
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
      simp [h_extract_v', hsize32]
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
              apply (Nat.cast_inj (R := ℤ)).mp; simpa using h
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
  all_goals exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)

private theorem roundtrip_off_int (s : ByteSize) (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode (.int s) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.int s) data off = Except.ok (v, off + enc.size) := by
  rcases v with v'|i|b|ba|str|addr|arr|tup
  · exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  · exact roundtrip_offset_int s i enc data off henc hdata
  all_goals exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)

private theorem roundtrip_off_bool (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode .bool v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode .bool data off = Except.ok (v, off + enc.size) := by
  rcases v with v'|i|b|ba|str|addr|arr|tup
  · exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  · exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  · exact roundtrip_offset_bool b enc data off henc hdata
  all_goals exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)

private theorem roundtrip_off_address (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode .address v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode .address data off = Except.ok (v, off + enc.size) := by
  cases v
  case address addr => exact roundtrip_offset_address addr enc data off henc hdata
  all_goals exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)

private theorem roundtrip_off_fixedBytes (s : ByteSize) (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode (.fixedBytes s) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.fixedBytes s) data off = Except.ok (v, off + enc.size) := by
  cases v
  case bytes ba => exact roundtrip_offset_fixedBytes s ba enc data off henc hdata
  all_goals exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)

private theorem roundtrip_off_bytes (v : ABIValue) (enc data : ByteArray) (off : Nat)
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
  all_goals exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)

private theorem roundtrip_off_string (v : ABIValue) (enc data : ByteArray) (off : Nat)
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
  all_goals exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)

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
        apply (Nat.cast_inj (R := ℤ)).mp; simpa using h
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
      simp only [headSize]; rw [← hev]; exact uint256ToBytes_size v' (natToBytes_size_bound v' hv256)
    · exact absurd (show Except.error _ = Except.ok ev from henc) (by simp)
  | _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)

theorem size_eq_int (s : ByteSize) (v : ABIValue) (ev : ByteArray) (henc : encode (.int s) v = Except.ok ev) : ev.size = headSize (.int s) := by
  cases v with
  | int v' =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    simp only [Bool.or_eq_true, decide_eq_true_eq] at henc
    split at henc
    · exact absurd (show Except.error _ = Except.ok ev from henc) (by simp)
    · rename_i hcond
      have hev := Except.ok.inj henc
      push_neg at hcond
      simp only [headSize]; rw [← hev]; exact intToBytes_size32 s v' ⟨by omega, by omega⟩
  | _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)

theorem size_eq_bool (v : ABIValue) (ev : ByteArray) (henc : encode .bool v = Except.ok ev) : ev.size = headSize .bool := by
  cases v with
  | bool v' =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    have hev := Except.ok.inj henc
    have hbits : (if v' then 1 else 0) < 2 ^ 256 := by split <;> omega
    simp only [headSize]; rw [← hev]; exact uint256ToBytes_size _ (natToBytes_size_bound _ hbits)
  | _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)

theorem size_eq_address (v : ABIValue) (ev : ByteArray) (henc : encode .address v = Except.ok ev) : ev.size = headSize .address := by
  cases v with
  | address v' =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    split at henc
    · rename_i h20
      have hev := Except.ok.inj henc
      simp only [headSize]; rw [← hev]; unfold padLeft; simp [h20, zeros_size]
    · exact absurd (show Except.error _ = Except.ok ev from henc) (by simp)
  | _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)

theorem size_eq_fixedBytes (s : ByteSize) (v : ABIValue) (ev : ByteArray) (henc : encode (.fixedBytes s) v = Except.ok ev) : ev.size = headSize (.fixedBytes s) := by
  cases v with
  | bytes v' =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    split at henc
    · rename_i hsz
      have hev := Except.ok.inj henc
      simp only [headSize]; rw [← hev]; exact padRight_size_32 v' (by rw [hsz]; exact s.h.right)
    · exact absurd (show Except.error _ = Except.ok ev from henc) (by simp)
  | _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)

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

theorem headSize_tuple_cons (t : ABIType) (ts : List ABIType) :
    headSize (.tuple (t :: ts)) = headSize t + headSize (.tuple ts) := by simp [headSize]

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
        simp only [headSize]
    · rw [if_pos (by simpa using hlen)] at henc
      exact absurd (show Except.error (Error.arrayElemCount n vals.length) = Except.ok ev from henc) (by simp)
  | uint _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | int _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | bool _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | bytes _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | string _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | address _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | tuple _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)

/-- Roundtrip for `fixedArray n e` (static-element branch proven; dynamic element branch pending). -/
theorem roundtrip_off_fixedArray (n : Nat) (e : ABIType) (ih : RoundtripVisitor e)
    (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode (.fixedArray n e) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.fixedArray n e) data off = Except.ok (v, off + enc.size) := by
  cases v with
  | array vals =>
    unfold encode foldABIType at henc
    delta instABIVisitorEncoderEntry at henc
    rcases hentry : foldABIType EncoderEntry e with ⟨elemDyn, elemEnc⟩
    rw [hentry] at henc
    dsimp at henc
    have helem : elemEnc = encode e := by unfold encode; rw [hentry]
    by_cases hlen : vals.length = n
    · rw [if_neg (not_not_intro hlen)] at henc
      cases hEL : encodeListElems elemEnc vals with
      | error x => rw [hEL] at henc; exact absurd (show Except.error x = Except.ok enc from henc) (by simp)
      | ok encd =>
        rw [hEL] at henc
        have hpack : enc = arrayPack elemDyn encd :=
          (Except.ok.inj (show Except.ok (arrayPack elemDyn encd) = Except.ok enc from henc)).symm
        unfold decode foldABIType
        delta instABIVisitorDecoderEntry
        dsimp
        cases hdyn : isDynamic e with
        | true =>
          -- FALSE AS STATED (no size precondition). With dynamic elements the decoder reads
          -- 32-byte head pointers, but `arrayPack` computes offsets assuming `headAreaSize = n*32`
          -- (Encode.lean:35). Each element encodes with size < 2^256, yet their sizes can sum past
          -- 2^256, so a written pointer `uint256ToBytes offset` becomes >32 bytes, corrupting the
          -- head/tail layout. Provable only under `enc.size < 2^256` (all offsets fit in 32 bytes).
          sorry
        | false =>
          have helemF : elemDyn = false := by
            have h := enc_fst_eq_isDynamic e; rw [hentry] at h; simp only [] at h; rw [h, hdyn]
          rw [helemF] at hpack
          rw [show arrayPack false encd = encd.foldl (·++·) ByteArray.empty from by simp [arrayPack]] at hpack
          simp only [decodeArrayElems, decodeStaticElems, Bool.false_eq_true, if_false]
          have hdec : ∀ (w : ABIValue) (ev : ByteArray) (o : Nat),
              encode e w = Except.ok ev → data.extract o (o + ev.size) = ev →
              (foldABIType DecoderEntry e) data o = Except.ok (w, o + ev.size) :=
            fun w ev o h1 h2 => ih.roundtrip_off w ev data o h1 h2
          have hslice : data.extract off (off + (encd.foldl (·++·) ByteArray.empty).size) = encd.foldl (·++·) ByteArray.empty := by
            rw [← hpack]; exact hdata
          rw [decodeStaticElemsGo_concat e data (foldABIType DecoderEntry e) hdec vals encd 0 n off []
                (by omega) (by rw [← helem]; exact hEL) hslice]
          rw [show off + (encd.foldl (·++·) ByteArray.empty).size = off + enc.size from by rw [hpack]]
          rfl
    · rw [if_pos (by simpa using hlen)] at henc
      exact absurd (show Except.error (Error.arrayElemCount n vals.length) = Except.ok enc from henc) (by simp)
  | uint _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | int _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | bool _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | bytes _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | string _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | address _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | tuple _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)

/-- Roundtrip for dynamic array `array e` (static-element branch proven; dynamic element branch pending). -/
theorem roundtrip_off_array (e : ABIType) (ih : RoundtripVisitor e)
    (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode (.array e) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.array e) data off = Except.ok (v, off + enc.size) := by
  cases v with
  | array vals =>
    unfold encode foldABIType at henc
    delta instABIVisitorEncoderEntry at henc
    rcases hentry : foldABIType EncoderEntry e with ⟨elemDyn, elemEnc⟩
    rw [hentry] at henc
    dsimp at henc
    have helem : elemEnc = encode e := by unfold encode; rw [hentry]
    split at henc
    · rename_i hlt
      cases hEL : encodeListElems elemEnc vals with
      | error x => rw [hEL] at henc; exact absurd (show Except.error x = Except.ok enc from henc) (by simp)
      | ok encd =>
        rw [hEL] at henc
        have hpack : enc = uint256ToBytes vals.length ++ arrayPack elemDyn encd :=
          (Except.ok.inj (show Except.ok (uint256ToBytes vals.length ++ arrayPack elemDyn encd) = Except.ok enc from henc)).symm
        have hPsz : (uint256ToBytes vals.length).size = 32 :=
          uint256ToBytes_size vals.length (natToBytes_size_bound vals.length hlt)
        set packed := arrayPack elemDyn encd with hpk
        have hencsz : enc.size = 32 + packed.size := by rw [hpack, ByteArray.size_append, hPsz]
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
          rw [← e0, hdata, hpack]
          exact ByteArray.extract_append_eq_right hPsz.symm (by rw [hPsz])
        unfold decode foldABIType
        delta instABIVisitorDecoderEntry
        dsimp
        rw [if_neg hb32]
        simp only [hlen]
        cases hdyn : isDynamic e with
        | true =>
          -- FALSE AS STATED (no size precondition). With dynamic elements the decoder reads
          -- 32-byte head pointers, but `arrayPack` computes offsets assuming `headAreaSize = n*32`
          -- (Encode.lean:35). Each element encodes with size < 2^256, yet their sizes can sum past
          -- 2^256, so a written pointer `uint256ToBytes offset` becomes >32 bytes, corrupting the
          -- head/tail layout. Provable only under `enc.size < 2^256` (all offsets fit in 32 bytes).
          sorry
        | false =>
          have helemF : elemDyn = false := by
            have h := enc_fst_eq_isDynamic e; rw [hentry] at h; simp only [] at h; rw [h, hdyn]
          have hpackstatic : packed = encd.foldl (·++·) ByteArray.empty := by rw [hpk, helemF]; simp [arrayPack]
          simp only [decodeArrayElems, decodeStaticElems, Bool.false_eq_true, if_false]
          have hdec : ∀ (w : ABIValue) (ev : ByteArray) (o : Nat),
              encode e w = Except.ok ev → data.extract o (o + ev.size) = ev →
              (foldABIType DecoderEntry e) data o = Except.ok (w, o + ev.size) :=
            fun w ev o h1 h2 => ih.roundtrip_off w ev data o h1 h2
          have hslice : data.extract (off + 32) ((off + 32) + (encd.foldl (·++·) ByteArray.empty).size) = encd.foldl (·++·) ByteArray.empty := by
            rw [← hpackstatic]; exact hsuffix
          rw [decodeStaticElemsGo_concat e data (foldABIType DecoderEntry e) hdec vals encd 0 vals.length (off + 32) []
                (by omega) (by rw [← helem]; exact hEL) hslice]
          rw [show (off + 32) + (encd.foldl (·++·) ByteArray.empty).size = off + enc.size from by rw [← hpackstatic, hencsz]; omega]
          rfl
    · exact absurd (show Except.error (Error.arrayLengthOverflow vals.length) = Except.ok enc from henc) (by simp)
  | uint _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | int _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | bool _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | bytes _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | string _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | address _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)
  | tuple _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry e with ⟨d, f⟩; dsimp; simp)

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

/-- Size of the static tuple packing = `headSize`. -/
theorem tuplePackStatic_size : ∀ {ts : List ABIType} (all : All RoundtripVisitor ts),
    (∀ t ∈ ts, isDynamic t = false) → ∀ (vs : List ABIValue) (encd : List (Bool × ByteArray)),
    instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd →
    (encd.foldl (fun acc x => acc ++ x.2) ByteArray.empty).size = headSize (.tuple ts) := by
  intro ts all
  induction all with
  | nil =>
    intro _ vs encd hgo
    simp only [foldAll] at hgo
    cases vs with
    | nil => rw [show encd = [] from (Except.ok.inj (show Except.ok [] = Except.ok encd from hgo)).symm]; simp [headSize]
    | cons v vs => exact absurd (show Except.error Error.typeValueMismatch = Except.ok encd from hgo) (by simp)
  | @cons t ts' a rest ih =>
    intro hstat vs encd hgo
    simp only [foldAll] at hgo
    rcases hentry : foldABIType EncoderEntry t with ⟨dyn, enc⟩
    rw [hentry] at hgo
    obtain ⟨v, vs', b, tail, rfl, hb, htail, rfl⟩ := go_cons_ok dyn enc (foldAll EncoderEntry ts') vs encd hgo
    have henc_t : enc = encode t := by unfold encode; rw [hentry]
    have hbsz : b.size = headSize t := a.size_eq (hstat t (by simp)) v b (by rw [← henc_t]; exact hb)
    rw [ba_foldl_snd_cons, ByteArray.size_append, hbsz,
        ih (fun t' ht' => hstat t' (List.mem_cons_of_mem t ht')) vs' tail htail, headSize_tuple_cons]

theorem size_eq_tuple {ts : List ABIType} (all : All RoundtripVisitor ts) :
    isDynamic (.tuple ts) = false → ∀ (v : ABIValue) (ev : ByteArray),
    encode (.tuple ts) v = Except.ok ev → ev.size = headSize (.tuple ts) := by
  intro hstat v ev henc
  cases v with
  | tuple vs =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    cases hgo : instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs with
    | error x => rw [hgo] at henc; exact absurd (show Except.error x = Except.ok ev from henc) (by simp)
    | ok encd =>
      rw [hgo] at henc
      have hev : ev = tuplePack (ts.map headSize) (ts.map isDynamic) encd :=
        (Except.ok.inj (show Except.ok (tuplePack (ts.map headSize) (ts.map isDynamic) encd) = Except.ok ev from henc)).symm
      have hany : (ts.map isDynamic).any id = false := by rw [tuple_any_isDynamic]; exact hstat
      rw [hev, tuplePack_static _ _ _ hany]
      exact tuplePackStatic_size all (tuple_static_elems ts hstat) vs encd hgo
  | uint _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  | int _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  | bool _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  | bytes _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  | string _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  | address _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  | array _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)

theorem size_eq_fixedArray (n : Nat) (e : ABIType) (ih : RoundtripVisitor e) :
    isDynamic (.fixedArray n e) = false → ∀ (v : ABIValue) (ev : ByteArray),
    encode (.fixedArray n e) v = Except.ok ev → ev.size = headSize (.fixedArray n e) := by
  intro hstat v ev henc
  have hstat_e : isDynamic e = false := by simpa [isDynamic] using hstat
  exact size_eq_fixedArray_core n e (fun v ev h => ih.size_eq hstat_e v ev h) hstat_e v ev henc

/-! ## Static tuple roundtrip -/

theorem headSize_foldl_init (init : Nat) (ts : List ABIType) :
    ts.foldl (fun acc t => acc + headSize t) init = init + headSize (.tuple ts) := by
  induction ts generalizing init with
  | nil => simp [headSize]
  | cons t ts ih => simp only [List.foldl_cons, ih, headSize_tuple_cons]; omega

theorem headSize_tuple_foldl (ts : List ABIType) :
    ts.foldl (fun acc t => acc + headSize t) 0 = headSize (.tuple ts) := by
  rw [headSize_foldl_init]; simp

theorem decodeTupleStatic_nil (data : ByteArray) (off : Nat) (acc : List ABIValue) :
    decodeTupleStatic (All.nil : All DecoderEntry []) data off acc = Except.ok (acc.reverse, off) := rfl

theorem decodeTupleStatic_cons {t : ABIType} {ts' : List ABIType} (dec' : DecoderEntry t)
    (rest : All DecoderEntry ts') (data : ByteArray) (off : Nat) (acc : List ABIValue) :
    decodeTupleStatic (All.cons dec' rest) data off acc
      = (dec' data off >>= fun x => decodeTupleStatic rest data x.2 (x.1 :: acc)) := rfl

/-- Decoding the concatenation of a statically-packed tuple recovers the values. -/
theorem decodeTupleStatic_concat {ts : List ABIType} (all : All RoundtripVisitor ts) (data : ByteArray) :
    ∀ (vs : List ABIValue) (encd : List (Bool × ByteArray)) (off : Nat) (acc : List ABIValue),
    (∀ t ∈ ts, isDynamic t = false) →
    instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd →
    data.extract off (off + (encd.foldl (fun a x => a ++ x.2) ByteArray.empty).size) = encd.foldl (fun a x => a ++ x.2) ByteArray.empty →
    decodeTupleStatic (foldAll DecoderEntry ts) data off acc = Except.ok (acc.reverse ++ vs, off + (encd.foldl (fun a x => a ++ x.2) ByteArray.empty).size) := by
  induction all with
  | nil =>
    intro vs encd off acc _ hgo hslice
    simp only [foldAll] at hgo ⊢
    cases vs with
    | nil =>
      rw [show encd = [] from (Except.ok.inj (show Except.ok [] = Except.ok encd from hgo)).symm]
      simp only [List.foldl_nil, ByteArray.size_empty, Nat.add_zero, List.append_nil]
      rw [decodeTupleStatic_nil]
    | cons v vs => exact absurd (show Except.error Error.typeValueMismatch = Except.ok encd from hgo) (by simp)
  | @cons t ts' a rest ih =>
    intro vs encd off acc hstat hgo hslice
    simp only [foldAll] at hgo
    rcases hentry : foldABIType EncoderEntry t with ⟨dyn, enc⟩
    rw [hentry] at hgo
    obtain ⟨v, vs', b, tail, rfl, hb, htail, rfl⟩ := go_cons_ok dyn enc (foldAll EncoderEntry ts') vs encd hgo
    have henc_t : enc = encode t := by unfold encode; rw [hentry]
    rw [ba_foldl_snd_cons] at hslice ⊢
    simp only [] at hslice ⊢
    have hsz : (b ++ tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size = b.size + (tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size := ByteArray.size_append
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
      a.roundtrip_off v b data off (by rw [← henc_t]; exact hb) hslice_b
    simp only [foldAll]
    rw [decodeTupleStatic_cons, hdec_t]
    show decodeTupleStatic (foldAll DecoderEntry ts') data (off + b.size) (v :: acc) = _
    rw [ih vs' tail (off + b.size) (v :: acc) (fun t' ht' => hstat t' (List.mem_cons_of_mem t ht')) htail hslice_tail]
    have h1 : (v :: acc).reverse ++ vs' = acc.reverse ++ v :: vs' := by simp
    have h2 : off + b.size + (tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size = off + (b ++ tail.foldl (fun a x => a ++ x.2) ByteArray.empty).size := by rw [hsz]; omega
    rw [h1, h2]

/-- Roundtrip for tuple (static branch proven; dynamic branch pending). -/
theorem roundtrip_off_tuple {ts : List ABIType} (all : All RoundtripVisitor ts)
    (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (henc : encode (.tuple ts) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.tuple ts) data off = Except.ok (v, off + enc.size) := by
  cases v with
  | tuple vs =>
    unfold encode foldABIType at henc; delta instABIVisitorEncoderEntry at henc; dsimp at henc
    cases hgo : instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs with
    | error x => rw [hgo] at henc; exact absurd (show Except.error x = Except.ok enc from henc) (by simp)
    | ok encd =>
      rw [hgo] at henc
      have hpack : enc = tuplePack (ts.map headSize) (ts.map isDynamic) encd :=
        (Except.ok.inj (show Except.ok (tuplePack (ts.map headSize) (ts.map isDynamic) encd) = Except.ok enc from henc)).symm
      unfold decode foldABIType; delta instABIVisitorDecoderEntry; dsimp
      cases hdyn : ts.any isDynamic with
      | true =>
        -- FALSE AS STATED (no size precondition), same root cause as the dynamic array case:
        -- `tuplePack` writes 32-byte head pointers (Encode.lean:54) assuming each dynamic field's
        -- offset fits in 32 bytes, but a successful encode can produce offsets ≥ 2^256, so
        -- `uint256ToBytes offset` exceeds 32 bytes and the head/tail layout no longer matches what
        -- `decodeTupleDynamic` reads. Provable only under a well-formedness bound `enc.size < 2^256`.
        sorry
      | false =>
        have hstat : isDynamic (.tuple ts) = false := by rw [← tuple_any_isDynamic]; simpa using hdyn
        have hany : (ts.map isDynamic).any id = false := by rw [tuple_any_isDynamic]; exact hstat
        have hslice : data.extract off (off + (encd.foldl (fun a x => a ++ x.2) ByteArray.empty).size) = encd.foldl (fun a x => a ++ x.2) ByteArray.empty := by
          rw [← tuplePack_static (ts.map headSize) (ts.map isDynamic) encd hany, ← hpack]; exact hdata
        have hsize : enc.size = headSize (.tuple ts) := by
          rw [hpack, tuplePack_static _ _ _ hany]; exact tuplePackStatic_size all (tuple_static_elems ts hstat) vs encd hgo
        have hoff : ts.foldl (fun acc t => acc + headSize t) 0 = enc.size := by rw [hsize, headSize_tuple_foldl]
        simp only [Bool.not_false, if_true]
        rw [decodeTupleStatic_concat all data vs encd off [] (tuple_static_elems ts hstat) hgo hslice]
        show Except.ok (ABIValue.tuple ([].reverse ++ vs), off + ts.foldl (fun acc t => acc + headSize t) 0) = Except.ok (ABIValue.tuple vs, off + enc.size)
        simp only [List.reverse_nil, List.nil_append, hoff]
  | uint _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  | int _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  | bool _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  | bytes _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  | string _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  | address _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)
  | array _ => exact absurd henc (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp)

/-! ## ABIVisitor instance -/

instance : ABIVisitor RoundtripVisitor where
  onUint s := ⟨roundtrip_off_uint s, fun _ => size_eq_uint s⟩
  onInt s := ⟨roundtrip_off_int s, fun _ => size_eq_int s⟩
  onBool := ⟨roundtrip_off_bool, fun _ => size_eq_bool⟩
  onAddress := ⟨roundtrip_off_address, fun _ => size_eq_address⟩
  onFixedBytes s := ⟨roundtrip_off_fixedBytes s, fun _ => size_eq_fixedBytes s⟩
  onBytes := ⟨roundtrip_off_bytes, fun h => by simp [isDynamic] at h⟩
  onString := ⟨roundtrip_off_string, fun h => by simp [isDynamic] at h⟩
  onArray {e} ih := ⟨roundtrip_off_array e ih, fun h => by simp [isDynamic] at h⟩
  onFixedArray n {e} ih := ⟨roundtrip_off_fixedArray n e ih, size_eq_fixedArray n e ih⟩
  onTuple {ts} all := ⟨roundtrip_off_tuple all, size_eq_tuple all⟩

theorem roundtrip (t : ABIType) (v : ABIValue) (data : ByteArray)
    (henc : encode t v = Except.ok data) : decode t data 0 = Except.ok (v, data.size) :=
  (foldABIType RoundtripVisitor t).roundtrip v data henc

/-! ## Dynamic-element groundwork (for the well-formedness-conditioned roundtrip)

The dynamic-element roundtrips (dyn array/fixedArray/tuple) are false as stated (see the
documented `sorry`s in the visitor): an encode can succeed while producing head pointers
`≥ 2^256`, which `uint256ToBytes` renders as >32-byte heads, corrupting the layout the decoder
relies on. Under a well-formedness bound (`enc.size < 2^256`, so every offset fits in 32 bytes)
they hold. The lemmas below are the verified core of that argument — in particular
`ddeg_concat`, which shows `decodeDynamicElemsGo` recovers the values from the head/tail layout.
Wiring these into a WF-conditioned visitor (plus an element-alignment `szdvd` fact and the
`decodeTupleDynamic` analogue) remains; see the `abi-lean-roundtrip-status` note. -/

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
    (hdvd : ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode e v = Except.ok ev → 32 ∣ ev.size) :
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
