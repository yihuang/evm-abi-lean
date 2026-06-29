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

theorem roundtrip_int (s : ByteSize) (v' : Int) (data : ByteArray)
    (henc : encode (.int s) (ABIValue.int v') = Except.ok data) : decode (.int s) data 0 = Except.ok (ABIValue.int v', data.size) := by
  sorry

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
  sorry

theorem roundtrip_string (v : ABIValue) (data : ByteArray)
    (henc : encode .string v = Except.ok data) : decode .string data 0 = Except.ok (v, data.size) := by
  sorry

/-! ## Int helper lemmas -/

private theorem intToBytes_decode_nonneg (s : ByteSize) (v' : Int) (hv_nonneg : v' ≥ 0)
    (hrange : v' < (2 ^ (s.len * 8 - 1) : Int)) (hbits256 : s.len * 8 ≤ 256) :
    decode (.int s) (intToBytes v' s.len) 0 = Except.ok (ABIValue.int v', (intToBytes v' s.len).size) := by
  sorry

private theorem intToBytes_decode_neg (s : ByteSize) (v' : Int) (hv_neg : ¬ v' ≥ 0)
    (hrange : -(2 ^ (s.len * 8 - 1) : Int) ≤ v') (hbits256 : s.len * 8 ≤ 256) :
    decode (.int s) (intToBytes v' s.len) 0 = Except.ok (ABIValue.int v', (intToBytes v' s.len).size) := by
  sorry

theorem decode_intToBytes (s : ByteSize) (v' : Int)
    (hrange : -(2 ^ (s.len * 8 - 1) : Int) ≤ v' ∧ v' < (2 ^ (s.len * 8 - 1) : Int)) :
    decode (.int s) (intToBytes v' s.len) 0 = Except.ok (ABIValue.int v', (intToBytes v' s.len).size) := by
  sorry

/-! ## Dynamic bytes/string helpers -/

private lemma dynamicRoundtrip_preamble (b : ByteArray) (hb256 : b.size < 2 ^ 256) :
    (uint256ToBytes b.size).size = 32 ∧ (padRight b (roundUp32 b.size)).size = roundUp32 b.size ∧
    b.size ≤ roundUp32 b.size ∧ (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).size = 32 + roundUp32 b.size ∧
    bytesToNat ((uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 0 32) = b.size ∧
    (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 32 (32 + b.size) = b := by
  sorry

private lemma decodeDynamicBytes_roundtrip (v' : ByteArray) (hv256 : v'.size < 2 ^ 256) (data : ByteArray)
    (hdata : data = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)) :
    decodeDynamicBytes data 0 = Except.ok (.bytes v', data.size) := by
  sorry

private lemma decodeDynamicString_roundtrip (v' : String) (hv256 : v'.toUTF8.size < 2 ^ 256) (data : ByteArray)
    (hdata : data = uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size)) :
    decodeDynamicString data 0 = Except.ok (.string v', data.size) := by
  sorry

/-! ## ABIVisitor instance -/

instance : ABIVisitor RoundtripVisitor where
  onUint s := ⟨roundtrip_uint s⟩
  onInt s := ⟨λ v data henc => by
    match v with
    | .int v' => exact roundtrip_int s v' data henc
    | x => sorry⟩
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
