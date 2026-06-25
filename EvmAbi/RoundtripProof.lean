/-
# Universal Roundtrip Theorem: encode ∘ decode = id
-/

import EvmAbi.ABI
import EvmAbi.Encode
import EvmAbi.Decode

open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode
set_option linter.unusedVariables false

def mkSingleton (b : UInt8) : ByteArray := { data := Array.mk [b] }

theorem mkSingleton_size (b : UInt8) : (mkSingleton b).size = 1 := by
  unfold mkSingleton ByteArray.size; simp

theorem extract_self (b : ByteArray) : b.extract 0 b.size = b := by
  rcases b with ⟨arr⟩; simp

theorem zeros_size (k : Nat) : (zeros k).size = k := by
  unfold zeros; induction k with
  | zero => rfl
  | succ k ih =>
    calc
      (ByteArray.mk (Array.mk (List.replicate (k+1) zeroByte))).size = (Array.mk (List.replicate (k+1) zeroByte)).size := rfl
      _ = (Array.mk (List.replicate (k+1) zeroByte)).toList.length := rfl
      _ = (List.replicate (k+1) zeroByte).length := rfl
      _ = k + 1 := by simp

theorem uint256ToBytes_size (v : Nat) (hv : (natToBytes v).size ≤ 32) : (uint256ToBytes v).size = 32 := by
  unfold uint256ToBytes padLeft; split
  · omega
  · simp [zeros_size]; omega

def numBytes (n : Nat) : Nat :=
  if n = 0 then 0 else 1 + numBytes (n / 256)
termination_by n
decreasing_by
  apply Nat.div_lt_self; omega; decide

theorem numBytes_lt_pow (n : Nat) (k : Nat) (hn : n < 256 ^ k) : numBytes n ≤ k := by
  induction k generalizing n
  case zero =>
    have hn' : n < 1 := by simpa using hn
    have h0 : n = 0 := by omega
    subst h0; simp [numBytes]
  case succ k ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [numBytes]
    · unfold numBytes; simp [hn0]
      have hn_mul : n < 256 * 256 ^ k := by
        calc
          n < 256 ^ (k+1) := hn
          _ = 256 ^ k * 256 := by simp [Nat.pow_succ]
          _ = 256 * 256 ^ k := by omega
      have hdiv_lt : n / 256 < 256 ^ k := Nat.div_lt_of_lt_mul hn_mul
      have h_ih := ih (n / 256) hdiv_lt; omega


theorem numBytes_bound (n : Nat) (hn : n < 2 ^ 256) : numBytes n ≤ 32 := by
  have h256_eq : 2 ^ 256 = 256 ^ 32 := by native_decide
  have hn' : n < 256 ^ 32 := by simpa [h256_eq] using hn
  exact numBytes_lt_pow n 32 hn'

theorem size_go (n : Nat) (acc : ByteArray) : (natToBytes.go n acc).size = numBytes n + acc.size := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ihn =>
    unfold natToBytes.go numBytes; split
    · simp
    · rename_i hn
      have hdiv : n / 256 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1 < 256)
      have h_sz : ({ data := Array.mk [((n % 256).toUInt8)] } ++ acc).size = 1 + acc.size := by
        have h1 : ({ data := Array.mk [((n % 256).toUInt8)] } : ByteArray).size = 1 := by
          calc
            ({ data := Array.mk [((n % 256).toUInt8)] } : ByteArray).size = (Array.mk [((n % 256).toUInt8)]).size := rfl
            _ = (Array.mk [((n % 256).toUInt8)]).toList.length := rfl
            _ = [((n % 256).toUInt8)].length := rfl
            _ = 1 := by simp
        simp [h1]
      have h_ih' : (natToBytes.go (n / 256) ({ data := Array.mk [((n % 256).toUInt8)] } ++ acc)).size =
          numBytes (n / 256) + (1 + acc.size) := by
        have h1 := ihn (n / 256) hdiv ({ data := Array.mk [((n % 256).toUInt8)] } ++ acc)
        rw [h_sz] at h1
        exact h1
      rw [h_ih']; omega

theorem natToBytes_size_bound (v : Nat) (hv : v < 2 ^ 256) : (natToBytes v).size ≤ 32 := by
  unfold natToBytes; split
  · native_decide
  · rename_i hv0
    have h_sz : (natToBytes.go v ByteArray.empty).size = numBytes v := by
      simpa using size_go v ByteArray.empty
    rw [h_sz]; exact numBytes_bound v hv

/-! ## Foundational lemmas -/

theorem list_foldl_shift (xs : List UInt8) (x : Nat) :
    xs.foldl (fun acc byte => acc * 256 + byte.toNat) x = x * 256 ^ xs.length + xs.foldl (fun acc byte => acc * 256 + byte.toNat) 0 := by
  induction xs generalizing x with
  | nil => simp
  | cons h t ih =>
    simp
    rw [ih (x * 256 + h.toNat), ih (h.toNat)]
    rw [Nat.add_mul, Nat.pow_succ]
    have h : x * 256 * (256 ^ t.length) = x * ((256 ^ t.length) * 256) := by
      calc
        x * 256 * (256 ^ t.length) = x * (256 * (256 ^ t.length)) := by simp [Nat.mul_assoc]
        _ = x * ((256 ^ t.length) * 256) := by simp [Nat.mul_comm 256 (256 ^ t.length)]
    rw [h]
    omega

theorem bytesToNat_append_singleton (b : UInt8) (acc : ByteArray) :
    bytesToNat (mkSingleton b ++ acc) = b.toNat * 256 ^ acc.size + bytesToNat acc := by
  calc
    bytesToNat (mkSingleton b ++ acc) = bytesToNat_list ((mkSingleton b ++ acc).data.toList) := rfl
    _ = bytesToNat_list ((mkSingleton b).data.toList ++ acc.data.toList) := by rw [ByteArray.toList_data_append]
    _ = bytesToNat_list (b :: acc.data.toList) := by simp [mkSingleton]
    _ = acc.data.toList.foldl (fun acc byte => acc * 256 + byte.toNat) (b.toNat) := by
      simp [bytesToNat_list]
    _ = b.toNat * 256 ^ acc.data.toList.length + acc.data.toList.foldl (fun acc byte => acc * 256 + byte.toNat) 0 :=
      list_foldl_shift (acc.data.toList) (b.toNat)
    _ = b.toNat * 256 ^ acc.size + acc.data.toList.foldl (fun acc byte => acc * 256 + byte.toNat) 0 := by simp
    _ = b.toNat * 256 ^ acc.size + bytesToNat_list acc.data.toList := rfl
    _ = b.toNat * 256 ^ acc.size + bytesToNat acc := rfl

theorem bytesToNat_go (n : Nat) (acc : ByteArray) : bytesToNat (natToBytes.go n acc) = n * 256 ^ acc.size + bytesToNat acc := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ihn =>
    unfold natToBytes.go; split
    · rename_i hzero
      subst hzero; simp
    · rename_i hn
      have hdiv : n / 256 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1 < 256)
      let b := (mkSingleton ((n % 256).toUInt8) ++ acc)
      have h_sz : b.size = 1 + acc.size := by
        unfold b
        simp [mkSingleton_size]
      have h_byt : bytesToNat b = (n % 256) * 256 ^ acc.size + bytesToNat acc := by
        unfold b
        rw [bytesToNat_append_singleton ((n % 256).toUInt8) acc]
        simp
      have h_ih' := ihn (n / 256) hdiv b
      have h_pow : 256 ^ (1 + acc.size) = 256 * 256 ^ acc.size := by
        calc
          256 ^ (1 + acc.size) = 256 ^ (acc.size + 1) := by simp [Nat.add_comm]
          _ = 256 ^ acc.size * 256 := by simp [Nat.pow_succ]
          _ = 256 * 256 ^ acc.size := by simp [Nat.mul_comm]
      calc
        bytesToNat (natToBytes.go (n / 256) b) = (n / 256) * 256 ^ b.size + bytesToNat b := h_ih'
        _ = (n / 256) * 256 ^ (1 + acc.size) + ((n % 256) * 256 ^ acc.size + bytesToNat acc) := by rw [h_sz, h_byt]
        _ = ((n / 256) * (256 * 256 ^ acc.size) + (n % 256) * 256 ^ acc.size) + bytesToNat acc := by
          rw [h_pow, Nat.add_assoc]
        _ = ((n / 256) * 256 * 256 ^ acc.size + (n % 256) * 256 ^ acc.size) + bytesToNat acc := by
          simp [Nat.mul_assoc]
        _ = (((n / 256) * 256 + (n % 256)) * 256 ^ acc.size) + bytesToNat acc := by
          rw [← Nat.add_mul]
        _ = n * 256 ^ acc.size + bytesToNat acc := by
          have h_divmod : (n / 256) * 256 + (n % 256) = n := by omega
          rw [h_divmod]

theorem bytesToNat_natToBytes (v : Nat) : bytesToNat (natToBytes v) = v := by
  unfold natToBytes; split
  · rename_i hzero; subst hzero; unfold bytesToNat bytesToNat_list; simp [zeroByte]
  · have h := bytesToNat_go v ByteArray.empty
    simpa [show (ByteArray.empty : ByteArray).size = 0 from by decide, show bytesToNat (ByteArray.empty : ByteArray) = 0 from by decide] using h

theorem bytesToNat_padLeft (b : ByteArray) (n : Nat) : bytesToNat (padLeft b n) = bytesToNat b := by
  unfold padLeft; split
  · rfl
  · unfold zeros bytesToNat bytesToNat_list
    rw [ByteArray.toList_data_append, List.foldl_append]
    have hz : List.foldl (fun (acc : Nat) (b : UInt8) => acc * 256 + b.toNat) 0
        (List.replicate (n - b.size) zeroByte) = 0 := by
      induction (n - b.size) with
      | zero => simp
      | succ k ih =>
        calc
          List.foldl (fun acc b => acc * 256 + b.toNat) 0 (List.replicate (k + 1) zeroByte)
              = List.foldl (fun acc b => acc * 256 + b.toNat) 0 (zeroByte :: List.replicate k zeroByte) := by
            simp [List.replicate]
          _ = List.foldl (fun acc b => acc * 256 + b.toNat) (0 * 256 + zeroByte.toNat) (List.replicate k zeroByte) := by
            simp [List.foldl]
          _ = List.foldl (fun acc b => acc * 256 + b.toNat) 0 (List.replicate k zeroByte) := by simp [zeroByte]
          _ = 0 := ih
    have hlist : ({ data := Array.mk (List.replicate (n - b.size) zeroByte) } : ByteArray).data.toList =
        List.replicate (n - b.size) zeroByte := by simp
    rw [hlist, hz]
theorem bytesToNat_uint256ToBytes (v : Nat) (hv : v < 2 ^ 256) : bytesToNat (uint256ToBytes v) = v := by
  unfold uint256ToBytes
  rw [bytesToNat_padLeft, bytesToNat_natToBytes v]

/-- Extracting the first b.size bytes of (b ++ c) gives b. -/
theorem extract_first_n (b c : ByteArray) : (b ++ c).extract 0 b.size = b := by
  apply ByteArray.ext; simp

theorem padRight_extract_eq (b : ByteArray) (sz : Nat) (hsz : b.size = sz) : (padRight b 32).extract 0 sz = b := by
  subst hsz
  unfold padRight; split
  · exact extract_self b
  · rename_i h_not
    have h_lt : b.size < 32 := by omega
    apply extract_first_n
theorem padLeft_extract_address (b : ByteArray) (h20 : b.size = 20) : (padLeft b 32).extract 12 32 = b := by
  have hpad : padLeft b 32 = zeros 12 ++ b := by
    unfold padLeft
    have h_not : ¬ 32 ≤ b.size := by omega
    simp [h20]
  rw [hpad]
  apply ByteArray.ext
  apply Array.ext
  · simp [h20, zeros_size 12]
  · intro i hi
    simp [h20, zeros_size 12] at hi ⊢


theorem roundtrip_uint (bits : BitSize) (v : ABIValue) (data : ByteArray) (henc : encode (.uint bits) v = Except.ok data) :
    decode (.uint bits) data 0 = Except.ok (v, data.size) := by
  cases v
  case uint v' =>
    unfold encode at henc; dsimp at henc
    by_cases hm : 2 ^ bits.val ≤ v'
    · simp [hm] at henc
    · simp [hm] at henc
      have hdata : data = uint256ToBytes v' := henc.symm
      have hrange : v' < 2 ^ bits.val := by omega
      have hv256 : v' < 2 ^ 256 := by
        have hbits256 : bits.val ≤ 256 := by cases bits <;> decide
        have : 2 ^ bits.val ≤ 2 ^ 256 := Nat.pow_le_pow_right (by omega) hbits256
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

theorem padRight_extract_self (b : ByteArray) (n : Nat) (h : b.size ≤ n) : (padRight b n).extract 0 b.size = b := by
  unfold padRight; split
  · exact extract_self b
  · exact extract_first_n b (zeros (n - b.size))

theorem extract_after_suffix (a b : ByteArray) (k : Nat) : (a ++ b).extract a.size (a.size + k) = b.extract 0 k := by
  apply ByteArray.ext; simp

theorem roundtrip_bytes_val (v' : ByteArray) (hv256 : v'.size < 2 ^ 256) :
    (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)).extract 32 (32 + v'.size) = v' := by
  have ha_sz : (uint256ToBytes v'.size).size = 32 :=
    uint256ToBytes_size v'.size (natToBytes_size_bound v'.size hv256)
  have h_val_sz : v'.size ≤ roundUp32 v'.size := by
    have : roundUp32 v'.size = ((v'.size + 31) / 32) * 32 := rfl; omega
  have h_sub : (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)).extract
    (uint256ToBytes v'.size).size ((uint256ToBytes v'.size).size + v'.size) = 
    (padRight v' (roundUp32 v'.size)).extract 0 v'.size :=
    extract_after_suffix (uint256ToBytes v'.size) (padRight v' (roundUp32 v'.size)) v'.size
  calc
    (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)).extract 32 (32 + v'.size)
        = (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)).extract
            (uint256ToBytes v'.size).size ((uint256ToBytes v'.size).size + v'.size) := by simp [ha_sz]
    _ = (padRight v' (roundUp32 v'.size)).extract 0 v'.size := h_sub
    _ = v' := padRight_extract_self v' (roundUp32 v'.size) h_val_sz

theorem roundtrip_int (bits : BitSize) (v' : Int) (data : ByteArray) (henc : encode (.int bits) (ABIValue.int v') = Except.ok data) :
    decode (.int bits) data 0 = Except.ok (ABIValue.int v', data.size) := by
  unfold encode at henc; dsimp at henc
  by_cases h1 : v' < -(2 ^ (bits.val - 1) : Int)
  · simp [h1] at henc
  · by_cases h2 : v' ≥ (2 ^ (bits.val - 1) : Int)
    · simp [h2] at henc
    · simp [h1, h2] at henc
      have hdata : data = intToBytes v' bits := henc.symm
      have hrange : -(2 ^ (bits.val - 1) : Int) ≤ v' ∧ v' < (2 ^ (bits.val - 1) : Int) := by omega
      have hbits256 : bits.val ≤ 256 := by cases bits <;> decide
      by_cases hv_nonneg : v' ≥ 0
      · have hv_lt_nat : v'.toNat < 2 ^ (bits.val - 1) := by
          apply Int.ofNat_lt.mp
          calc
            (v'.toNat : Int) = v' := by rw [Int.toNat_of_nonneg hv_nonneg]
            _ < (2 ^ (bits.val - 1) : Int) := hrange.2
        have hv_lt_256 : v'.toNat < 2 ^ 256 := by
          have : v'.toNat < 2 ^ (bits.val - 1) := hv_lt_nat
          have h_pow : 2 ^ (bits.val - 1) ≤ 2 ^ 256 :=
            Nat.pow_le_pow_right (by omega) (by omega)
          omega
        have hsize32 : (intToBytes v' bits).size = 32 := by
          calc
            (intToBytes v' bits).size = (uint256ToBytes v'.toNat).size := by
              simp [intToBytes, uint256ToBytes, hv_nonneg]
            _ = 32 := uint256ToBytes_size v'.toNat (natToBytes_size_bound v'.toNat hv_lt_256)
        have h_self : (intToBytes v' bits).extract 0 32 = intToBytes v' bits := by
          rw [← hsize32, extract_self]

        have h_val : bytesToNat ((intToBytes v' bits).extract 0 32) % 2 ^ bits.val = v'.toNat := by
          rw [h_self]
          calc
            bytesToNat (intToBytes v' bits) % 2 ^ bits.val
                = bytesToNat (uint256ToBytes v'.toNat) % 2 ^ bits.val := by
              simp [intToBytes, uint256ToBytes, hv_nonneg]
            _ = v'.toNat % 2 ^ bits.val := by
              rw [bytesToNat_uint256ToBytes v'.toNat hv_lt_256]
            _ = v'.toNat := by
              have h_lt_pow : v'.toNat < 2 ^ bits.val := by
                have h_pow : 2 ^ (bits.val - 1) ≤ 2 ^ bits.val :=
                  Nat.pow_le_pow_right (by decide) (Nat.sub_le bits.val 1)
                omega
              exact Nat.mod_eq_of_lt h_lt_pow
        unfold decode; rw [hdata]
        simp [hsize32, h_val, hv_lt_nat]
        omega
      · sorry
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
theorem fromUTF8!_toUTF8 (s : String) : String.fromUTF8! (s.toUTF8) = s := by
  have h_valid : (s.toUTF8).IsValidUTF8 := by
    refine ByteArray.IsValidUTF8.intro (s.toList) ?_
    simp
  unfold String.fromUTF8!
  rw [dif_pos h_valid]
  have h_eq_byte : s.toUTF8 = s.toByteArray := by simp
  have h_eq_valid : h_valid = s.isValidUTF8 := Subsingleton.elim _ _
  calc
    String.fromUTF8 (s.toUTF8) h_valid = String.ofByteArray (s.toUTF8) h_valid := rfl
    _ = String.ofByteArray (s.toByteArray) s.isValidUTF8 := by
      rw [h_eq_byte, h_eq_valid]
    _ = s := rfl

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
theorem roundtrip_aux (t : ABIType) (v : ABIValue) (data : ByteArray) (henc : encode t v = Except.ok data) :
    decode t data 0 = Except.ok (v, data.size) :=
  match t with
  | .uint bits => roundtrip_uint bits v data henc
  | .int bits => by
      cases v
      case int v' => exact roundtrip_int bits v' data henc
      case uint v' => simp [encode] at henc
      case bool v' => simp [encode] at henc
      case bytes v' => simp [encode] at henc
      case string v' => simp [encode] at henc
      case address v' => simp [encode] at henc
      case array _ => simp [encode] at henc
      case tuple _ => simp [encode] at henc
  | .bool => roundtrip_bool v data henc
  | .bytesM sz => by
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
          by_cases h32 : sz ≤ 32
          · have h_size : (padRight v' 32).size = 32 := by
              have h_v32 : v'.size ≤ 32 := by omega
              unfold padRight; split
              · omega
              · have h_lt : v'.size < 32 := by omega
                calc
                  (v' ++ zeros (32 - v'.size)).size = v'.size + (zeros (32 - v'.size)).size := by simp
                  _ = v'.size + (32 - v'.size) := by simp [zeros_size]
                  _ = 32 := by omega
            unfold decode; rw [hdata]; simp [h_extract, h_size]
          · sorry
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
