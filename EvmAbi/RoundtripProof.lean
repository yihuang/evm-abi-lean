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

/-! ## Foundational lemmas (currently unproven) -/

theorem bytesToNat_append_singleton (b : UInt8) (acc : ByteArray) :
    bytesToNat (mkSingleton b ++ acc) = b.toNat * 256 ^ acc.size + bytesToNat acc := by
  sorry

theorem pad_const (k : Nat) : bytesToNat (zeros k ++ (natToBytes v)) = bytesToNat (natToBytes v) := by
  sorry

theorem bytesToNat_natToBytes (v : Nat) : bytesToNat (natToBytes v) = v := by
  sorry

theorem bytesToNat_uint256ToBytes (v : Nat) (hv : v < 2 ^ 256) : bytesToNat (uint256ToBytes v) = v := by
  sorry

/-- Extracting the first b.size bytes of (b ++ c) gives b. -/
theorem extract_first_n (b c : ByteArray) : (b ++ c).extract 0 b.size = b := by
  apply ByteArray.ext; simp

theorem padRight_extract_eq (b : ByteArray) (sz : Nat) (hsz : b.size = sz) : (padRight b 32).extract 0 sz = b := by
  subst hsz
  unfold padRight; split
  · exact extract_self b
  · rename_i h_not
    have h_lt : b.size < 32 := by omega
    exact extract_first_n b (zeros (32 - b.size))

theorem padLeft_extract_address (b : ByteArray) (h20 : b.size = 20) : (padLeft b 32).extract 12 32 = b := by
  sorry

---- Main roundtrip theorem ----

theorem roundtrip (t : ABIType) (v : ABIValue) (data : ByteArray) (henc : encode t v = Except.ok data) :
    decode t data 0 = Except.ok (v, data.size) := by
  have henc_tv : encode t v = Except.ok data := henc
  cases t
  case uint bits =>
    cases v
    case uint v' =>
      by_cases hm : 2 ^ bits.val ≤ v'
      · unfold encode at henc_tv; dsimp at henc_tv; rw [if_pos hm] at henc_tv; simp at henc_tv
      · unfold encode at henc_tv; dsimp at henc_tv; rw [if_neg hm] at henc_tv; simp at henc_tv
        have hdata : data = uint256ToBytes v' := henc_tv.symm
        have hrange : v' < 2 ^ bits.val := by omega
        have hv256 : v' < 2 ^ 256 := by
          have hbits256 : bits.val ≤ 256 := by
            cases bits <;> decide
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
    case int v' => simp [encode] at henc_tv
    case bool v' => simp [encode] at henc_tv
    case bytes v' => simp [encode] at henc_tv
    case string v' => simp [encode] at henc_tv
    case address v' => simp [encode] at henc_tv
    case array vals => simp [encode] at henc_tv
    case tuple vals => simp [encode] at henc_tv
  case int bits =>
    cases v
    case int v' => sorry
    case uint v' => simp [encode] at henc_tv
    case bool v' => simp [encode] at henc_tv
    case bytes v' => simp [encode] at henc_tv
    case string v' => simp [encode] at henc_tv
    case address v' => simp [encode] at henc_tv
    case array vals => simp [encode] at henc_tv
    case tuple vals => simp [encode] at henc_tv
  case bool =>
    cases v
    case bool v' =>
      simp [encode] at henc_tv
      have hdata : data = uint256ToBytes (if v' then 1 else 0) := henc_tv.symm
      have hbits : (if v' then 1 else 0) < 2 ^ 256 := by split <;> omega
      have hsize32 : (uint256ToBytes (if v' then 1 else 0)).size = 32 :=
        uint256ToBytes_size (if v' then 1 else 0) (natToBytes_size_bound (if v' then 1 else 0) hbits)
      have h_val : bytesToNat ((uint256ToBytes (if v' then 1 else 0)).extract 0 32) = (if v' then 1 else 0) := by
        calc
          bytesToNat ((uint256ToBytes (if v' then 1 else 0)).extract 0 32) = bytesToNat (uint256ToBytes (if v' then 1 else 0)) := by
            rw [← hsize32, extract_self]
          _ = (if v' then 1 else 0) := bytesToNat_uint256ToBytes (if v' then 1 else 0) hbits
      unfold decode; rw [hdata]; simp [hsize32, h_val]; cases v' <;> simp
    case uint v' => simp [encode] at henc_tv
    case int v' => simp [encode] at henc_tv
    case bytes v' => simp [encode] at henc_tv
    case string v' => simp [encode] at henc_tv
    case address v' => simp [encode] at henc_tv
    case array vals => simp [encode] at henc_tv
    case tuple vals => simp [encode] at henc_tv
  case bytesM sz =>
    cases v
    case bytes v' => sorry
    case uint v' => simp [encode] at henc_tv
    case int v' => simp [encode] at henc_tv
    case bool v' => simp [encode] at henc_tv
    case string v' => simp [encode] at henc_tv
    case address v' => simp [encode] at henc_tv
    case array vals => simp [encode] at henc_tv
    case tuple vals => simp [encode] at henc_tv
  case address =>
    cases v
    case address v' => sorry
    case uint v' => simp [encode] at henc_tv
    case int v' => simp [encode] at henc_tv
    case bool v' => simp [encode] at henc_tv
    case bytes v' => simp [encode] at henc_tv
    case string v' => simp [encode] at henc_tv
    case array vals => simp [encode] at henc_tv
    case tuple vals => simp [encode] at henc_tv
  case bytes =>
    cases v
    case bytes v' => sorry
    case uint v' => simp [encode] at henc_tv
    case int v' => simp [encode] at henc_tv
    case bool v' => simp [encode] at henc_tv
    case string v' => simp [encode] at henc_tv
    case address v' => simp [encode] at henc_tv
    case array vals => simp [encode] at henc_tv
    case tuple vals => simp [encode] at henc_tv
  case string =>
    cases v
    case string v' => sorry
    case uint v' => simp [encode] at henc_tv
    case int v' => simp [encode] at henc_tv
    case bool v' => simp [encode] at henc_tv
    case bytes v' => simp [encode] at henc_tv
    case address v' => simp [encode] at henc_tv
    case array vals => simp [encode] at henc_tv
    case tuple vals => simp [encode] at henc_tv
  case array elemType sizeOpt =>
    cases v
    case array vals => sorry
    case uint v' => simp [encode] at henc_tv
    case int v' => simp [encode] at henc_tv
    case bool v' => simp [encode] at henc_tv
    case bytes v' => simp [encode] at henc_tv
    case string v' => simp [encode] at henc_tv
    case address v' => simp [encode] at henc_tv
    case tuple vals => simp [encode] at henc_tv
  case tuple elems =>
    cases v
    case tuple vals => sorry
    case uint v' => simp [encode] at henc_tv
    case int v' => simp [encode] at henc_tv
    case bool v' => simp [encode] at henc_tv
    case bytes v' => simp [encode] at henc_tv
    case string v' => simp [encode] at henc_tv
    case address v' => simp [encode] at henc_tv
    case array vals => simp [encode] at henc_tv
