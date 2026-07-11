import Mathlib.Tactic
import EvmAbi.ABI
import EvmAbi.Encode
import EvmAbi.Decode

open EvmAbi.ABI

/-! ## Except helpers -/

/-- Invert a successful `Except` bind: `x >>= f = ok b` yields the intermediate `ok a`. -/
theorem bind_ok_inv {ε α β : Type _} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact absurd (show Except.error e = Except.ok b from h) (by simp)
  | ok a => exact ⟨a, rfl, h⟩

/-- Single-byte ByteArray constructor. -/
def mkSingleton (b : UInt8) : ByteArray := { data := Array.mk [b] }

/- Size of mkSingleton is always 1. -/
theorem mkSingleton_size (b : UInt8) : (mkSingleton b).size = 1 := by
  unfold mkSingleton ByteArray.size; simp

/- Extracting [0, size) from a ByteArray yields itself. -/
theorem extract_self (b : ByteArray) : b.extract 0 b.size = b := by
  rcases b with ⟨arr⟩; simp

/- zeros k produces exactly k zero bytes. -/
theorem zeros_size (k : Nat) : (zeros k).size = k := by
  simp [zeros, ByteArray.size]

/- uint256ToBytes v is always 32 bytes when natToBytes v fits in 32 bytes. -/
theorem uint256ToBytes_size (v : Nat) (hv : (natToBytes v).size ≤ 32) : (uint256ToBytes v).size = 32 := by
  unfold uint256ToBytes padLeft; split
  · omega
  · simp [zeros_size]; omega

/- Number of base-256 digits needed to represent n (0 for n=0). -/
def numBytes (n : Nat) : Nat :=
  if n = 0 then 0 else 1 + numBytes (n / 256)
termination_by n
decreasing_by
  apply Nat.div_lt_self; omega; decide

/- If n < 256^k then numBytes n ≤ k. -/
theorem numBytes_lt_pow (n : Nat) (k : Nat) (hn : n < 256 ^ k) : numBytes n ≤ k := by
  induction k generalizing n
  case zero =>
    have hn' : n < 1 := by simpa using hn
    have hn0 : n = 0 := by omega
    subst hn0; simp [numBytes]
  case succ k ih =>
    by_cases hn0 : n = 0
    · subst hn0; simp [numBytes]
    · unfold numBytes; simp [hn0]
      have hdiv_lt : n / 256 < 256 ^ k :=
        Nat.div_lt_of_lt_mul (by simpa [Nat.pow_succ, mul_comm] using hn)
      have h_ih := ih (n / 256) hdiv_lt
      simpa [add_comm] using Nat.add_le_add_right h_ih 1

/- A 256-bit value fits in at most 32 bytes. -/
theorem numBytes_bound (n : Nat) (hn : n < 2 ^ 256) : numBytes n ≤ 32 := by
  have h256_eq : 2 ^ 256 = 256 ^ 32 := by decide
  have hn' : n < 256 ^ 32 := by simpa [h256_eq] using hn
  exact numBytes_lt_pow n 32 hn'

/- If n ≥ 256^k then numBytes n ≥ k+1. -/
theorem numBytes_ge_pow (n : Nat) (k : Nat) (h : 256 ^ k ≤ n) : k + 1 ≤ numBytes n := by
  induction k generalizing n with
  | zero =>
    by_cases hn0 : n = 0
    · subst hn0; simp at h
    · unfold numBytes; simp [hn0]
  | succ k ih =>
    have hnpos : n ≠ 0 := by
      intro hzero; subst hzero; simp at h
    unfold numBytes; simp [hnpos]
    have h_div : 256 ^ k ≤ n / 256 := by
      have h_mul : 256 ^ k * 256 ≤ n := by
        simpa [Nat.pow_succ, mul_comm] using h
      have h' : (256 ^ k * 256) / 256 ≤ n / 256 :=
        Nat.div_le_div_right h_mul
      calc
        256 ^ k = (256 ^ k * 256) / 256 := by
          symm; exact Nat.mul_div_cancel (256 ^ k) (by decide : 0 < 256)
        _ ≤ n / 256 := h'
    have ih' := ih (n / 256) h_div
    omega


/- Size of the recursive natToBytes accumulator. -/
theorem size_go (n : Nat) (acc : ByteArray) : (natToBytes.go n acc).size = numBytes n + acc.size := by
  induction n, acc using natToBytes.go.induct with
  | case1 acc => simp [natToBytes.go, numBytes]
  | case2 n acc hn ih =>
    rw [natToBytes.go, if_neg hn, numBytes, if_neg hn, ih]
    have h_sz : ({ data := Array.mk [((n % 256).toUInt8)] } ++ acc).size = 1 + acc.size := by
      simp [ByteArray.size_append]; rfl
    omega

/- When 2^(8k-1) ≤ n < 2^(8k), natToBytes n has exactly k bytes. -/
theorem natToBytes_size_range (n : Nat) (k : Nat) (hk : 0 < k) (h_lo : 2 ^ (k * 8 - 1) ≤ n) (h_hi : n < 2 ^ (k * 8)) :
    (natToBytes n).size = k := by
  have h_pow_pos : 0 < 2 ^ (k * 8 - 1) :=
    Nat.pow_pos (by omega : 0 < 2) (n := k * 8 - 1)
  have h_pos : n > 0 := by omega
  have h_hi' : n < 256 ^ k := by
    calc
      n < 2 ^ (k * 8) := h_hi
      _ = 2 ^ (8 * k) := by simp [Nat.mul_comm]
      _ = (2 ^ 8) ^ k := by rw [Nat.pow_mul]
      _ = 256 ^ k := by
        have h256 : (2 : Nat) ^ 8 = 256 := by decide
        simp [h256]
  have h_lo' : 256 ^ (k - 1) ≤ n := by
    have h_exp_le : 8 * (k - 1) ≤ k * 8 - 1 := by omega
    have h_pow_le : 2 ^ (8 * (k - 1)) ≤ 2 ^ (k * 8 - 1) :=
      Nat.pow_le_pow_right (by omega : 0 < 2) h_exp_le
    calc
      256 ^ (k - 1) = (2 ^ 8) ^ (k - 1) := by
        have h256 : (2 : Nat) ^ 8 = 256 := by decide
        simp [h256]
      _ = 2 ^ (8 * (k - 1)) := by rw [Nat.pow_mul]
      _ ≤ 2 ^ (k * 8 - 1) := h_pow_le
      _ ≤ n := h_lo
  have h_numBytes : numBytes n = k := by
    apply Nat.le_antisymm
    · exact numBytes_lt_pow n k h_hi'
    · have h_nb := numBytes_ge_pow n (k - 1) h_lo'
      omega
  calc
    (natToBytes n).size = (natToBytes.go n ByteArray.empty).size := by
      unfold natToBytes
      by_cases hn0 : n = 0
      · exfalso; omega
      · simp [hn0]
    _ = numBytes n + 0 := by rw [size_go, show ByteArray.empty.size = 0 from by decide]
    _ = numBytes n := by simp
    _ = k := h_numBytes

/- natToBytes for a value < 2^256 fits in 32 bytes. -/
theorem natToBytes_size_bound (v : Nat) (hv : v < 2 ^ 256) : (natToBytes v).size ≤ 32 := by
  unfold natToBytes; split
  · decide
  · rename_i hv0
    have h_sz : (natToBytes.go v ByteArray.empty).size = numBytes v := by
      simpa using size_go v ByteArray.empty
    rw [h_sz]; exact numBytes_bound v hv

/-! ## bytesToNat lemmas -/

/- Shift a non-zero initial accumulator out of a list foldl. -/
theorem list_foldl_shift (xs : List UInt8) (x : Nat) :
    xs.foldl (fun acc byte => acc * 256 + byte.toNat) x = x * 256 ^ xs.length + xs.foldl (fun acc byte => acc * 256 + byte.toNat) 0 := by
  induction xs generalizing x with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (x * 256 + h.toNat), ih (0 * 256 + h.toNat)]
    ring

/- bytesToNat of (b ++ acc) where b is a single byte. -/
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

/- bytesToNat of natToBytes.go recovers the original n. -/
theorem bytesToNat_go (n : Nat) (acc : ByteArray) : bytesToNat (natToBytes.go n acc) = n * 256 ^ acc.size + bytesToNat acc := by
  induction n, acc using natToBytes.go.induct with
  | case1 acc => simp [natToBytes.go]
  | case2 n acc hn ih =>
    rw [natToBytes.go, if_neg hn, ih]
    have h_sz : ({ data := Array.mk [((n % 256).toUInt8)] } ++ acc : ByteArray).size = 1 + acc.size := by
      simp [ByteArray.size_append]; rfl
    have h_byt : bytesToNat ({ data := Array.mk [((n % 256).toUInt8)] } ++ acc : ByteArray) = (n % 256) * 256 ^ acc.size + bytesToNat acc := by
      rw [show ({ data := Array.mk [((n % 256).toUInt8)] } ++ acc : ByteArray) = mkSingleton ((n % 256).toUInt8) ++ acc from rfl,
          bytesToNat_append_singleton]
      simp
    rw [h_sz, h_byt]
    calc n / 256 * 256 ^ (1 + acc.size) + ((n % 256) * 256 ^ acc.size + bytesToNat acc)
        = (n / 256 * 256 + n % 256) * 256 ^ acc.size + bytesToNat acc := by ring
      _ = n * 256 ^ acc.size + bytesToNat acc := by rw [show n / 256 * 256 + n % 256 = n from by omega]

/- bytesToNat ∘ natToBytes = id. -/
theorem bytesToNat_natToBytes (v : Nat) : bytesToNat (natToBytes v) = v := by
  unfold natToBytes; split
  · rename_i hzero; subst hzero; unfold bytesToNat bytesToNat_list; simp [zeroByte]
  · have h := bytesToNat_go v ByteArray.empty
    simpa [show (ByteArray.empty : ByteArray).size = 0 from by decide, show bytesToNat (ByteArray.empty : ByteArray) = 0 from by decide] using h

/- bytesToNat distributes over append. -/
theorem bytesToNat_append_general (a b : ByteArray) : bytesToNat (a ++ b) = bytesToNat a * 256 ^ b.size + bytesToNat b := by
  unfold bytesToNat bytesToNat_list
  rw [ByteArray.toList_data_append, List.foldl_append]
  simpa [bytesToNat_list] using list_foldl_shift (b.data.toList) (bytesToNat_list a.data.toList)

/- Padding zeros on the left does not change the numeric value. -/
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
        rw [List.replicate_succ, List.foldl_cons]
        simp [zeroByte]
        exact ih
    have hlist : ({ data := Array.mk (List.replicate (n - b.size) zeroByte) } : ByteArray).data.toList =
        List.replicate (n - b.size) zeroByte := by simp
    rw [hlist, hz]

/- bytesToNat ∘ uint256ToBytes = id for values < 2^256. -/
theorem bytesToNat_uint256ToBytes (v : Nat) : bytesToNat (uint256ToBytes v) = v := by
  unfold uint256ToBytes
  rw [bytesToNat_padLeft, bytesToNat_natToBytes v]

/-! ## ByteArray extraction lemmas -/

/- Extracting the first b.size bytes of (b ++ c) gives b. -/
theorem extract_first_n (b c : ByteArray) : (b ++ c).extract 0 b.size = b := by
  apply ByteArray.ext; simp

/- padRight b 32 extracts back to b for the first sz bytes. -/
/- padRight b n extracts back to b for the first b.size bytes. -/
theorem padRight_extract_self (b : ByteArray) (n : Nat) : (padRight b n).extract 0 b.size = b := by
  unfold padRight; split
  · exact extract_self b
  · exact extract_first_n b (zeros (n - b.size))

theorem padRight_extract_eq (b : ByteArray) (sz : Nat) (hsz : b.size = sz) : (padRight b 32).extract 0 sz = b := by
  subst hsz; exact padRight_extract_self b 32

/- padLeft b 32 with a 20-byte address extracts the original at offset 12. -/
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

/- padRight b 32 is always 32 bytes when b ≤ 32 bytes. -/
theorem padRight_size_32 (b : ByteArray) (h : b.size ≤ 32) : (padRight b 32).size = 32 := by
  unfold padRight; split
  · omega
  · simp [zeros_size]; omega

/- Extract a suffix of an append equals extracting from the second part. -/
theorem extract_after_suffix (a b : ByteArray) (k : Nat) : (a ++ b).extract a.size (a.size + k) = b.extract 0 k := by
  apply ByteArray.ext; simp

/- For a valid ByteArray v', the encoding used by .bytes decoding produces
   the original v' when extracting from offset 32. -/
theorem roundtrip_bytes_val (v' : ByteArray) (hv256 : v'.size < 2 ^ 256) :
    (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)).extract 32 (32 + v'.size) = v' := by
  have ha_sz : (uint256ToBytes v'.size).size = 32 :=
    uint256ToBytes_size v'.size (natToBytes_size_bound v'.size hv256)
  have h_sub : (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)).extract
    (uint256ToBytes v'.size).size ((uint256ToBytes v'.size).size + v'.size) = 
    (padRight v' (roundUp32 v'.size)).extract 0 v'.size :=
    extract_after_suffix (uint256ToBytes v'.size) (padRight v' (roundUp32 v'.size)) v'.size
  calc
    (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)).extract 32 (32 + v'.size)
        = (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)).extract
            (uint256ToBytes v'.size).size ((uint256ToBytes v'.size).size + v'.size) := by simp [ha_sz]
    _ = (padRight v' (roundUp32 v'.size)).extract 0 v'.size := h_sub
    _ = v' := padRight_extract_self v' (roundUp32 v'.size)

/-! ## UTF-8 lemmas -/

/- UTF-8 encode → decode cycle is identity. -/
theorem fromUTF8!_toUTF8 (s : String) : String.fromUTF8! (s.toUTF8) = s := by
  unfold String.fromUTF8!
  have h : s.toByteArray.IsValidUTF8 := by simpa using s.isValidUTF8
  simp [h]
  have h_eq : h = s.isValidUTF8 := Subsingleton.elim _ _
  rw [h_eq]; rfl

/- For v' < 0, intToBytes v' byteLen is 32 bytes when the unsigned value fits in 32 bytes. -/
theorem intToBytes_neg_size (v' : Int) (byteLen : Nat) (hv_nonpos : ¬ v' ≥ 0)
    (h_bounded : ((2 : Int) ^ (byteLen * 8) + v').toNat < 2 ^ 256) :
    (intToBytes v' byteLen).size = 32 := by
  unfold intToBytes; dsimp
  simp [hv_nonpos]
  let u := ((2 : Int) ^ (byteLen * 8) + v').toNat
  have h_sz : (natToBytes u).size ≤ 32 := natToBytes_size_bound u h_bounded
  have h_total : (ByteArray.mk (Array.mk (List.replicate (32 - (natToBytes u).size) 0xFF)) ++ natToBytes u).size = 32 := by
    rw [ByteArray.size_append]
    have h_left : (ByteArray.mk (Array.mk (List.replicate (32 - (natToBytes u).size) 0xFF))).size = 32 - (natToBytes u).size := by
      unfold ByteArray.size; simp
    rw [h_left]
    omega
  simpa [u] using h_total


/- .toNat of (2 : Int) ^ b equals (2 : Nat) ^ b. -/
theorem two_toNat_eq (b : Nat) : ((2 : Int) ^ b).toNat = (2 : Nat) ^ b := by norm_cast
theorem two_pow_succ_sub (b : Nat) (hbpos : 0 < b) : (2 : Int) ^ b - (2 : Int) ^ (b - 1) = (2 : Int) ^ (b - 1) := by
  have h : (2 : ℤ) ^ b = (2 : ℤ) ^ (b - 1) * (2 : ℤ) := by
    calc
      (2 : ℤ) ^ b = (2 : ℤ) ^ ((b - 1) + 1) := by rw [Nat.sub_add_cancel hbpos]
      _ = (2 : ℤ) ^ (b - 1) * (2 : ℤ) := by rw [pow_succ]
  omega
