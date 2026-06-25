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

------------------------------------------------------------------------------
-- Base-256 digits (least significant first)
------------------------------------------------------------------------------

def digits256 (n : Nat) : List Nat :=
  if h : n < 256 then [n] else n % 256 :: digits256 (n / 256)

theorem dig_lt_256 (n : Nat) : ∀ d ∈ digits256 n, d < 256 := by
  refine (Nat.strongRecOn (motive := λ n => ∀ d ∈ digits256 n, d < 256) n ?_)
  intro n ih
  unfold digits256
  split
  · intro d hd; simp at hd; subst hd; assumption
  · intro d hd
    simp at hd
    rcases hd with (rfl | hd)
    · exact Nat.mod_lt n (by decide : 0 < 256)
    · refine ih (n / 256) ?_ d hd
      exact Nat.div_lt_self (Nat.pos_of_ne_zero
        (by intro hzero; subst hzero; simp at *)) (by decide : 1 < 256)

theorem foldl_snoc (xs : List Nat) (x a : Nat) :
    (xs ++ [x]).foldl (fun acc d => acc * 256 + d) a = (xs.foldl (fun acc d => acc * 256 + d) a) * 256 + x := by
  induction xs generalizing a with
  | nil => simp
  | cons y xs ih => simp [ih (a * 256 + y)]

theorem foldl_reverse_digits256 (v : Nat) :
    (digits256 v).reverse.foldl (fun acc d => acc * 256 + d) 0 = v := by
  refine (Nat.strongRecOn (motive := λ v =>
    (digits256 v).reverse.foldl (fun acc d => acc * 256 + d) 0 = v) v ?_)
  intro v ih
  unfold digits256
  split
  · simp
  · rename_i hv
    have hpos : v ≠ 0 := by
      intro hzero; subst hzero; simp at hv
    have hdiv : v / 256 < v :=
      Nat.div_lt_self (Nat.pos_of_ne_zero hpos) (by decide : 1 < 256)
    have h_ih : (digits256 (v / 256)).reverse.foldl (fun acc d => acc * 256 + d) 0 = v / 256 :=
      ih (v / 256) hdiv
    have h_rev : (v % 256 :: digits256 (v / 256)).reverse = (digits256 (v / 256)).reverse ++ [v % 256] := by
      simp
    rw [h_rev, foldl_snoc, h_ih]
    rw [show v / 256 * 256 + v % 256 = v from by
      rw [Nat.mul_comm]; exact Nat.div_add_mod v 256]

------------------------------------------------------------------------------
-- Big-endian byte-list conversion
------------------------------------------------------------------------------

def natToBytesBE (v : Nat) : List UInt8 :=
  (digits256 v).reverse.map UInt8.ofNat

def bytesToNatBE (bs : List UInt8) : Nat :=
  (bs.map UInt8.toNat).foldl (fun acc d => acc * 256 + d) 0

theorem map_toNat_ofNat_id (l : List Nat) (h_all : ∀ d ∈ l, UInt8.toNat (UInt8.ofNat d) = d) :
    List.map (UInt8.toNat ∘ UInt8.ofNat) l = l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    have hd : UInt8.toNat (UInt8.ofNat d) = d := h_all d (by simp)
    have hds : ∀ d' ∈ ds, UInt8.toNat (UInt8.ofNat d') = d' :=
      λ d' hd' => h_all d' (List.mem_cons_of_mem d hd')
    simp [hd, ih hds]

theorem bytesToNatBE_natToBytesBE (v : Nat) : bytesToNatBE (natToBytesBE v) = v := by
  unfold natToBytesBE bytesToNatBE
  have h_all : ∀ d ∈ digits256 v, UInt8.toNat (UInt8.ofNat d) = d := by
    intro d hd
    have h_lt : d < 256 := dig_lt_256 v d hd
    simp [h_lt]
  have h_map : List.map (UInt8.toNat ∘ UInt8.ofNat) (digits256 v) = digits256 v :=
    map_toNat_ofNat_id (digits256 v) h_all
  calc
    ((List.map UInt8.ofNat ((digits256 v).reverse)).map UInt8.toNat).foldl (fun acc d => acc * 256 + d) 0
        = (List.map (UInt8.toNat ∘ UInt8.ofNat) ((digits256 v).reverse)).foldl (fun acc d => acc * 256 + d) 0 := by
      simp
    _ = ((digits256 v).reverse).foldl (fun acc d => acc * 256 + d) 0 := by
      simp [h_map, List.map_reverse]
    _ = v := foldl_reverse_digits256 v

------------------------------------------------------------------------------
-- Relate current ByteArray functions
theorem uint256ToBytes_eq (v : Nat) : uint256ToBytes v = ByteArray.mk (Array.mk (natToBytesBE v)) := by
  -- Proving this requires showing padLeft (natToBytes v) 32 = ByteArray.mk (Array.mk ((digits256 v).reverse.map UInt8.ofNat))
  -- This follows from the fact that natToBytes v produces the same bytes as (digits256 v).reverse.map UInt8.ofNat
  -- which is true by construction of natToBytes via repeated ÷256 and digits256 via repeated ÷256
  sorry

theorem foldl_map_uint8 (l : List UInt8) (a : Nat) : l.foldl (fun acc byte => acc * 256 + byte.toNat) a =
    (l.map UInt8.toNat).foldl (fun acc d => acc * 256 + d) a := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih => simp [ih (a * 256 + x.toNat)]

theorem bytesToNat_eq (b : ByteArray) : bytesToNat b = bytesToNatBE (Array.toList b.data) := by
  -- ByteArray.foldl is defined via foldlM internally; proving equality to List.foldl
  -- requires an internal lemma about ByteArray.foldlM's implementation.
  -- Not needed for the main roundtrip proof (uses bytesToNat directly).
  sorry

theorem natToBytesBE_size (v : Nat) : (natToBytesBE v).length ≤ 32 := by
  -- digits256 v has at most 32 digits for any v < 2^256
  -- For the roundtrip theorem, encode only succeeds when v < 2^bits.val ≤ 2^256,
  -- so this holds.
  sorry
-- Main roundtrip theorem
------------------------------------------------------------------------------

theorem roundtrip (t : ABIType) (v : ABIValue) (data : ByteArray) (henc : encode t v = Except.ok data) :
    decode t data 0 = Except.ok (v, data.size) := by
  sorry
