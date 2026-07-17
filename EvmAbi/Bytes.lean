/-!
# Abi.Bytes

Byte-list plumbing for the ABI layer (roadmap node 1): right-padding to a
multiple of 32, splitting into fixed-size chunks, and `take`/`drop` lemmas
over appended buffers.

Everything here is proved once so the ABI proofs never redo list arithmetic.
This module depends only on the Lean 4 core library.
-/

namespace EvmAbi

/-! ## take/drop over appended buffers -/

/-- Taking the length of a prefix from an append gives the prefix. -/
theorem take_append_of_length {xs ys : List α} (h : xs.length = k) :
    (xs ++ ys).take k = xs := by
  subst h; simp

/-- Dropping the length of a prefix from an append gives the suffix. -/
theorem drop_append_of_length {xs ys : List α} (h : xs.length = k) :
    (xs ++ ys).drop k = ys := by
  subst h; simp

/-! ## Right-padding to a multiple of 32 -/

/-- Right-pad a byte list with zeros to the next multiple of 32. -/
def pad32 (bs : List UInt8) : List UInt8 :=
  bs ++ List.replicate ((32 - bs.length % 32) % 32) 0

theorem length_pad32 (bs : List UInt8) :
    (pad32 bs).length = bs.length + (32 - bs.length % 32) % 32 := by
  simp [pad32]

/-- The padded length is always 32-byte aligned. -/
theorem dvd_length_pad32 (bs : List UInt8) : 32 ∣ (pad32 bs).length := by
  rw [length_pad32]; omega

/-- Padding only ever appends bytes. -/
theorem length_le_length_pad32 (bs : List UInt8) : bs.length ≤ (pad32 bs).length := by
  rw [length_pad32]; omega

/-- The original bytes are the prefix of the padded buffer. -/
theorem take_length_pad32 (bs : List UInt8) : (pad32 bs).take bs.length = bs := by
  simp [pad32]

/-- The padding itself is what follows the original bytes. -/
theorem drop_length_pad32 (bs : List UInt8) :
    (pad32 bs).drop bs.length = List.replicate ((32 - bs.length % 32) % 32) 0 := by
  simp [pad32]

/-- Padding an already aligned buffer does nothing. -/
theorem pad32_eq_of_dvd (h : 32 ∣ bs.length) : pad32 bs = bs := by
  have hz : (32 - bs.length % 32) % 32 = 0 := by omega
  simp [pad32, hz]

/-! ## Splitting into fixed-size chunks -/

/-- Split a list into chunks of size `k`; the last chunk may be shorter.
    Empty input gives empty output. -/
def splitEvery (k : Nat) (l : List α) : List (List α) :=
  if l = [] then
    []
  else if 0 < k ∧ k < l.length then
    l.take k :: splitEvery k (l.drop k)
  else
    [l]
termination_by l.length
decreasing_by
  simp_wf
  omega

/-- Splitting and flattening is the identity. -/
theorem flatten_splitEvery (l : List α) : (splitEvery k l).flatten = l := by
  induction l using splitEvery.induct (k := k) with
  | case1 => rw [splitEvery, if_pos rfl]; simp
  | case2 x hne hlt ih =>
      rw [splitEvery, if_neg hne, if_pos hlt]
      simp [List.flatten_cons, ih, List.take_append_drop]
  | case3 x hne hnlt =>
      rw [splitEvery, if_neg hne, if_neg hnlt]; simp

/-- An aligned buffer splits into exactly `length / 32` chunks. -/
theorem length_splitEvery (hd : 32 ∣ l.length) :
    (splitEvery 32 l).length = l.length / 32 := by
  induction l using splitEvery.induct (k := 32) with
  | case1 => rw [splitEvery, if_pos rfl]; simp
  | case2 x hne hlt ih =>
      have hd' : 32 ∣ (x.drop 32).length := by
        rw [List.length_drop]; omega
      rw [splitEvery, if_neg hne, if_pos hlt, List.length_cons, ih hd']
      rw [List.length_drop]
      omega
  | case3 x hne hnlt =>
      rw [splitEvery, if_neg hne, if_neg hnlt, List.length_singleton]
      have hpos : 0 < x.length :=
        Nat.pos_of_ne_zero fun h => hne (List.length_eq_zero_iff.mp h)
      omega

/-- Every chunk of an aligned buffer has length exactly 32. -/
theorem length_mem_splitEvery (hd : 32 ∣ l.length) :
    ∀ c ∈ splitEvery 32 l, c.length = 32 := by
  induction l using splitEvery.induct (k := 32) with
  | case1 => rw [splitEvery, if_pos rfl]; simp
  | case2 x hne hlt ih =>
      have hd' : 32 ∣ (x.drop 32).length := by
        rw [List.length_drop]; omega
      rw [splitEvery, if_neg hne, if_pos hlt]
      intro c hc
      simp only [List.mem_cons] at hc
      cases hc with
      | inl he => rw [he, List.length_take]; omega
      | inr ht => exact ih hd' c ht
  | case3 x hne hnlt =>
      rw [splitEvery, if_neg hne, if_neg hnlt]
      intro c hc
      simp only [List.mem_singleton] at hc
      rw [hc]
      have hpos : 0 < x.length :=
        Nat.pos_of_ne_zero fun h => hne (List.length_eq_zero_iff.mp h)
      omega

end EvmAbi
