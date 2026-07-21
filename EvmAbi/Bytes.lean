/-!
# EvmAbi.Bytes

Byte-list plumbing for the ABI layer (roadmap node 1): right-padding to a
multiple of 32, and `take`/`drop` lemmas over appended buffers.

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

/-- The original bytes are the prefix of the padded buffer. -/
theorem take_length_pad32 (bs : List UInt8) : (pad32 bs).take bs.length = bs := by
  simp [pad32]

/-- The padding itself is what follows the original bytes. -/
theorem drop_length_pad32 (bs : List UInt8) :
    (pad32 bs).drop bs.length = List.replicate ((32 - bs.length % 32) % 32) 0 := by
  simp [pad32]

end EvmAbi
