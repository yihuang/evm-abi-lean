/-!
# EvmAbi.Align

32-byte alignment arithmetic (roadmap node 3). EVM ABI buffers, offsets and
lengths are almost always multiples of 32; this module collects the small
arithmetic facts about `Aligned n := 32 ∣ n` so the codec proofs can stay
free of arithmetic noise. Everything closes by `omega`.

This module depends only on the Lean 4 core library.
-/

namespace EvmAbi

/-- `n` is 32-byte aligned. -/
def Aligned (n : Nat) : Prop := 32 ∣ n

theorem aligned_mul (k : Nat) : Aligned (32 * k) := ⟨k, rfl⟩

theorem aligned_add {a b : Nat} (ha : Aligned a) (hb : Aligned b) : Aligned (a + b) := by
  obtain ⟨ka, rfl⟩ := ha
  obtain ⟨kb, rfl⟩ := hb
  exact ⟨ka + kb, by omega⟩

/-- The length of an append of aligned buffers is aligned. -/
theorem aligned_length_append {xs ys : List α} (hx : Aligned xs.length) (hy : Aligned ys.length) :
    Aligned (xs ++ ys).length := by
  rw [List.length_append]
  exact aligned_add hx hy

end EvmAbi
