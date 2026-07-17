/-!
# Abi.Align

32-byte alignment arithmetic (roadmap node 3). EVM ABI buffers, offsets and
lengths are almost always multiples of 32; this module collects the small
arithmetic facts about `Aligned n := 32 ∣ n` so the codec proofs can stay
free of arithmetic noise. Everything closes by `omega`.

This module depends only on the Lean 4 core library.
-/

namespace EvmAbi

/-- `n` is 32-byte aligned. -/
def Aligned (n : Nat) : Prop := 32 ∣ n

theorem aligned_zero : Aligned 0 := ⟨0, rfl⟩

theorem aligned_mul (k : Nat) : Aligned (32 * k) := ⟨k, rfl⟩

theorem aligned_iff_mod (n : Nat) : Aligned n ↔ n % 32 = 0 := by
  show 32 ∣ n ↔ n % 32 = 0
  constructor <;> intro h <;> omega

theorem aligned_add {a b : Nat} (ha : Aligned a) (hb : Aligned b) : Aligned (a + b) := by
  obtain ⟨ka, rfl⟩ := ha
  obtain ⟨kb, rfl⟩ := hb
  exact ⟨ka + kb, by omega⟩

theorem aligned_sub {a b : Nat} (ha : Aligned a) (hb : Aligned b) : Aligned (a - b) := by
  obtain ⟨ka, rfl⟩ := ha
  obtain ⟨kb, rfl⟩ := hb
  exact ⟨ka - kb, by omega⟩

/-- The length of an append of aligned buffers is aligned. -/
theorem aligned_length_append {xs ys : List α} (hx : Aligned xs.length) (hy : Aligned ys.length) :
    Aligned (xs ++ ys).length := by
  rw [List.length_append]
  exact aligned_add hx hy

/-- Taking an aligned prefix within bounds has exactly that length. -/
theorem length_take_mul_32_of_le {buf : List α} {i : Nat} (h : 32 * i ≤ buf.length) :
    (buf.take (32 * i)).length = 32 * i := by
  rw [List.length_take]
  omega

/-- Dropping an aligned prefix leaves `length - 32 * i` bytes. -/
theorem length_drop_mul_32 (buf : List α) (i : Nat) :
    (buf.drop (32 * i)).length = buf.length - 32 * i :=
  List.length_drop ..

/-- The `i`-th aligned offset of an aligned buffer stays within bounds. -/
theorem mul_32_le_length_of_lt {buf : List α} {n i : Nat} (hn : buf.length = 32 * n) (h : i < n) :
    32 * i + 32 ≤ buf.length := by
  omega

/-- Splitting an aligned offset out of an aligned length. -/
theorem length_sub_mul_32 {n i : Nat} (h : i ≤ n) : 32 * n - 32 * i = 32 * (n - i) := by
  omega

end EvmAbi
