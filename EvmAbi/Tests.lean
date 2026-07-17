import EvmAbi.Bytes
import EvmAbi.Align
import EvmAbi.Word

/-!
# Abi.Tests

Computation-checked instances for the `Abi.*` infrastructure modules:
`#eval` sanity checks plus `decide` / `native_decide` regression tests.
-/

namespace EvmAbi

open Binary

/-! ## pad32 -/

#eval (pad32 [1, 2, 3]).length                    -- 32
#eval (pad32 ((List.range 40).map UInt8.ofNat)).length  -- 64
#eval (pad32 ([] : List UInt8)).length            -- 0

example : (pad32 [1, 2, 3]).take 3 = [1, 2, 3] := by decide
example : (pad32 ([] : List UInt8)).length = 0 := by decide
example : 32 ∣ (pad32 [7]).length := by decide
example : pad32 (UInt256.toBEBytes 9) = UInt256.toBEBytes 9 := by native_decide

/-! ## splitEvery -/

#eval splitEvery 2 [1, 2, 3, 4, 5]                -- [[1, 2], [3, 4], [5]]
#eval (splitEvery 32 (List.range 64)).length      -- 2

example : (splitEvery 32 (List.range 96)).flatten = List.range 96 := by native_decide
example : (splitEvery 32 (List.range 64)).length = 2 := by native_decide
example : ∀ c ∈ splitEvery 32 (List.range 96), c.length = 32 := by native_decide
example : splitEvery 32 ([] : List Nat) = [] := by native_decide

/-! ## wordAt / natAt -/

-- Two words written consecutively; reading index 1 gives the second word.
#eval wordAt (UInt256.toBEBytes 7 ++ UInt256.toBEBytes 8) 1    -- some 8
#eval natAt (UInt256.toBEBytes 7 ++ UInt256.toBEBytes 8) 0     -- some 7
#eval wordAt (UInt256.toBEBytes 7) 1                           -- none (out of range)

example : wordAt (UInt256.toBEBytes 42) 0 = some (42 : UInt256) := by native_decide
example : natAt (UInt256.toBEBytes 42) 0 = some 42 := by native_decide
example : wordAt (UInt256.toBEBytes 1 ++ UInt256.toBEBytes 2 ++ UInt256.toBEBytes 3) 2
    = some (3 : UInt256) := by native_decide

-- The same instance proved via the library theorem (no computation)
example : natAt (UInt256.toBEBytes 7 ++ UInt256.toBEBytes 8) 0 = some 7 := by
  have e := natAt_append ([] : List UInt8) (UInt256.toBEBytes 8) (7 : UInt256) 0 (by simp)
  have h7 : (7 : UInt256).toNat = 7 := by native_decide
  simpa [bytesOfWord, h7] using e

/-! ## Aligned -/

example : Aligned (pad32 [1, 2, 3]).length := dvd_length_pad32 _
example : Aligned ((UInt256.toBEBytes 1) ++ (UInt256.toBEBytes 2)).length :=
  aligned_length_append ⟨1, by native_decide⟩ ⟨1, by native_decide⟩

end EvmAbi
