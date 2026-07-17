import EvmAbi.Bytes
import EvmAbi.Align
import EvmAbi.Word
import EvmAbi.Ty
import EvmAbi.Static
import EvmAbi.Dynamic
import EvmAbi.Codec
import EvmAbi.StaticArray
import EvmAbi.Parts

/-!
# EvmAbi.Tests

Computation-checked instances for the `EvmAbi.*` infrastructure modules:
`#eval` sanity checks plus `decide` / `native_decide` regression tests.
-/

namespace EvmAbi

open Binary
open Ty

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

/-! ## Static primitives (node 4) -/

-- uintM: a word with the value in the last byte(s)
#eval encodeUint 42
example : decodeUint (encodeUint 42) = some 42 := by native_decide
-- the same instance via the library theorem (no computation)
example : decodeUint (encodeUint 42) = some 42 := decodeUint_encodeUint (by native_decide)

-- intM: -1 is the all-ones word (two's complement)
example : encodeInt (-1) = List.replicate 32 255 := by native_decide
example : decodeInt (List.replicate 32 255) = some (-1 : Int) := by native_decide
example : decodeInt (encodeInt (-5)) = some (-5 : Int) := by native_decide
example : decodeInt (encodeInt 100) = some (100 : Int) := by native_decide
example : decodeInt (encodeInt (-5)) = some (-5 : Int) :=
  decodeInt_encodeInt (M := 8) (by decide) (by decide) (by native_decide) (by native_decide)

-- bool: strict decoding
example : decodeBool (encodeBool true) = some true := by native_decide
example : decodeBool (encodeBool false) = some false := by native_decide
example : decodeBool (encodeUint 2) = none := by native_decide

-- address (20 bytes, right-aligned)
example : decodeAddress (encodeAddress 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa) =
    some 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa := by native_decide

-- bytesN: left-aligned, zero padding checked strictly
example : encodeBytesN [0x12, 0x34] = [0x12, 0x34] ++ List.replicate 30 0 := by native_decide
example : decodeBytesN 2 (encodeBytesN [0x12, 0x34]) = some [0x12, 0x34] := by native_decide
example : decodeBytesN 2 ([0x12, 0x34] ++ List.replicate 29 0 ++ [1]) = none := by native_decide

/-! ## Dynamic bytes / string (node 5) -/

-- ABI-spec instance: enc(0x010203 as bytes) = 0x03 word ++ 0x010203 padded
#eval encodeBytes [1, 2, 3]
example : decodeBytes (encodeBytes [1, 2, 3]) = some [1, 2, 3] := by native_decide
example : decodeBytes (encodeBytes [1, 2, 3]) = some [1, 2, 3] :=
  decodeBytes_encodeBytes (by native_decide)
example : decodeBytes (encodeBytes (List.replicate 64 7)) = some (List.replicate 64 7) := by
  native_decide
example : decodeBytes (encodeBytes []) = some [] := by native_decide

#eval encodeString "Hello, world!"
example : decodeString (encodeString "Hello, world!") = some "Hello, world!" := by
  native_decide
example : decodeString (encodeString "Hello, world!") = some "Hello, world!" :=
  decodeString_encodeString (by native_decide)

/-! ## Ty-indexed codec (S2 wrap-up) -/

-- Ty-level roundtrips by computation

example : decode (.uint 8) (encode (.uint 8) ⟨200, by decide⟩) = some ⟨200, by decide⟩ := by
  native_decide

example : decode (.int 16) (encode (.int 16) ⟨-1000, by decide⟩) = some ⟨-1000, by decide⟩ := by
  native_decide

example : decode .bool (encode .bool true) = some true := by native_decide

example : decode (.bytesN 5) (encode (.bytesN 5) ⟨[1,2,3,4,5], rfl⟩)
    = some ⟨[1,2,3,4,5], rfl⟩ := by native_decide

example : decode .bytes (encode .bytes [0x61, 0x62, 0x63])
    = some [0x61, 0x62, 0x63] := by native_decide

example : decode .string (encode .string "Hello, world!")
    = some "Hello, world!" := by native_decide

-- The same instances via library theorems (no computation)

example : decode (.uint 8) (encode (.uint 8) ⟨200, by decide⟩) = some ⟨200, by decide⟩ :=
  roundtrip (.uint 8) (by decide) _ trivial

example : decode (.int 8) (encode (.int 8) ⟨-5, by decide⟩) = some ⟨-5, by decide⟩ :=
  roundtrip (.int 8) (by decide) _ trivial

example : decode .bool (encode .bool false) = some false :=
  roundtrip .bool (by decide) _ trivial

example : decode .bytes (encode .bytes [1, 2, 3]) = some [1, 2, 3] :=
  roundtrip_bytes [1, 2, 3] (by decide)

example : decode .string (encode .string "hello") = some "hello" :=
  roundtrip_string "hello" (by native_decide)

-- encodeStatic_length

example : (encode (.uint 256) ⟨42, by decide⟩).length = 32 := by
  rw [encodeStatic_length (.uint 256) (by exact rfl) (by decide) ⟨42, by decide⟩]

-- encode_length_aligned

example : Aligned (encode .bytes ([1, 2, 3] : List UInt8)).length :=
  encode_length_aligned .bytes (by decide) _

/-! ## Static arrays (node 6) -/

#eval encodeWordArray [1, 2, 3]
example : decodeWordArray 3 (encodeWordArray [1, 2, 3]) = some [1, 2, 3] := by native_decide
example : decodeWordArray 3 (encodeWordArray [1, 2, 3]) = some [1, 2, 3] :=
  decodeWordArray_encodeWordArray ([1, 2, 3] : List UInt256)
example : wordAt (encodeWordArray [7, 8, 9]) 1 = some 8 := by native_decide
example : wordAt (encodeWordArray [7, 8, 9]) 1 = some 8 :=
  wordAt_encodeWordArray _ _ (by decide)

/-! ## Head/tail combinator (node 7) -/

/-- Demo tuple `(uint 1, bytes 0x010203, uint 2)`: a dynamic part between
two static ones. -/
def demoParts : List Part :=
  [ ⟨encodeUint 1, [], false⟩,
    ⟨[], encodeBytes [1, 2, 3], true⟩,
    ⟨encodeUint 2, [], false⟩ ]

theorem wf_demoParts : WF demoParts :=
  wf_cons (by native_decide) (wf_cons (by native_decide) (wf_cons (by native_decide) wf_nil))

-- the full encoding: heads word(1), word(96), word(2); tails word(3) ++ 0x010203 padded
#eval encodeParts demoParts
example : (encodeParts demoParts).length = 160 := by native_decide
example : 32 ∣ (encodeParts demoParts).length := dvd_length_encodeParts wf_demoParts

-- the offset word of the dynamic part sits at head position 1 and contains 96
example : wordAt (encodeParts demoParts) 1 = some (UInt256.ofNat 96) := by native_decide
example : wordAt (encodeParts demoParts) 1 = some (UInt256.ofNat 96) := by
  have h := wordAt_offset_append (xs := [⟨encodeUint 1, [], false⟩]) (head := [])
    (tail := encodeBytes [1, 2, 3]) (ys := [⟨encodeUint 2, [], false⟩]) wf_demoParts
  exact h

-- dropping to the tail offset lands on the bytes encoding
example : (encodeParts demoParts).drop 96 = encodeBytes [1, 2, 3] := by native_decide
example : (encodeParts demoParts).drop (tailOffset demoParts 1) =
    encodeBytes [1, 2, 3] ++ encodeTails [⟨encodeUint 2, [], false⟩] :=
  drop_tailOffset_append (xs := [⟨encodeUint 1, [], false⟩]) (head := [])
    (tail := encodeBytes [1, 2, 3]) (ys := [⟨encodeUint 2, [], false⟩])

-- following the offset word reads the tail back
example : (wordAt (encodeParts demoParts) 1).map
    (fun w => ((encodeParts demoParts).drop w.toNat).take 64) =
    some (encodeBytes [1, 2, 3]) := by
  have h := readTail_append (xs := [⟨encodeUint 1, [], false⟩]) (head := [])
    (tail := encodeBytes [1, 2, 3]) (ys := [⟨encodeUint 2, [], false⟩])
    wf_demoParts (by native_decide)
  exact h

-- end-to-end: prefix-decode the dynamic bytes value at its tail offset
example : decodeBytesPrefix ((encodeParts demoParts).drop 96) = some ([1, 2, 3], 64) := by
  native_decide
example : decodeBytesPrefix ((encodeParts demoParts).drop (tailOffset demoParts 1)) =
    some ([1, 2, 3], (encodeBytes [1, 2, 3]).length) := by
  have h := decodeBytesPrefix_tailOffset (xs := [⟨encodeUint 1, [], false⟩]) (head := [])
    (bs := [1, 2, 3]) (ys := [⟨encodeUint 2, [], false⟩]) (by native_decide)
  exact h

end EvmAbi
