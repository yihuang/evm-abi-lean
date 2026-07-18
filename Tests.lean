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
# Tests

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
  roundtrip_static (.uint 8) rfl (by native_decide) _

example : decode (.int 8) (encode (.int 8) ⟨-5, by decide⟩) = some ⟨-5, by decide⟩ :=
  roundtrip_static (.int 8) rfl (by native_decide) _

example : decode .bool (encode .bool false) = some false :=
  roundtrip_static .bool rfl (by native_decide) _

example : decode .bytes (encode .bytes [1, 2, 3]) = some [1, 2, 3] :=
  roundtrip_bytes [1, 2, 3] (by decide)

example : decode .string (encode .string "hello") = some "hello" :=
  roundtrip_string "hello" (by native_decide)

-- encodeStatic_length

example : (encode (.uint 256) ⟨42, by decide⟩).length = 32 := by
  rw [encode_length_static (.uint 256) rfl (by native_decide) ⟨42, by decide⟩]
  simp [headSize]

-- encode_length_aligned

example : Aligned (encode .bytes ([1, 2, 3] : List UInt8)).length :=
  encode_length_aligned .bytes (by native_decide) _

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

/-! ## Spec vectors (node 8): Solidity ABI specification examples -/

/- The canonical vectors of the Solidity ABI specification, encoded at the
`Ty` level (without the selector): `sam("dave", true, [1,2,3])`,
`f(0x123, [0x456, 0x789], "1234567890", "Hello, world!")` and
`g([[1, 2], [3]], ["one", "two", "three"])`.  Byte-exact encodings are
checked by computation; `sam` and `f` are additionally re-proved through
the library theorems (no computation). -/

/-- `sam`'s argument tuple: `(bytes, bool, uint256[])`. -/
def specSamTy : Ty := .tuple [.bytes, .bool, .array (.uint 256)]

/-- `sam("dave", true, [1,2,3])`'s arguments. -/
def specSamVal : specSamTy.Val :=
  ([0x64, 0x61, 0x76, 0x65], true, ([⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], ()))

/-- The spec encoding of `sam`'s arguments. -/
def specSamBytes : List UInt8 :=
  encodeUint 0x60 ++ encodeUint 1 ++ encodeUint 0xa0 ++
  encodeUint 4 ++ [0x64, 0x61, 0x76, 0x65] ++ List.replicate 28 0 ++
  encodeUint 3 ++ encodeUint 1 ++ encodeUint 2 ++ encodeUint 3

example : encode specSamTy specSamVal = specSamBytes := by native_decide

example : decode specSamTy (encode specSamTy specSamVal) = some specSamVal :=
  roundtrip specSamTy (by native_decide) specSamVal
    (by
      simp only [specSamTy, specSamVal, LenBound]
      repeat first
        | rw [Ty.TupleLenBounds.eq_2]
        | rw [Ty.TupleLenBounds.eq_1]
        | rw [Ty.AllLenBound.eq_2]
        | rw [Ty.AllLenBound.eq_1]
      simp only [Ty.LenBound]
      repeat first
        | rw [Ty.AllLenBound.eq_2]
        | rw [Ty.AllLenBound.eq_1]
      simp only [Ty.LenBound]
      decide)
    (by native_decide)

/-- `f`'s argument types: `(uint256, uint32[], bytes10, bytes)`. -/
def specFArgs : List Ty := [.uint 256, .array (.uint 32), .bytesN 10, .bytes]

/-- `f`'s argument tuple. -/
def specFTy : Ty := .tuple specFArgs

/-- `f(0x123, [0x456, 0x789], "1234567890", "Hello, world!")`'s arguments. -/
def specFVal : specFTy.Val :=
  (⟨0x123, by decide⟩, [⟨0x456, by decide⟩, ⟨0x789, by decide⟩],
    ⟨[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30], rfl⟩,
    ([0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21], ()))

/-- The spec encoding of `f`'s arguments. -/
def specFBytes : List UInt8 :=
  encodeUint 0x123 ++ encodeUint 0x80 ++
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30] ++ List.replicate 22 0 ++
  encodeUint 0xe0 ++
  encodeUint 2 ++ encodeUint 0x456 ++ encodeUint 0x789 ++
  encodeUint 13 ++
  [0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21] ++
  List.replicate 19 0

example : encode specFTy specFVal = specFBytes := by native_decide

example : decode specFTy (encode specFTy specFVal) = some specFVal :=
  roundtrip specFTy (by native_decide) specFVal
    (by
      simp only [specFTy, specFVal, specFArgs, LenBound]
      repeat first
        | rw [Ty.TupleLenBounds.eq_2]
        | rw [Ty.TupleLenBounds.eq_1]
        | rw [Ty.AllLenBound.eq_2]
        | rw [Ty.AllLenBound.eq_1]
      simp only [Ty.LenBound]
      repeat first
        | rw [Ty.AllLenBound.eq_2]
        | rw [Ty.AllLenBound.eq_1]
      simp only [Ty.LenBound]
      decide)
    (by native_decide)

/-- `g`'s argument tuple: `(uint256[][], string[])`. -/
def specGTy : Ty := .tuple [.array (.array (.uint 256)), .array .string]

/-- `g([[1, 2], [3]], ["one", "two", "three"])`'s arguments. -/
def specGVal : specGTy.Val :=
  ([[⟨1, by decide⟩, ⟨2, by decide⟩], [⟨3, by decide⟩]],
    (["one", "two", "three"], ()))

/-- The spec encoding of `g`'s arguments. -/
def specGBytes : List UInt8 :=
  encodeUint 0x40 ++ encodeUint 0x140 ++
  encodeUint 2 ++ encodeUint 0x40 ++ encodeUint 0xa0 ++
  encodeUint 2 ++ encodeUint 1 ++ encodeUint 2 ++
  encodeUint 1 ++ encodeUint 3 ++
  encodeUint 3 ++ encodeUint 0x60 ++ encodeUint 0xa0 ++ encodeUint 0xe0 ++
  encodeUint 3 ++ [0x6f, 0x6e, 0x65] ++ List.replicate 29 0 ++
  encodeUint 3 ++ [0x74, 0x77, 0x6f] ++ List.replicate 29 0 ++
  encodeUint 5 ++ [0x74, 0x68, 0x72, 0x65, 0x65] ++ List.replicate 27 0

example : encode specGTy specGVal = specGBytes := by native_decide

/-! ## Canonical decoding -/

def nonCanonicalBytesBuf : List UInt8 := encode .bytes [1, 2, 3] ++ [0xff]

example : decode .bytes nonCanonicalBytesBuf = some [1, 2, 3] := by native_decide

example : (decode .bytes (encode .bytes [1, 2, 3])).map (encode .bytes) =
    some (encode .bytes [1, 2, 3]) := by native_decide

example : IsCanonical .bytes nonCanonicalBytesBuf := by
  refine ⟨[1, 2, 3], ?_, ?_⟩
  · native_decide
  · native_decide

example : ∃ enc, (decode .bytes nonCanonicalBytesBuf).map (encode .bytes) = some enc ∧
    nonCanonicalBytesBuf.take enc.length = enc := by
  apply decode_then_encode_roundtrip
  refine ⟨[1, 2, 3], ?_, ?_⟩
  · native_decide
  · native_decide

example : decode .bytes nonCanonicalBytesBuf = some [1, 2, 3] := by native_decide

def aliasedTupleBuf : List UInt8 :=
  encodeUint 64 ++ encodeUint 64 ++ encode .bytes [1]

example : decode (.tuple [.bytes, .bytes]) aliasedTupleBuf = none := by native_decide

end EvmAbi
