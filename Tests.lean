import EvmAbi.Bytes
import EvmAbi.Align
import EvmAbi.Word
import EvmAbi.Ty
import EvmAbi.Static
import EvmAbi.Dynamic
import EvmAbi.Codec
import EvmAbi.StaticArray
import EvmAbi.Parts
import EvmAbi.Packed
import EvmAbi.Canonical

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

example : decode .bytes (encode .bytes ⟨[0x61, 0x62, 0x63], by decide⟩)
    = some ⟨[0x61, 0x62, 0x63], by decide⟩ := by native_decide

example : decode .string (encode .string ⟨"Hello, world!", by native_decide⟩)
    = some ⟨"Hello, world!", by native_decide⟩ := by native_decide

-- The same instances via library theorems (no computation)

example : decode (.uint 8) (encode (.uint 8) ⟨200, by decide⟩) = some ⟨200, by decide⟩ :=
  roundtrip_static (.uint 8) rfl (by native_decide) _

example : decode (.int 8) (encode (.int 8) ⟨-5, by decide⟩) = some ⟨-5, by decide⟩ :=
  roundtrip_static (.int 8) rfl (by native_decide) _

example : decode .bool (encode .bool false) = some false :=
  roundtrip_static .bool rfl (by native_decide) _

example : decode .bytes (encode .bytes ⟨[1, 2, 3], by decide⟩) = some ⟨[1, 2, 3], by decide⟩ :=
  roundtrip_bytes ⟨[1, 2, 3], by decide⟩

example : decode .string (encode .string ⟨"hello", by native_decide⟩) =
    some ⟨"hello", by native_decide⟩ :=
  roundtrip_string ⟨"hello", by native_decide⟩

-- encodeStatic_length

example : (encode (.uint 256) ⟨42, by decide⟩).length = 32 := by
  rw [encode_length_static (.uint 256) rfl (by native_decide) ⟨42, by decide⟩]
  simp [headSize]

-- encode_length_aligned

example : Aligned (encode .bytes ⟨[1, 2, 3], by decide⟩).length :=
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
  (⟨[0x64, 0x61, 0x76, 0x65], by decide⟩, true,
    (⟨[⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩, ()))

/-- The spec encoding of `sam`'s arguments. -/
def specSamBytes : List UInt8 :=
  encodeUint 0x60 ++ encodeUint 1 ++ encodeUint 0xa0 ++
  encodeUint 4 ++ [0x64, 0x61, 0x76, 0x65] ++ List.replicate 28 0 ++
  encodeUint 3 ++ encodeUint 1 ++ encodeUint 2 ++ encodeUint 3

example : encode specSamTy specSamVal = specSamBytes := by native_decide

example : decode specSamTy (encode specSamTy specSamVal) = some specSamVal :=
  roundtrip specSamTy (by native_decide) specSamVal (by native_decide)

/-- `f`'s argument types: `(uint256, uint32[], bytes10, bytes)`. -/
def specFArgs : List Ty := [.uint 256, .array (.uint 32), .bytesN 10, .bytes]

/-- `f`'s argument tuple. -/
def specFTy : Ty := .tuple specFArgs

/-- `f(0x123, [0x456, 0x789], "1234567890", "Hello, world!")`'s arguments. -/
def specFVal : specFTy.Val :=
  (⟨0x123, by decide⟩, ⟨[⟨0x456, by decide⟩, ⟨0x789, by decide⟩], by decide⟩,
    ⟨[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30], rfl⟩,
    (⟨[0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21],
      by decide⟩, ()))

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
  roundtrip specFTy (by native_decide) specFVal (by native_decide)

/-- `g`'s argument tuple: `(uint256[][], string[])`. -/
def specGTy : Ty := .tuple [.array (.array (.uint 256)), .array .string]

/-- `g([[1, 2], [3]], ["one", "two", "three"])`'s arguments. -/
def specGVal : specGTy.Val :=
  (⟨[⟨[⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩, ⟨[⟨3, by decide⟩], by decide⟩], by decide⟩,
    (⟨[⟨"one", by native_decide⟩, ⟨"two", by native_decide⟩, ⟨"three", by native_decide⟩],
      by decide⟩, ()))

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

/-! ## Canonical validation (node 8 strictness): positive vectors -/

-- the spec encodings validate, consuming exactly their length
example : validate specSamTy specSamBytes = some specSamBytes.length := by native_decide
example : validate specFTy specFBytes = some specFBytes.length := by native_decide
example : validate specGTy specGBytes = some specGBytes.length := by native_decide

-- and are strictly decodable (checked via `.isSome` since the dependent
-- return type has no `DecidableEq` instance)
example : (decodeCanonical specSamTy specSamBytes).isSome = true := by native_decide
example : (decodeCanonical specFTy specFBytes).isSome = true := by native_decide
example : (decodeCanonical specGTy specGBytes).isSome = true := by native_decide

-- the same instances via library theorems (no computation)

example : IsCanonical specSamTy (encode specSamTy specSamVal) :=
  isCanonical_encode specSamTy (by native_decide) specSamVal (by native_decide)

example : decodeCanonical specSamTy (encode specSamTy specSamVal) = some specSamVal :=
  decodeCanonical_encode specSamTy (by native_decide) specSamVal (by native_decide)

/-- **Canonical uniqueness** (computational): re-encoding the decoded value
gives the original buffer back. -/
example : encode specFTy specFVal = specFBytes := by native_decide

/-! ## C4: bounds are intrinsic, image characterization -/

-- forward: a canonical buffer IS an encoding — no bound on the value side
example : ∃ v, decode specSamTy specSamBytes = some v ∧
    encode specSamTy v = specSamBytes :=
  (isCanonical_iff specSamTy (by native_decide) specSamBytes (by native_decide)).mp
    (by unfold IsCanonical; native_decide)

-- backward: canonicity of an encoding through the iff
example : IsCanonical specSamTy (encode specSamTy specSamVal) :=
  (isCanonical_iff specSamTy (by native_decide) _ (by native_decide)).mpr
    ⟨specSamVal,
      roundtrip specSamTy (by native_decide) specSamVal (by native_decide),
      rfl⟩

-- the strict roundtrip through the strict-decoder characterization
example : decodeCanonical specSamTy (encode specSamTy specSamVal) = some specSamVal :=
  (decodeCanonical_eq_some_iff specSamTy (by native_decide) _ specSamVal
    (by native_decide)).mpr rfl

/-! ## Canonical validation: negative vectors -/

/-- Demo type `(bytes, bytes)`: two dynamic components. -/
def ncTy : Ty := .tuple [.bytes, .bytes]

/-- Two dynamic components sharing one tail (duplicate offset). -/
def ncSharedTail : List UInt8 :=
  encodeUint 0x40 ++ encodeUint 0x40 ++ encodeBytes [1]

/-- Tails swapped relative to the component order. -/
def ncSwapped : List UInt8 :=
  encodeUint 0x80 ++ encodeUint 0x40 ++ encodeBytes [2] ++ encodeBytes [1]

/-- A 32-byte gap between the head section and the first tail. -/
def ncGap : List UInt8 :=
  encodeUint 0x60 ++ encodeUint 0xA0 ++ encodeUint 0 ++ encodeBytes [1] ++ encodeBytes [2]

/-- An offset pointing back into the head section. -/
def ncIntoHead : List UInt8 :=
  encodeUint 0x20 ++ encodeUint 0x40 ++ encodeBytes [1] ++ encodeBytes [2]

/-- A misaligned offset. -/
def ncMisaligned : List UInt8 :=
  encodeUint 0x41 ++ encodeUint 0x80 ++ encodeBytes [1] ++ encodeBytes [2]

-- the lenient decoder accepts all of these (the leniency gap)
example : (decode ncTy ncSharedTail).isSome = true := by native_decide
example : (decode ncTy ncSwapped).isSome = true := by native_decide
example : (decode ncTy ncGap).isSome = true := by native_decide
example : (decode ncTy ncIntoHead).isSome = true := by native_decide

-- the canonical validator and the strict decoder reject all of them
example : validate ncTy ncSharedTail = none := by native_decide
example : validate ncTy ncSwapped = none := by native_decide
example : validate ncTy ncGap = none := by native_decide
example : validate ncTy ncIntoHead = none := by native_decide
example : validate ncTy ncMisaligned = none := by native_decide
example : (decodeCanonical ncTy ncSharedTail).isNone = true := by native_decide
example : (decodeCanonical ncTy ncSwapped).isNone = true := by native_decide
example : (decodeCanonical ncTy ncGap).isNone = true := by native_decide
example : (decodeCanonical ncTy ncIntoHead).isNone = true := by native_decide
example : (decodeCanonical ncTy ncMisaligned).isNone = true := by native_decide

-- trailing garbage: the prefix validator accepts (reporting the canonical
-- prefix length), but the strict decoder rejects it
example : validate specSamTy (specSamBytes ++ [0]) = some specSamBytes.length := by
  native_decide
example : (decodeCanonical specSamTy (specSamBytes ++ [0])).isNone = true := by native_decide

/-! ## Packed ABI: primitive encodings -/

-- uint8: 1 byte
#eval encodePacked (.uint 8) ⟨42, by decide⟩            -- [42]
example : encodePacked (.uint 8) ⟨42, by decide⟩ = [42] := by native_decide

-- uint256: 32 bytes, big-endian
example : encodePacked (.uint 256) ⟨1, by decide⟩ =
    List.replicate 31 0 ++ [1] := by native_decide

-- int8: -1 = 0xFF
example : encodePacked (.int 8) ⟨-1, by decide⟩ = [0xFF] := by native_decide

-- bool: 1 byte
example : encodePacked .bool true = [1] := by native_decide
example : encodePacked .bool false = [0] := by native_decide

-- address: 20 bytes
example : (encodePacked .address ⟨1, by decide⟩).length = 20 := by native_decide

-- bytes4: 4 bytes, no padding
example : encodePacked (.bytesN 4) ⟨[0xDE, 0xAD, 0xBE, 0xEF], by decide⟩ =
    [0xDE, 0xAD, 0xBE, 0xEF] := by native_decide

/-! ## Packed ABI: compound encodings -/

-- static tuple (uint8, bool): 1 + 1 = 2 bytes
example : encodePacked (.tuple [.uint 8, .bool]) (⟨42, by decide⟩, (true, ())) =
    [42, 1] := by native_decide

-- static tuple (address, uint8): 20 + 1 = 21 bytes
example : (encodePacked (.tuple [.address, .uint 8])
    (⟨0, by decide⟩, (⟨255, by decide⟩, ()))).length = 21 := by native_decide

-- static fixed array uint8[3]: elements padded to 32-byte words (Solidity
-- packed rule 3), 96 bytes total
example : encodePacked (.fixedArray (.uint 8) 3)
    ⟨[⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ =
    encodeUint 1 ++ encodeUint 2 ++ encodeUint 3 := by native_decide

-- nested tuple ((uint8, bool), bytes2) flattens to (1 + 1) + 2 = 4 bytes —
-- a non-Solidity extension (Solidity rejects structs in packed mode);
-- pinned here as the total function's documented behavior
example : encodePacked (.tuple [.tuple [.uint 8, .bool], .bytesN 2])
    ((⟨42, by decide⟩, (true, ())), (⟨[0xAB, 0xCD], by decide⟩, ())) =
    [42, 1, 0xAB, 0xCD] := by native_decide

/-! ## Packed ABI: roundtrips -/

-- primitive roundtrips
example : decodePacked (.uint 8) (encodePacked (.uint 8) ⟨42, by decide⟩) =
    some ⟨42, by decide⟩ := by native_decide

example : decodePacked (.int 8) (encodePacked (.int 8) ⟨-1, by decide⟩) =
    some ⟨-1, by decide⟩ := by native_decide

example : decodePacked .bool (encodePacked .bool true) = some true := by native_decide

example : decodePacked .address (encodePacked .address ⟨0xABCDEF, by decide⟩) =
    some ⟨0xABCDEF, by decide⟩ := by native_decide

example : decodePacked (.bytesN 4)
    (encodePacked (.bytesN 4) ⟨[0xDE, 0xAD, 0xBE, 0xEF], by decide⟩) =
    some ⟨[0xDE, 0xAD, 0xBE, 0xEF], by decide⟩ := by native_decide

-- tuple roundtrip
example : decodePacked (.tuple [.uint 8, .bool])
    (encodePacked (.tuple [.uint 8, .bool]) (⟨42, by decide⟩, (true, ()))) =
    some (⟨42, by decide⟩, (true, ())) := by native_decide

-- fixed array roundtrip
example : decodePacked (.fixedArray (.uint 8) 3)
    (encodePacked (.fixedArray (.uint 8) 3)
      ⟨[⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩) =
    some ⟨[⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ := by native_decide

-- nested tuple roundtrip
example : decodePacked (.tuple [.tuple [.uint 8, .bool], .bytesN 2])
    (encodePacked (.tuple [.tuple [.uint 8, .bool], .bytesN 2])
      ((⟨42, by decide⟩, (true, ())), (⟨[0xAB, 0xCD], by decide⟩, ()))) =
    some ((⟨42, by decide⟩, (true, ())), (⟨[0xAB, 0xCD], by decide⟩, ())) := by native_decide

/-! ## Packed ABI: Solidity Non-standard Packed Mode

Spec rules used here:
* array elements are padded, still encoded in-place
* dynamic types (`bytes`, `string`, `T[]`) are encoded in-place without length
* structs / nested arrays are not supported by Solidity (no reference vector)
-/

/-- Solidity packed `uint8[3]([1,2,3])`: three left-padded 32-byte words. -/
def solidityPackedUint8x3 : List UInt8 :=
  encodeUint 1 ++ encodeUint 2 ++ encodeUint 3

/-- Spec example payload: `string("Hello, world!")` without length prefix. -/
def solidityPackedHello : List UInt8 :=
  "Hello, world!".toUTF8.data.toList

-- Control (must stay green): flat multi-arg style product is unpadded.
-- Solidity: abi.encodePacked(uint8(1), uint8(2), uint8(3)) = 0x010203
example : encodePacked (.tuple [.uint 8, .uint 8, .uint 8])
    (⟨1, by decide⟩, (⟨2, by decide⟩, (⟨3, by decide⟩, ()))) =
    [1, 2, 3] := by native_decide

-- Rule 3 — array elements are padded to 32-byte words: 96 bytes total.
example : encodePacked (.fixedArray (.uint 8) 3)
    ⟨[⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩ =
    solidityPackedUint8x3 := by native_decide

example : (encodePacked (.fixedArray (.uint 8) 3)
    ⟨[⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩).length = 96 := by
  native_decide

example : packedSize (.fixedArray (.uint 8) 3) = 96 := by native_decide

-- Rule 2 — dynamic types are encoded in place, without the length word.
-- Solidity: abi.encodePacked(string("Hello, world!")) = 0x48656c6c6f2c20776f726c6421
example : encodePacked .string "Hello, world!" = solidityPackedHello := by native_decide

example : encodePacked .string "Hello, world!" ≠ ([] : List UInt8) := by native_decide

example : encodePacked .bytes [1, 2, 3] = [1, 2, 3] := by native_decide

example : encodePacked .bytes [1, 2, 3] ≠ ([] : List UInt8) := by native_decide

-- Dynamic array: length omitted; each element padded to 32 bytes.
-- Solidity: abi.encodePacked(uint16[]([3, 4])) = word(3) ++ word(4)
example : encodePacked (.array (.uint 16))
    [⟨3, by decide⟩, ⟨4, by decide⟩] =
    encodeUint 3 ++ encodeUint 4 := by native_decide

-- Invalid widths (m % 8 ≠ 0) are rejected at decode — encodeBEU truncates
-- them, so accepting them would let a lossy encode "roundtrip".
example : decodePacked (.uint 12) (encodePacked (.uint 12) ⟨4095, by decide⟩) = none := by
  native_decide

-- Zero-width types are invalid (`Valid` needs `8 ≤ m`) and their packed
-- encoding is empty, so decoding must refuse rather than conjure a value
-- (previously `decodePacked (.int 0)` mapped -1 to `some 0`).
example : decodePacked (.uint 0) [] = none := by decide
example : decodePacked (.int 0) (encodePacked (.int 0) ⟨-1, by decide⟩) = none := by decide

-- Rule 4 — the Solidity-conformant fragment: scalars, bytes/string, and
-- arrays of scalars; structs and nested arrays are outside it.
example : PackedSupported (.array (.uint 16)) = true := by native_decide
example : PackedSupported .string = true := by native_decide
example : PackedSupported (.fixedArray (.fixedArray (.uint 8) 2) 2) = false := by native_decide
example : PackedSupported (.tuple [.uint 8, .bool]) = false := by native_decide

/-! ## Packed ABI: kernel reducibility

The packed codec is structurally recursive, so plain `decide` (kernel
reduction, no compiler in the trusted base) evaluates it.  These fail if
the mutual blocks ever fall back to well-founded recursion (`Acc.rec`
gets stuck under `decide`).  Array clauses defer to the standard `encode`
and stay `native_decide`-only. -/

example : encodePacked .bool true = [1] := by decide
example : encodePacked (.uint 8) ⟨42, by decide⟩ = [42] := by decide
example : encodePacked (.tuple [.uint 8, .bool]) (⟨42, by decide⟩, (true, ())) =
    [42, 1] := by decide
example : decodePacked (.uint 8) [42] = some ⟨42, by decide⟩ := by decide

end EvmAbi
