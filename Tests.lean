import EvmAbi.Bytes
import EvmAbi.Align
import EvmAbi.Word
import EvmAbi.Ty
import EvmAbi.Builder
import EvmAbi.Static
import EvmAbi.Dynamic
import EvmAbi.Codec
import EvmAbi.Codec.Strict
import EvmAbi.Parts
import EvmAbi.Packed
import EvmAbi.HumanReadable
import EvmAbi.HumanReadable.Meta

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

/-! ## Ty-indexed codec (S2 wrap-up) -/

-- Ty-level roundtrips by computation

example : decodeStrict (.uint 8) (encode (.uint 8) ⟨200, by decide⟩) = some ⟨200, by decide⟩ := by
  native_decide

example : decodeStrict (.int 16) (encode (.int 16) ⟨-1000, by decide⟩) = some ⟨-1000, by decide⟩ := by
  native_decide

example : decodeStrict .bool (encode .bool true) = some true := by native_decide

example : decodeStrict (.bytesN 5) (encode (.bytesN 5) ⟨[1,2,3,4,5], rfl⟩)
    = some ⟨[1,2,3,4,5], rfl⟩ := by native_decide

example : decodeStrict .bytes (encode .bytes ⟨[0x61, 0x62, 0x63], by decide⟩)
    = some ⟨[0x61, 0x62, 0x63], by decide⟩ := by native_decide

example : decodeStrict .string (encode .string ⟨"Hello, world!", by native_decide⟩)
    = some ⟨"Hello, world!", by native_decide⟩ := by native_decide

-- The same instances via library theorems (no computation)

example : decodeStrict (.uint 8) (encode (.uint 8) ⟨200, by decide⟩) = some ⟨200, by decide⟩ :=
  decodeStrict_encode (.uint 8) (by native_decide) _ (by native_decide)

example : decodeStrict (.int 8) (encode (.int 8) ⟨-5, by decide⟩) = some ⟨-5, by decide⟩ :=
  decodeStrict_encode (.int 8) (by native_decide) _ (by native_decide)

example : decodeStrict .bool (encode .bool false) = some false :=
  decodeStrict_encode .bool (by native_decide) _ (by native_decide)

example : decodeStrict .bytes (encode .bytes ⟨[1, 2, 3], by decide⟩) =
    some ⟨[1, 2, 3], by decide⟩ :=
  decodeStrict_encode .bytes (by native_decide) _ (by native_decide)

example : decodeStrict .string (encode .string ⟨"hello", by native_decide⟩) =
    some ⟨"hello", by native_decide⟩ :=
  decodeStrict_encode .string (by native_decide) _ (by native_decide)

-- encodeStatic_length

example : (encode (.uint 256) ⟨42, by decide⟩).length = 32 := by
  rw [encode_length_static (.uint 256) rfl (by native_decide) ⟨42, by decide⟩]
  simp [headSize]

-- encode_length_aligned

example : Aligned (encode .bytes ⟨[1, 2, 3], by decide⟩).length :=
  encode_length_aligned .bytes (by native_decide) _

/-! ## Head/tail combinator (node 7) -/

/-- Demo tuple `(uint 1, bytes 0x010203, uint 2)`: a dynamic part between
two static ones. -/
def demoParts : List Part :=
  [ ⟨Builder.ofList (encodeUint 1), ∅, false⟩,
    ⟨∅, Builder.ofList (encodeBytes [1, 2, 3]), true⟩,
    ⟨Builder.ofList (encodeUint 2), ∅, false⟩ ]

theorem wf_demoParts : WF demoParts :=
  wf_cons (by native_decide) (wf_cons (by native_decide) (wf_cons (by native_decide) wf_nil))

-- the full encoding: heads word(1), word(96), word(2); tails word(3) ++ 0x010203 padded
#eval encodeParts demoParts
example : (encodeParts demoParts).length = 160 := by native_decide
example : 32 ∣ (encodeParts demoParts).length := dvd_length_encodeParts wf_demoParts

-- the offset word of the dynamic part sits at head position 1 and contains 96
example : wordAt (encodeParts demoParts) 1 = some (UInt256.ofNat 96) := by native_decide
example : wordAt (encodeParts demoParts) 1 = some (UInt256.ofNat 96) := by
  have h := wordAt_offset_append (xs := [⟨Builder.ofList (encodeUint 1), ∅, false⟩]) (head := ∅)
    (tail := Builder.ofList (encodeBytes [1, 2, 3]))
    (ys := [⟨Builder.ofList (encodeUint 2), ∅, false⟩]) wf_demoParts
  exact h

-- dropping to the tail offset lands on the bytes encoding
example : (encodeParts demoParts).drop 96 = encodeBytes [1, 2, 3] := by native_decide
example : (encodeParts demoParts).drop (tailOffset demoParts 1) =
    encodeBytes [1, 2, 3] ++ encodeTails [⟨Builder.ofList (encodeUint 2), ∅, false⟩] :=
  drop_tailOffset_append (xs := [⟨Builder.ofList (encodeUint 1), ∅, false⟩]) (head := ∅)
    (tail := Builder.ofList (encodeBytes [1, 2, 3]))
    (ys := [⟨Builder.ofList (encodeUint 2), ∅, false⟩])

-- end-to-end: prefix-decode the dynamic bytes value at its tail offset
example : decodeBytesPrefix ((encodeParts demoParts).drop 96) = some ([1, 2, 3], 64) := by
  native_decide

/-! ## Canonical validation (node 8 strictness): positive vectors -/

-- types and values shared with the spec-vector section below

def specSamTy : Ty := ty! "(bytes, bool, uint256[])"

def specSamVal : specSamTy.Val :=
  (⟨[0x64, 0x61, 0x76, 0x65], by decide⟩, (true,
    (⟨[⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩, ())))

def specSamBytes : List UInt8 :=
  encodeUint 0x60 ++ encodeUint 1 ++ encodeUint 0xa0 ++
  encodeUint 4 ++ [0x64, 0x61, 0x76, 0x65] ++ List.replicate 28 0 ++
  encodeUint 3 ++ encodeUint 1 ++ encodeUint 2 ++ encodeUint 3

def specFTy : Ty := ty! "(uint256, uint32[], bytes10, bytes)"

def specFVal : specFTy.Val :=
  (⟨0x123, by decide⟩, (⟨[⟨0x456, by decide⟩, ⟨0x789, by decide⟩], by decide⟩,
    (⟨[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30], rfl⟩,
    (⟨[0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21],
      by decide⟩, ()))))

def specFBytes : List UInt8 :=
  encodeUint 0x123 ++ encodeUint 0x80 ++
  [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30] ++ List.replicate 22 0 ++
  encodeUint 0xe0 ++
  encodeUint 2 ++ encodeUint 0x456 ++ encodeUint 0x789 ++
  encodeUint 13 ++
  [0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21] ++
  List.replicate 19 0

def specGTy : Ty := ty! "(uint256[][], string[])"

def specGVal : specGTy.Val :=
  (⟨[⟨[⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩, ⟨[⟨3, by decide⟩], by decide⟩], by decide⟩,
    (⟨[⟨"one", by native_decide⟩, ⟨"two", by native_decide⟩, ⟨"three", by native_decide⟩],
      by decide⟩, ()))

def specGBytes : List UInt8 :=
  encodeUint 0x40 ++ encodeUint 0x140 ++
  encodeUint 2 ++ encodeUint 0x40 ++ encodeUint 0xa0 ++
  encodeUint 2 ++ encodeUint 1 ++ encodeUint 2 ++
  encodeUint 1 ++ encodeUint 3 ++
  encodeUint 3 ++ encodeUint 0x60 ++ encodeUint 0xa0 ++ encodeUint 0xe0 ++
  encodeUint 3 ++ [0x6f, 0x6e, 0x65] ++ List.replicate 29 0 ++
  encodeUint 3 ++ [0x74, 0x77, 0x6f] ++ List.replicate 29 0 ++
  encodeUint 5 ++ [0x74, 0x68, 0x72, 0x65, 0x65] ++ List.replicate 27 0

/-! ### Byte-exact spec vectors

The canonical vectors of the Solidity ABI specification, encoded at the `Ty`
level (without the selector): `sam("dave", true, [1,2,3])`,
`f(0x123, [0x456, 0x789], "1234567890", "Hello, world!")` and
`g([[1, 2], [3]], ["one", "two", "three"])`.  Byte-exactness is checked by
computation; `sam` and `f` are additionally re-proved through the library
roundtrip theorem (no computation). -/

example : encode specSamTy specSamVal = specSamBytes := by native_decide
example : encode specFTy specFVal = specFBytes := by native_decide
example : encode specGTy specGVal = specGBytes := by native_decide

example : decodeStrict specSamTy (encode specSamTy specSamVal) = some specSamVal :=
  decodeStrict_encode specSamTy (by native_decide) specSamVal (by native_decide)

example : decodeStrict specFTy (encode specFTy specFVal) = some specFVal :=
  decodeStrict_encode specFTy (by native_decide) specFVal (by native_decide)

-- the spec encodings are canonical (strictly decodable, no trailing garbage)
example : IsCanonical specSamTy specSamBytes := by native_decide
example : IsCanonical specFTy specFBytes := by native_decide
example : IsCanonical specGTy specGBytes := by native_decide

-- and are strictly decodable (checked via `.isSome` since the dependent
-- return type has no `DecidableEq` instance)
example : (decodeStrict specSamTy specSamBytes).isSome = true := by native_decide
example : (decodeStrict specFTy specFBytes).isSome = true := by native_decide
example : (decodeStrict specGTy specGBytes).isSome = true := by native_decide

-- the same instances via library theorems (no computation)

example : IsCanonical specSamTy (encode specSamTy specSamVal) :=
  isCanonical_encode specSamTy (by native_decide) specSamVal (by native_decide)

example : decodeStrict specSamTy (encode specSamTy specSamVal) = some specSamVal :=
  decodeStrict_encode specSamTy (by native_decide) specSamVal (by native_decide)

/-! ## C4: bounds are intrinsic, image characterization -/

-- forward: a canonical buffer IS an encoding — no bound on the value side
example : ∃ v, encode specSamTy v = specSamBytes :=
  (isCanonical_iff specSamTy (by native_decide) specSamBytes (by native_decide)).mp
    (by unfold IsCanonical; native_decide)

-- backward: canonicity of an encoding through the iff
example : IsCanonical specSamTy (encode specSamTy specSamVal) :=
  (isCanonical_iff specSamTy (by native_decide) _ (by native_decide)).mpr
    ⟨specSamVal, rfl⟩

-- the strict roundtrip through the strict-decoder characterization
example : decodeStrict specSamTy (encode specSamTy specSamVal) = some specSamVal :=
  (decodeStrict_eq_some_iff specSamTy (by native_decide) _ specSamVal
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

-- the strict decoder rejects all of them (offset words that violate the
-- canonical layout: duplicate, swapped, gapped, head-pointing, misaligned)
example : (decodeStrict ncTy ncSharedTail).isNone = true := by native_decide
example : (decodeStrict ncTy ncSwapped).isNone = true := by native_decide
example : (decodeStrict ncTy ncGap).isNone = true := by native_decide
example : (decodeStrict ncTy ncIntoHead).isNone = true := by native_decide
example : (decodeStrict ncTy ncMisaligned).isNone = true := by native_decide

-- trailing garbage: the strict decoder rejects it
example : (decodeStrict specSamTy (specSamBytes ++ [0])).isNone = true := by native_decide

/-! ## The consumed count is structural

`decode` reports how many bytes it consumed, so `decodeElem` advances the
tail frontier in `O(1)` instead of measuring the cursors — the count is
the encoding's length, and the remainder is untouched. -/

-- a prefix decode through trailing data reports the encoding length
example :
    decode .bytes (encodeBytes [1, 2, 3] ++ [0xFF]) =
      some (⟨[1, 2, 3], by decide⟩, 64, [0xFF]) := by native_decide

example :
    decode (.uint 8) (encode (.uint 8) ⟨7, by decide⟩ ++ [0xFF]) =
      some (⟨7, by decide⟩, 32, [0xFF]) := by native_decide

-- a compound value's count is its whole layout, head plus tails
example :
    (decode specSamTy (specSamBytes ++ [0xFF])).map (fun p => (p.2.1, p.2.2)) =
      some (specSamBytes.length, [0xFF]) := by native_decide

/-! ## Zero-head element types are rejected

An element type occupying no head bytes (`()`, `T[0]`) would let a
32-byte length word name arbitrarily many elements, with the element walk
bounded by nothing.  Such array types are invalid, and `decode` rejects
them before reading the length word. -/

example : ¬ (Ty.array (.tuple [])).Valid := by decide
example : ¬ (Ty.array (.fixedArray (.uint 8) 0)).Valid := by decide

-- the element type itself stays valid — it is only its array that is not
example : (Ty.tuple []).Valid := by decide

-- a 32-byte buffer claiming 2^64 elements is rejected outright
example : (decodeStrict (.array (.tuple [])) (encodeUint (2 ^ 64))).isNone = true := by
  native_decide

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
example : encodePacked .string ⟨"Hello, world!", by native_decide⟩ = solidityPackedHello := by native_decide

example : encodePacked .string ⟨"Hello, world!", by native_decide⟩ ≠ ([] : List UInt8) := by native_decide

example : encodePacked .bytes ⟨[1, 2, 3], by decide⟩ = [1, 2, 3] := by native_decide
example : encodePacked .bytes ⟨[1, 2, 3], by decide⟩ ≠ ([] : List UInt8) := by native_decide

-- Dynamic array: length omitted; each element padded to 32 bytes.
-- Solidity: abi.encodePacked(uint16[]([3, 4])) = word(3) ++ word(4)
example : encodePacked (.array (.uint 16))
    ⟨[⟨3, by decide⟩, ⟨4, by decide⟩], by decide⟩ =
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

/-!
## Human-readable ABI

User-facing APIs: compile-time macros (`ty!`, `item!`, `params!`) for
`encode`/`decode`, and the curried runtime parsers (`Ty.parse`,
`AbiItem.parse`).
-/

section HumanReadable

/-! ### `ty!` — compile-time type → encode/decode roundtrip

A single composite type exercises every scalar, fixed-array, and dynamic
payload in one roundtrip:

```
(uint256, int16, address, bool, bytes4, bytes, string, uint256[3], uint256[])
```
-/

def composite : Ty :=
  ty! "(uint256, int16, address, bool, bytes4, bytes, string, uint256[3], uint256[])"

/-- One value inhabiting the composite type — exercises every ABI category. -/
def compositeVal : composite.Val :=
  let u : (ty! "uint256").Val := ⟨42, by decide⟩
  let i : (ty! "int16").Val := ⟨-1000, by decide⟩
  let a : (ty! "address").Val := ⟨0xABCDEF, by decide⟩
  let b : (ty! "bool").Val := true
  let b4 : (ty! "bytes4").Val := ⟨[0xDE, 0xAD, 0xBE, 0xEF], rfl⟩
  let bs : (ty! "bytes").Val := ⟨[0x61, 0x62, 0x63], by decide⟩
  let s : (ty! "string").Val := ⟨"Hello, world!", by native_decide⟩
  let fa : (ty! "uint256[3]").Val := ⟨[⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], rfl⟩
  let da : (ty! "uint256[]").Val := ⟨[⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩
  (u, (i, (a, (b, (b4, (bs, (s, (fa, (da, ())))))))))

/-- Everything `ty!` produces is `Ty.Valid`, so the codec theorems apply to it. -/
theorem composite_valid : composite.Valid := by decide

-- printed as head words plus a length: the whole 576-byte buffer overflows
-- the pretty printer's recursion limit and falls back to the raw printer
#eval (encode composite compositeVal).take 64

example : (encode composite compositeVal).length = 576 := by native_decide

example : decodeStrict composite (encode composite compositeVal) = some compositeVal :=
  decodeStrict_encode composite composite_valid _ (by native_decide)

/-! ### Widths outside the spec are rejected

A successful parse always yields a `Ty.Valid` type (see `composite_valid`
above).  `Ty` has no `DecidableEq`, so rejection is checked through
`Option.isNone`, and `#guard` evaluates it without a `native_decide` proof. -/

#guard (Ty.parse "uint7").isNone
#guard (Ty.parse "uint999").isNone
#guard (Ty.parse "int0").isNone
#guard (Ty.parse "bytes0").isNone
#guard (Ty.parse "bytes33").isNone
-- an invalid width anywhere inside a composite type sinks the whole parse
#guard (Ty.parse "(uint8, bytes33)").isNone
#guard (Ty.parse "uint7[]").isNone
#guard (Ty.parse "(uint8, bytes32)[]").isSome
-- an array whose element type occupies no head is rejected, though the
-- element type parses on its own
#guard (Ty.parse "()").isSome
#guard (Ty.parse "()[]").isNone
#guard (Ty.parse "uint8[0][]").isNone
#guard (Ty.parse "uint8[0]").isSome

/-! ### Tuple arrays: `(T₁, …, Tₙ)[]` and `(T₁, …, Tₙ)[k]` -/

example : ty! "(address, uint256)[]" = .array (.tuple [.address, .uint 256]) := rfl
example : ty! "(address, uint256)[2]" = .fixedArray (.tuple [.address, .uint 256]) 2 := rfl
example : ty! "(bool)[][3]" = .fixedArray (.array (.tuple [.bool])) 3 := rfl
-- `()[2]` is fine (the element count comes from the type), but `()[]` is not:
-- see "Zero-head element types are rejected" above
example : ty! "()[2]" = .fixedArray (.tuple []) 2 := rfl

/-- A dynamic array of static structs — the shape of a Solidity `struct[]`. -/
def structArray : Ty := ty! "(address, uint256)[]"

theorem structArray_valid : structArray.Valid := by decide

def structArrayVal : structArray.Val :=
  ⟨[(⟨0xAAAA, by decide⟩, (⟨1, by decide⟩, ())),
    (⟨0xBBBB, by decide⟩, (⟨2, by decide⟩, ()))], by decide⟩

example : decodeStrict structArray (encode structArray structArrayVal) = some structArrayVal :=
  decodeStrict_encode structArray structArray_valid _ (by native_decide)

/-! ### `item!` — function/event/error signatures → call-data encoding -/

-- ERC-20 `transfer(address,uint256)` — two-argument function

example :
  let item := item! "function transfer(address to, uint256 amount) returns (bool)"
  let t := item.inputsTy
  let v : t.Val := (⟨0xABCDEF, by decide⟩, (⟨1000, by decide⟩, ()))
  decodeStrict t (encode t v) = some v
:= by
  intro item t v; apply decodeStrict_encode t (by native_decide) v (by native_decide)

-- ERC-20 `balanceOf(address)` — single-argument function, view modifier

#eval
  let item := item! "function balanceOf(address account) view returns (uint256)"
  encode item.inputsTy (⟨0xABCDEF, by decide⟩, ())

-- A single argument stays wrapped in a tuple: for a dynamic argument the
-- call-data block leads with the offset word, which the bare `bytes` encoding
-- would omit.

example : (item! "function f(bytes data)").inputsTy = .tuple [.bytes] := rfl

example :
  let t := (item! "function f(bytes data)").inputsTy
  let v : t.Val := (⟨[0x61, 0x62, 0x63], by decide⟩, ())
  (encode t v).take 32 = encodeUint 0x20 := by native_decide

-- custom error

#eval
  let err := item! "error Unauthorized(address caller)"
  err.inputsTy

/-! ### Solidity source noise: aliases, modifiers, data locations -/

example : ty! "uint" = .uint 256 := rfl
example : ty! "int" = .int 256 := rfl
example : ty! "(uint, int)[]" = .array (.tuple [.uint 256, .int 256]) := rfl

-- visibility keywords are dropped, the mutability keyword is kept
example : (item! "function f() public payable") = .function "f" [] [] .payable := rfl
example : (item! "function f() external view returns (uint256)").outputsTy
    = some (.tuple [.uint 256]) := rfl
example : (item! "function f() virtual override returns (bool)").outputsTy
    = some (.tuple [.bool]) := rfl

-- data locations and `address payable` are dropped
example : (item! "function f(bytes calldata data) external").inputsTy = .tuple [.bytes] := rfl
example : (item! "function f(string memory s) public view returns (string memory)").inputsTy
    = .tuple [.string] := rfl
example : (item! "function f(address payable to)").inputsTy = .tuple [.address] := rfl
-- consumed at the type layer, so it composes with tuples, arrays and locations
example : ty! "(address payable, uint256)" = .tuple [.address, .uint 256] := rfl
example : (item! "function f(address payable[] calldata to)").inputsTy
    = .tuple [.array .address] := rfl
-- but only after `address`: elsewhere `payable` is not part of the type
#guard (AbiItem.parse "function f(uint256 payable)").isNone

-- `indexed` is the one keyword that survives into the ABI
example : (item! "event Transfer(address indexed from, address indexed to, uint256 value)")
    = .event "Transfer" [⟨.address, some "from", true⟩, ⟨.address, some "to", true⟩,
        ⟨.uint 256, some "value", false⟩] := rfl

example : (item! "fallback() external payable") = .fallback .payable := rfl
example : (item! "receive() external payable") = .receive := rfl
example : (item! "constructor(address owner) public payable")
    = .constructor [⟨.address, some "owner", false⟩] .payable := rfl

-- an unknown modifier is still a parse failure
#guard (AbiItem.parse "function f() bogus returns (bool)").isNone
#guard (AbiItem.parse "function f(uint256 a").isNone

-- a second mutability keyword — conflicting or repeated — is a parse failure
#guard (AbiItem.parse "function f() view payable").isNone
#guard (AbiItem.parse "function f() payable payable").isNone
#guard (AbiItem.parse "constructor() payable view").isNone
-- visibility around a single mutability keyword is still fine
#guard (AbiItem.parse "function f() external view returns (bool)").isSome

/-! ### `params!` — parameter list to `List AbiParam` -/

#guard (params! "address spender, uint256 amount").length = 2

#guard (params! "").isEmpty

-- `parseAbi` takes one item per line and skips blank lines
#guard (parseAbi "function a(uint256)\n\nevent B(bool)\n").isSome
#guard (parseAbi "function a(uint256); event B(bool)").isNone

-- a comma must be followed by a parameter
#guard (AbiParam.parseList "address spender,").isNone
#guard (AbiItem.parse "function f(uint256 a, )").isNone
#guard (AbiItem.parse "function f(, uint256 a)").isNone

/-! ### Spec-vector `sam`: `(bytes, bool, uint256[])` -/

#eval
  let t := ty! "(bytes, bool, uint256[])"
  let v : t.Val :=
    (⟨[0x64, 0x61, 0x76, 0x65], by decide⟩, (true,
      (⟨[⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩, ())))
  encode t v

example :
  let t := ty! "(bytes, bool, uint256[])"
  let v : t.Val :=
    (⟨[0x64, 0x61, 0x76, 0x65], by decide⟩, (true,
      (⟨[⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩, ())))
  decodeStrict t (encode t v) = some v
:= by
  intro t v; apply decodeStrict_encode t (by native_decide) v (by native_decide)

end HumanReadable

/-! ## Builder form (roadmap node 9) -/

-- Materialization agrees with the legacy encoders.
#eval (putUint 42).toList == encodeUint 42                      -- true
#eval (putBytes [1, 2, 3]).toList == encodeBytes [1, 2, 3]      -- true

example : (putUint 42).toList = encodeUint 42 := by native_decide
example : (putBytes [1, 2, 3]).toList = encodeBytes [1, 2, 3] := by native_decide

-- Builder composition: O(1) sequencing, materialized once.
#eval (putUint 42 ++ putBool true ++ putBytes [1, 2, 3]).toList.length  -- 128

end EvmAbi
