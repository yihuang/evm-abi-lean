import EvmAbi.Bytes
import EvmAbi.Align
import EvmAbi.Word
import EvmAbi.Ty
import EvmAbi.Builder
import EvmAbi.Static
import EvmAbi.Dynamic
import EvmAbi.Codec
import EvmAbi.Codec.Strict
import EvmAbi.Codec.ByteArray
import EvmAbi.Codec.Runtime
import EvmAbi.Parts
import EvmAbi.Packed
import EvmAbi.HumanReadable
import EvmAbi.HumanReadable.Meta
import EvmAbi.Compile.Meta

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

example : Spec.decodeStrict (.uint 8) (Spec.encode (.uint 8) ⟨200, by decide⟩) = some ⟨200, by decide⟩ := by
  native_decide

example : Spec.decodeStrict (.int 16) (Spec.encode (.int 16) ⟨-1000, by decide⟩) = some ⟨-1000, by decide⟩ := by
  native_decide

example : Spec.decodeStrict .bool (Spec.encode .bool true) = some true := by native_decide

example : Spec.decodeStrict (.bytesN 5) (Spec.encode (.bytesN 5) ⟨[1,2,3,4,5], rfl⟩)
    = some ⟨[1,2,3,4,5], rfl⟩ := by native_decide

example : Spec.decodeStrict .bytes (Spec.encode .bytes ⟨[0x61, 0x62, 0x63], by decide⟩)
    = some ⟨[0x61, 0x62, 0x63], by decide⟩ := by native_decide

example : Spec.decodeStrict .string (Spec.encode .string ⟨"Hello, world!", by native_decide⟩)
    = some ⟨"Hello, world!", by native_decide⟩ := by native_decide

-- The same instances via library theorems (no computation)

example : Spec.decodeStrict (.uint 8) (Spec.encode (.uint 8) ⟨200, by decide⟩) = some ⟨200, by decide⟩ :=
  Spec.decodeStrict_encode (.uint 8) (by native_decide) _ (by native_decide)

example : Spec.decodeStrict (.int 8) (Spec.encode (.int 8) ⟨-5, by decide⟩) = some ⟨-5, by decide⟩ :=
  Spec.decodeStrict_encode (.int 8) (by native_decide) _ (by native_decide)

example : Spec.decodeStrict .bool (Spec.encode .bool false) = some false :=
  Spec.decodeStrict_encode .bool (by native_decide) _ (by native_decide)

example : Spec.decodeStrict .bytes (Spec.encode .bytes ⟨[1, 2, 3], by decide⟩) =
    some ⟨[1, 2, 3], by decide⟩ :=
  Spec.decodeStrict_encode .bytes (by native_decide) _ (by native_decide)

example : Spec.decodeStrict .string (Spec.encode .string ⟨"hello", by native_decide⟩) =
    some ⟨"hello", by native_decide⟩ :=
  Spec.decodeStrict_encode .string (by native_decide) _ (by native_decide)

-- encodeStatic_length

example : (Spec.encode (.uint 256) ⟨42, by decide⟩).length = 32 := by
  rw [Spec.encode_length_static (.uint 256) rfl (by native_decide) ⟨42, by decide⟩]
  simp [headSize]

-- Spec.encode_length_aligned

example : Aligned (Spec.encode .bytes ⟨[1, 2, 3], by decide⟩).length :=
  Spec.encode_length_aligned .bytes (by native_decide) _

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

-- end-to-end: prefix-Spec.decode the dynamic bytes value at its tail offset
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

example : Spec.encode specSamTy specSamVal = specSamBytes := by native_decide
example : Spec.encode specFTy specFVal = specFBytes := by native_decide
example : Spec.encode specGTy specGVal = specGBytes := by native_decide

example : Spec.decodeStrict specSamTy (Spec.encode specSamTy specSamVal) = some specSamVal :=
  Spec.decodeStrict_encode specSamTy (by native_decide) specSamVal (by native_decide)

example : Spec.decodeStrict specFTy (Spec.encode specFTy specFVal) = some specFVal :=
  Spec.decodeStrict_encode specFTy (by native_decide) specFVal (by native_decide)

-- the spec encodings are canonical (strictly decodable, no trailing garbage)
example : Spec.IsCanonical specSamTy specSamBytes := by native_decide
example : Spec.IsCanonical specFTy specFBytes := by native_decide
example : Spec.IsCanonical specGTy specGBytes := by native_decide

-- and are strictly decodable (checked via `.isSome` since the dependent
-- return type has no `DecidableEq` instance)
example : (Spec.decodeStrict specSamTy specSamBytes).isSome = true := by native_decide
example : (Spec.decodeStrict specFTy specFBytes).isSome = true := by native_decide
example : (Spec.decodeStrict specGTy specGBytes).isSome = true := by native_decide

-- the same instances via library theorems (no computation)

example : Spec.IsCanonical specSamTy (Spec.encode specSamTy specSamVal) :=
  Spec.isCanonical_encode specSamTy (by native_decide) specSamVal (by native_decide)

example : Spec.decodeStrict specSamTy (Spec.encode specSamTy specSamVal) = some specSamVal :=
  Spec.decodeStrict_encode specSamTy (by native_decide) specSamVal (by native_decide)

/-! ## C4: bounds are intrinsic, image characterization -/

-- forward: a canonical buffer IS an encoding — no bound on the value side
example : ∃ v, Spec.encode specSamTy v = specSamBytes :=
  (Spec.isCanonical_iff specSamTy (by native_decide) specSamBytes (by native_decide)).mp
    (by unfold Spec.IsCanonical; native_decide)

-- backward: canonicity of an encoding through the iff
example : Spec.IsCanonical specSamTy (Spec.encode specSamTy specSamVal) :=
  (Spec.isCanonical_iff specSamTy (by native_decide) _ (by native_decide)).mpr
    ⟨specSamVal, rfl⟩

-- the strict roundtrip through the strict-decoder characterization
example : Spec.decodeStrict specSamTy (Spec.encode specSamTy specSamVal) = some specSamVal :=
  (Spec.decodeStrict_eq_some_iff specSamTy (by native_decide) _ specSamVal
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
example : (Spec.decodeStrict ncTy ncSharedTail).isNone = true := by native_decide
example : (Spec.decodeStrict ncTy ncSwapped).isNone = true := by native_decide
example : (Spec.decodeStrict ncTy ncGap).isNone = true := by native_decide
example : (Spec.decodeStrict ncTy ncIntoHead).isNone = true := by native_decide
example : (Spec.decodeStrict ncTy ncMisaligned).isNone = true := by native_decide

-- trailing garbage: the strict decoder rejects it
example : (Spec.decodeStrict specSamTy (specSamBytes ++ [0])).isNone = true := by native_decide

/-! ## The consumed count is structural

`Spec.decode` reports how many bytes it consumed, so `decodeElem` advances the
tail frontier in `O(1)` instead of measuring the cursors — the count is
the encoding's length, and the remainder is untouched. -/

-- a prefix Spec.decode through trailing data reports the encoding length
example :
    Spec.decode .bytes (encodeBytes [1, 2, 3] ++ [0xFF]) =
      some (⟨[1, 2, 3], by decide⟩, 64, [0xFF]) := by native_decide

example :
    Spec.decode (.uint 8) (Spec.encode (.uint 8) ⟨7, by decide⟩ ++ [0xFF]) =
      some (⟨7, by decide⟩, 32, [0xFF]) := by native_decide

-- a compound value's count is its whole layout, head plus tails
example :
    (Spec.decode specSamTy (specSamBytes ++ [0xFF])).map (fun p => (p.2.1, p.2.2)) =
      some (specSamBytes.length, [0xFF]) := by native_decide

/-! ## Zero-head element types are rejected

An element type occupying no head bytes (`()`, `T[0]`) would let a
32-byte length word name arbitrarily many elements, with the element walk
bounded by nothing.  Such array types are invalid, and `Spec.decode` rejects
them before reading the length word. -/

example : ¬ (Ty.array (.tuple [])).Valid := by decide
example : ¬ (Ty.array (.fixedArray (.uint 8) 0)).Valid := by decide

-- the element type itself stays valid — it is only its array that is not
example : (Ty.tuple []).Valid := by decide

-- a 32-byte buffer claiming 2^64 elements is rejected outright
example : (Spec.decodeStrict (.array (.tuple [])) (encodeUint (2 ^ 64))).isNone = true := by
  native_decide

/-! ## Primitive reads at a `ByteArray` offset

Each agrees with its list counterpart on the suffix — that is
`decodeUintBA_eq` and friends — and the window is clamped to the buffer, so
a length word off the wire cannot size an allocation. -/

/-- Head section of `(uint256, bytes)`: a word then an offset word. -/
def baBuf : ByteArray :=
  Spec.encodeByteArray (.tuple [.uint 256, .bytes])
    (⟨7, by decide⟩, (⟨[1, 2, 3], by decide⟩, ()))

example : decodeUintBA baBuf 0 = decodeUint (baBuf.data.toList.drop 0) := by native_decide
example : decodeUintBA baBuf 32 = decodeUint (baBuf.data.toList.drop 32) := by native_decide
example : decodeBoolBA baBuf 0 = decodeBool (baBuf.data.toList.drop 0) := by native_decide
example : decodeBytesPrefixBA baBuf 64 = decodeBytesPrefix (baBuf.data.toList.drop 64) := by
  native_decide

-- reading past the end is `none`, not a crash
example : decodeUintBA baBuf 1000 = none := by native_decide

-- an attacker-chosen length must not size the copy: the window clamps, so
-- this is 32 bytes and not a request for `2 ^ 200`
example : (windowList baBuf 0 (2 ^ 200)).length = baBuf.size := by native_decide

/-! ## The offset-cursor decoder

`decodeStrictBA` walks the buffer by offset instead of converting it to a
list and slicing.  `decodeStrictBA_eq` says the two agree, so these check
the computation matches the theorem — on the spec vectors, and on the same
non-canonical inputs the list decoder rejects. -/

example : decodeStrictBA specSamTy (Spec.encodeByteArray specSamTy specSamVal) = some specSamVal :=
  decodeStrictBA_encodeByteArray specSamTy (by native_decide) specSamVal (by native_decide)

example : (decodeStrictBA specFTy (Spec.encodeByteArray specFTy specFVal)).isSome = true := by
  native_decide
example : (decodeStrictBA specGTy (Spec.encodeByteArray specGTy specGVal)).isSome = true := by
  native_decide

-- the offset walk and the list walk decide the same buffers
example : (decodeStrictBA specSamTy specSamBytes.toByteArray).isSome =
    (Spec.decodeStrict specSamTy specSamBytes).isSome := by native_decide

example : IsCanonicalBA specSamTy specSamBytes.toByteArray := by native_decide

-- and the capstones themselves, as theorems (no computation)
example : ∃ v, Spec.encodeByteArray specSamTy v = Spec.encodeByteArray specSamTy specSamVal :=
  (isCanonicalBA_iff specSamTy (by native_decide) _ (by native_decide)).mp
    (by unfold IsCanonicalBA
        rw [decodeStrictBA_encodeByteArray specSamTy (by native_decide) specSamVal
          (by native_decide)]
        rfl)

example : decodeStrictBA specGTy (Spec.encodeByteArray specGTy specGVal) = some specGVal :=
  (decodeStrictBA_eq_some_iff specGTy (by native_decide) _ specGVal (by native_decide)).mpr rfl

-- the non-canonical vectors are rejected by the offset walk too
example : (decodeStrictBA ncTy ncSharedTail.toByteArray).isNone = true := by native_decide
example : (decodeStrictBA ncTy ncSwapped.toByteArray).isNone = true := by native_decide
example : (decodeStrictBA ncTy ncGap.toByteArray).isNone = true := by native_decide
example : (decodeStrictBA ncTy ncIntoHead.toByteArray).isNone = true := by native_decide
example : (decodeStrictBA ncTy ncMisaligned.toByteArray).isNone = true := by native_decide

-- trailing garbage: the exact-consumption check is now `n = ba.size`
example : (decodeStrictBA specSamTy (specSamBytes ++ [0]).toByteArray).isNone = true := by
  native_decide

-- degenerate inputs behave the same on both paths
example : (decodeStrictBA (.uint 256) ByteArray.empty).isNone = true := by native_decide
example : (decodeStrictBA (.tuple []) ByteArray.empty).isSome = true := by native_decide
example : (decodeStrictBA (.array (.uint 256))
    (Spec.encodeByteArray (.array (.uint 256)) ⟨[], by decide⟩)).isSome = true := by native_decide
example : (decodeStrictBA .bytes (Spec.encodeByteArray .bytes ⟨[], by decide⟩)).isSome = true := by
  native_decide

-- the zero-head guard and the window clamp hold on the offset path too
example : (decodeStrictBA (.array (.tuple [])) (encodeUint (2 ^ 64)).toByteArray).isNone = true := by
  native_decide
example : (decodeStrictBA .bytes (encodeUint (2 ^ 200)).toByteArray).isNone = true := by
  native_decide

-- truncating an encoding anywhere is rejected by both, identically
example :
  let t : Ty := .tuple [.bytes, .uint 8]
  let v : t.Val := (⟨[1, 2, 3], by decide⟩, (⟨9, by decide⟩, ()))
  let ba := Spec.encodeByteArray t v
  ∀ i ∈ [0, 1, 31, 32, 63, 64, 95, 96, 127],
    (decodeStrictBA t (ba.extract 0 i)).isSome = (Spec.decodeStrict t (ba.extract 0 i).data.toList).isSome
:= by native_decide

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

-- Invalid widths (m % 8 ≠ 0) are rejected at Spec.decode — encodeBEU truncates
-- them, so accepting them would let a lossy Spec.encode "roundtrip".
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
gets stuck under `decide`).  Array clauses defer to the standard `Spec.encode`
and stay `native_decide`-only. -/

example : encodePacked .bool true = [1] := by decide
example : encodePacked (.uint 8) ⟨42, by decide⟩ = [42] := by decide
example : encodePacked (.tuple [.uint 8, .bool]) (⟨42, by decide⟩, (true, ())) =
    [42, 1] := by decide
example : decodePacked (.uint 8) [42] = some ⟨42, by decide⟩ := by decide

/-! ## Packed ABI: large scalar tuples (linear walk) -/

/-- A replicated `uint8` tuple: `n` copies of `42`. -/
def repU8 : (n : Nat) → TupleVal (List.replicate n (.uint 8))
  | 0 => ()
  | n + 1 => (⟨42, by decide⟩, repU8 n)

-- Roundtrip a 1024-element flat scalar tuple in a single walk.  Every
-- scalar primitive only ever touches its own component width (the
-- take-based sufficiency check), so the walk is linear in the tuple
-- length rather than quadratic in it.
example : decodePacked (.tuple (List.replicate 1024 (.uint 8)))
    (encodePacked (.tuple (List.replicate 1024 (.uint 8))) (repU8 1024)) =
    some (repU8 1024) := by
  apply roundtrip_packed_static
  · native_decide
  · native_decide

-- Decode larger flat scalar tuples in a single walk.  With the old
-- length-based primitives each step re-measured the whole remaining
-- cursor (`O(k²)` total); the counted take-based check keeps every step
-- bounded by the component's own width, so these finish in a single
-- linear pass.
#eval (decodePacked (.tuple (List.replicate 4096 (.uint 8)))
    (encodePacked (.tuple (List.replicate 4096 (.uint 8))) (repU8 4096))).isSome  -- true
#eval (decodePacked (.tuple (List.replicate 8192 (.uint 8)))
    (encodePacked (.tuple (List.replicate 8192 (.uint 8))) (repU8 8192))).isSome  -- true

/-! ## Builder

The builder denotes the byte list it stands for, and `run` produces exactly
those bytes.  `Builder` is structurally recursive, so `decide` evaluates it. -/

example : (Builder.ofList [1, 2, 3]).toList = [1, 2, 3] := by decide
example : (Builder.zeros 4).toList = [0, 0, 0, 0] := by decide
example : (Builder.ofList [1] ++ (∅ : Builder) ++ Builder.zeros 2).toList = [1, 0, 0] := by decide

-- the cached size is the denotation's length, by construction
example : (Builder.ofList [1, 2, 3] ++ Builder.zeros 29).size = 32 := by decide
example : ∀ b : Builder, b.size = b.toList.length := Builder.size_eq_length_toList

-- `run` materialises the denotation
example : (Builder.ofList [1, 2] ++ Builder.zeros 2).run.data.toList = [1, 2, 0, 0] := by
  native_decide
example : (Builder.chunk "hi".toUTF8).run.data.toList = [0x68, 0x69] := by native_decide

/-! ## Executable encoder

`Spec.encodeByteArray` runs the very builder `Spec.encode` materializes, into a
`ByteArray`.  It agrees with the specification encoder on the Solidity spec
vectors — and by `Spec.data_toList_encodeByteArray`, on *every* value, with no
computation. -/

#eval (Spec.encodeByteArray specSamTy specSamVal).size    -- 320

example : (Spec.encodeByteArray specSamTy specSamVal).data.toList = specSamBytes := by native_decide
example : (Spec.encodeByteArray specFTy specFVal).data.toList = specFBytes := by native_decide
example : (Spec.encodeByteArray specGTy specGVal).data.toList = specGBytes := by native_decide

example : Spec.encodeByteArray specSamTy specSamVal = specSamBytes.toByteArray := by native_decide

-- the same instances via the library theorem (no computation)
example : (Spec.encodeByteArray specSamTy specSamVal).data.toList = Spec.encode specSamTy specSamVal :=
  Spec.data_toList_encodeByteArray specSamTy specSamVal

example : Spec.encodeByteArray specGTy specGVal = (Spec.encode specGTy specGVal).toByteArray :=
  Spec.encodeByteArray_eq specGTy specGVal

-- and the roundtrip transported onto it
example : Spec.decode specSamTy (Spec.encodeByteArray specSamTy specSamVal).data.toList =
    some (specSamVal, (Spec.encode specSamTy specSamVal).length, []) :=
  Spec.decode_encodeByteArray specSamTy (by native_decide) specSamVal (by native_decide)

example : Spec.decodeStrict specFTy (Spec.encodeByteArray specFTy specFVal).data.toList = some specFVal :=
  Spec.decodeStrict_encodeByteArray specFTy (by native_decide) specFVal (by native_decide)

example : (Spec.encodeByteArray specGTy specGVal).size = (Spec.encode specGTy specGVal).length :=
  Spec.size_encodeByteArray specGTy specGVal

/-!
## Human-readable ABI

User-facing APIs: compile-time macros (`ty!`, `item!`, `params!`) for
`Spec.encode`/`Spec.decode`, and the curried runtime parsers (`Ty.parse`,
`AbiItem.parse`).
-/

section HumanReadable

/-! ### `ty!` — compile-time type → Spec.encode/Spec.decode roundtrip

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
#eval (Spec.encode composite compositeVal).take 64

example : (Spec.encode composite compositeVal).length = 576 := by native_decide

example : Spec.decodeStrict composite (Spec.encode composite compositeVal) = some compositeVal :=
  Spec.decodeStrict_encode composite composite_valid _ (by native_decide)

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

example : Spec.decodeStrict structArray (Spec.encode structArray structArrayVal) = some structArrayVal :=
  Spec.decodeStrict_encode structArray structArray_valid _ (by native_decide)

/-! ### `item!` — function/event/error signatures → call-data encoding -/

-- ERC-20 `transfer(address,uint256)` — two-argument function

example :
  let item := item! "function transfer(address to, uint256 amount) returns (bool)"
  let t := item.inputsTy
  let v : t.Val := (⟨0xABCDEF, by decide⟩, (⟨1000, by decide⟩, ()))
  Spec.decodeStrict t (Spec.encode t v) = some v
:= by
  intro item t v; apply Spec.decodeStrict_encode t (by native_decide) v (by native_decide)

-- ERC-20 `balanceOf(address)` — single-argument function, view modifier

#eval
  let item := item! "function balanceOf(address account) view returns (uint256)"
  Spec.encode item.inputsTy (⟨0xABCDEF, by decide⟩, ())

-- A single argument stays wrapped in a tuple: for a dynamic argument the
-- call-data block leads with the offset word, which the bare `bytes` encoding
-- would omit.

example : (item! "function f(bytes data)").inputsTy = .tuple [.bytes] := rfl

example :
  let t := (item! "function f(bytes data)").inputsTy
  let v : t.Val := (⟨[0x61, 0x62, 0x63], by decide⟩, ())
  (Spec.encode t v).take 32 = encodeUint 0x20 := by native_decide

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
  Spec.encode t v

example :
  let t := ty! "(bytes, bool, uint256[])"
  let v : t.Val :=
    (⟨[0x64, 0x61, 0x76, 0x65], by decide⟩, (true,
      (⟨[⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩, ())))
  Spec.decodeStrict t (Spec.encode t v) = some v
:= by
  intro t v; apply Spec.decodeStrict_encode t (by native_decide) v (by native_decide)

end HumanReadable

/-! ## Builder form (roadmap node 9) -/

-- Materialization agrees with the legacy encoders.
#eval (putUint 42).toList == encodeUint 42                      -- true
#eval (putBytes [1, 2, 3]).toList == encodeBytes [1, 2, 3]      -- true

example : (putUint 42).toList = encodeUint 42 := by native_decide
example : (putBytes [1, 2, 3]).toList = encodeBytes [1, 2, 3] := by native_decide

-- Builder composition: O(1) sequencing, materialized once.
#eval (putUint 42 ++ putBool true ++ putBytes [1, 2, 3]).toList.length  -- 128

/-! ## Runtime API (primary names)

`encode`, `decode`, `decodeStrict` and `IsCanonical` are the user-facing
runtime codec: `ValBA` values in, `ByteArray` out and back.  The `Spec`
namespace holds the list-based specification they are proved against. -/

example : (decodeStrict (.uint 8) (encode (.uint 8) ⟨200, by decide⟩)) =
    some ⟨200, by decide⟩ := by native_decide

example : (decodeStrict .bytes (encode .bytes ⟨"hi".toUTF8, by native_decide⟩)) =
    some ⟨"hi".toUTF8, by native_decide⟩ := by native_decide

example : IsCanonical .bool (encode .bool true) := by native_decide

example : (encode .bool true).data.toList = Spec.encode .bool true := by
  simp [ValBA.toList, data_toList_encode]

/-! ### …and the same properties by theorem

The instances above are computed; these are the runtime capstones applied, so
they hold for *every* value. -/

example (v : ValBA (.uint 8)) (hb : (encode (.uint 8) v).size < 2 ^ 256) :
    decodeStrict (.uint 8) (encode (.uint 8) v) = some v :=
  decodeStrict_encode (.uint 8) (by decide) v hb

example (v : ValBA specSamTy) (hb : (encode specSamTy v).size < 2 ^ 256) :
    decodeStrict specSamTy (encode specSamTy v) = some v :=
  decodeStrict_encode specSamTy (by native_decide) v hb

example (ba : ByteArray) (v : ValBA specSamTy) (h : decodeStrict specSamTy ba = some v) :
    encode specSamTy v = ba :=
  encode_of_decodeStrict specSamTy (by native_decide) ba v h

example (ba : ByteArray) (hb : ba.size < 2 ^ 256) :
    IsCanonical specSamTy ba ↔ ∃ v, encode specSamTy v = ba :=
  isCanonical_iff specSamTy (by native_decide) ba hb

example (v w : ValBA specSamTy) (h : ValBA.toList specSamTy v = ValBA.toList specSamTy w) :
    v = w :=
  ValBA.toList_injective specSamTy h

/-! ## The ABI compiler (`EvmAbi.Compile.Meta`)

`abi_encoder` / `abi_decoder` / `abi_codec` emit a codec specialised to one
type, plus the theorems that it agrees with `encode` / `decodeStrict`.  The
vectors below are the same three the spec-vector section checks — encoded here
by *compiled* code, so the compiler is held to the published bytes, not merely
to the generic encoder. -/

open EvmAbi.Compile.Meta

abi_codec samArgs "sam(bytes, bool, uint256[])"
abi_encoder fArgs "f(uint256, uint32[], bytes10, bytes)"
abi_encoder gArgs "(uint256[][], string[])"

def samArgsVal : ValBA samArgs.ty :=
  (⟨⟨#[0x64, 0x61, 0x76, 0x65]⟩, by decide⟩, true,
    ⟨[⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩], by decide⟩, ())

def fArgsVal : ValBA fArgs.ty :=
  (⟨0x123, by decide⟩,
    ⟨[⟨0x456, by decide⟩, ⟨0x789, by decide⟩], by decide⟩,
    ⟨⟨#[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30]⟩, by decide⟩,
    ⟨⟨#[0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x2c, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21]⟩,
      by decide⟩, ())

def gArgsVal : ValBA gArgs.ty :=
  (⟨[⟨[⟨1, by decide⟩, ⟨2, by decide⟩], by decide⟩, ⟨[⟨3, by decide⟩], by decide⟩], by decide⟩,
    ⟨[⟨"one", by native_decide⟩, ⟨"two", by native_decide⟩, ⟨"three", by native_decide⟩],
      by decide⟩, ())

-- byte-exact against the specification vectors
example : (samArgs.encode samArgsVal).data.toList = specSamBytes := by native_decide
example : (fArgs fArgsVal).data.toList = specFBytes := by native_decide
example : (gArgs gArgsVal).data.toList = specGBytes := by native_decide

-- …and the compiled encoders are the generic one, by theorem: no computation,
-- every value.  This is what the command proves as it emits the code.
example (v : ValBA samArgs.ty) : samArgs.encode v = encode samArgs.ty v := samArgs.encode_eq v
example (v : ValBA gArgs.ty) : gArgs v = encode gArgs.ty v := gArgs_eq v

-- the verified roundtrip transports to compiled output for free
example (v : ValBA fArgs.ty) (hb : (fArgs v).size < 2 ^ 256) :
    decodeStrict fArgs.ty (fArgs v) = some v := fArgs_decodeStrict v hb

example : (decodeStrict gArgs.ty (gArgs gArgsVal)).isSome := by native_decide

-- every clause of the type grammar goes through the compiler
abi_codec allTys "(uint8, int64, bool, address, bytes4, bytes, string, (bool, bytes)[2],
  uint16[][], (address, (uint256, bytes)))"

example (v : ValBA allTys.ty) : allTys.encode v = encode allTys.ty v := allTys.encode_eq v

def allTysVal : ValBA allTys.ty :=
  (⟨7, by decide⟩, ⟨-9, by decide⟩, false, ⟨0xbeef, by decide⟩,
    ⟨⟨#[1, 2, 3, 4]⟩, by decide⟩, ⟨⟨#[9, 9]⟩, by decide⟩, ⟨"hi", by native_decide⟩,
    ⟨[(true, ⟨⟨#[1]⟩, by decide⟩, ()), (false, ⟨⟨#[]⟩, by decide⟩, ())], by decide⟩,
    ⟨[⟨[⟨1, by decide⟩], by decide⟩], by decide⟩,
    (⟨0xcafe, by decide⟩, (⟨5, by decide⟩, ⟨⟨#[7, 7, 7]⟩, by decide⟩, ()), ()), ())

example : allTys.encode allTysVal == encode allTys.ty allTysVal := by native_decide
example : (decodeStrict allTys.ty (allTys.encode allTysVal)).isSome := by native_decide

-- a leaf type compiles too (the root need not be compound)
abi_encoder justBytes "bytes"

example : (justBytes ⟨⟨#[1, 2]⟩, by decide⟩).data.toList =
    encodeBytes [1, 2] := by native_decide

/-! ### the decoder side

`abi_decoder` compiles the strict decoder, `abi_codec` both directions.  The
compiled decoder *is* `decodeStrict` (that is `_eq`), so it accepts exactly
the canonical buffers — the negative vectors below are the same ones the
strictness section rejects. -/

-- the compiled decoder reads the specification's own vector
example : (samArgs.decode specSamBytes.toByteArray).isSome := by native_decide

-- and rejects what `decodeStrict` rejects: trailing garbage, …
example : (samArgs.decode (specSamBytes ++ [0]).toByteArray).isSome = false := by native_decide

-- … a truncated buffer, …
example : (samArgs.decode (specSamBytes.take 64).toByteArray).isSome = false := by native_decide

-- … and a non-canonical offset word (the `bytes` tail claimed one word early)
example : (samArgs.decode
    ((encodeUint 0x40 ++ specSamBytes.drop 32).toByteArray)).isSome = false := by native_decide

-- compiled encoder in, compiled decoder out, by computation …
example : (allTys.decode (allTys.encode allTysVal)).isSome := by native_decide

-- … and by theorem, for every value
example (v : ValBA samArgs.ty) (hb : (samArgs.encode v).size < 2 ^ 256) :
    samArgs.decode (samArgs.encode v) = some v := samArgs.roundtrip v hb

example (ba : ByteArray) : samArgs.decode ba = decodeStrict samArgs.ty ba :=
  samArgs.decode_eq ba

example (ba : ByteArray) (v : ValBA samArgs.ty) (h : samArgs.decode ba = some v) :
    encode samArgs.ty v = ba := samArgs.decode_uniq ba v h

abi_decoder justBytesDec "bytes"

example : (justBytesDec (encode .bytes ⟨⟨#[1, 2]⟩, by decide⟩)).isSome := by native_decide

end EvmAbi
