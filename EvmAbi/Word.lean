import Binary.UInt256
import EvmAbi.Bytes

/-!
# EvmAbi.Word

The 32-byte word layer (roadmap node 2): reading and writing EVM words
(`UInt256`) at aligned positions of a byte buffer.

The central fact is `wordAt_append`: a word written at an aligned position
of a buffer is read back unchanged — the minimal prototype of the offset
reasoning that the ABI head/tail scheme needs later.
-/

namespace EvmAbi

open Binary

/-- The 32 bytes of an EVM word, big-endian. -/
def bytesOfWord (w : UInt256) : List UInt8 := w.toBEBytes

theorem length_bytesOfWord (w : UInt256) : (bytesOfWord w).length = 32 :=
  UInt256.length_toBEBytes w

/-- Read the `i`-th 32-byte word (0-indexed) from a buffer;
    `none` when fewer than 32 bytes remain. -/
def wordAt (buf : List UInt8) (i : Nat) : Option UInt256 :=
  if ((buf.drop (32 * i)).take 32).length = 32 then
    some (UInt256.ofBEBytes ((buf.drop (32 * i)).take 32))
  else
    none

/-- Read the `i`-th word as a natural number. -/
def natAt (buf : List UInt8) (i : Nat) : Option Nat := (wordAt buf i).map UInt256.toNat

/-- **Read-back**: a word written at its aligned position is recovered
    unchanged, regardless of what surrounds it. -/
theorem wordAt_append (buf rest : List UInt8) (w : UInt256) (i : Nat)
    (h : buf.length = 32 * i) :
    wordAt (buf ++ (bytesOfWord w ++ rest)) i = some w := by
  have hdr : (buf ++ (bytesOfWord w ++ rest)).drop (32 * i) = bytesOfWord w ++ rest := by
    rw [← h]
    exact drop_append_of_length rfl
  have htake : (bytesOfWord w ++ rest).take 32 = bytesOfWord w :=
    take_append_of_length (length_bytesOfWord w)
  unfold wordAt
  rw [hdr, htake, if_pos (length_bytesOfWord w)]
  show some (UInt256.ofBEBytes (UInt256.toBEBytes w)) = some w
  rw [UInt256.ofBEBytes_toBEBytes]

/-- `natAt` variant of the read-back theorem. -/
theorem natAt_append (buf rest : List UInt8) (w : UInt256) (i : Nat)
    (h : buf.length = 32 * i) :
    natAt (buf ++ (bytesOfWord w ++ rest)) i = some w.toNat := by
  simp [natAt, wordAt_append buf rest w i h]

/-- Anything `natAt` reads back is below `2 ^ 256`: it came out of a
32-byte word. -/
theorem natAt_lt {buf : List UInt8} {i n : Nat} (h : natAt buf i = some n) :
    n < 2 ^ 256 := by
  simp only [natAt] at h
  cases hw : wordAt buf i with
  | none => simp only [hw, Option.map_none] at h; contradiction
  | some w =>
      simp only [hw, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact UInt256.toNat_lt w

/-! ## Reading a word straight out of a `ByteArray`

`natAt` slices: `drop` walks the buffer to the offset and `take` allocates a
fresh 32-cell list.  A reader that walks `k` words of one buffer therefore
costs `O(k · n)`.  `natAtBA` reads the same word by index —
`Binary.decodeBEBytesFrom`, which `Binary.Fast` implements without ever
touching `ba.data.toList` — so it is `O(1)` in the buffer.

`natAtBA_eq` is the bridge: the two agree, with the offset in bytes rather
than in words, so anything proved about `natAt` transports. -/

/-- Read the 32-byte word at *byte* offset `off` of a `ByteArray`, without
slicing it; `none` when fewer than 32 bytes remain. -/
def natAtBA (ba : ByteArray) (off : Nat) : Option Nat :=
  if off + 32 ≤ ba.size then some (decodeBEBytesFrom ba off 32) else none

/-- **Bridge**: the indexed read is the list read at the same position. -/
theorem natAtBA_eq (ba : ByteArray) (off : Nat) :
    natAtBA ba off = natAt (ba.data.toList.drop off) 0 := by
  have hlen : ((ba.data.toList.drop off).take 32).length = min 32 (ba.size - off) := by
    rw [List.length_take, List.length_drop, ← ByteArray.size_eq_toList_length]
  simp only [natAtBA, natAt, wordAt, Nat.mul_zero, List.drop_zero, hlen]
  by_cases h : off + 32 ≤ ba.size
  · rw [if_pos h, if_pos (by omega : min 32 (ba.size - off) = 32)]
    have h32 : ((ba.data.toList.drop off).take 32).length = UInt256.byteSize := by
      rw [hlen]; show min 32 (ba.size - off) = 32; omega
    -- exactly `byteSize` bytes fit, so nothing truncates on the way in
    have hnt : (UInt256.ofBEBytes ((ba.data.toList.drop off).take 32)).toNat =
        decodeBEU ((ba.data.toList.drop off).take 32) := by
      show (UInt256.ofNat (decodeBEU _)).toNat = _
      rw [UInt256.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      have hb := decodeBEU_lt ((ba.data.toList.drop off).take 32)
      rwa [h32] at hb
    simp only [Option.map_some, Option.some.injEq, decodeBEBytesFrom]
    exact hnt.symm
  · rw [if_neg h, if_neg (by omega : ¬ min 32 (ba.size - off) = 32)]
    rfl

/-- A word read out of a `ByteArray` is below `2 ^ 256`, like any word. -/
theorem natAtBA_lt {ba : ByteArray} {off n : Nat} (h : natAtBA ba off = some n) :
    n < 2 ^ 256 := natAt_lt (by rwa [← natAtBA_eq])

end EvmAbi
