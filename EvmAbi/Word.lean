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

/-- Reading a freshly written word at offset 0. -/
theorem wordAt_zero (w : UInt256) (rest : List UInt8) :
    wordAt (bytesOfWord w ++ rest) 0 = some w := by
  have e := wordAt_append ([] : List UInt8) rest w 0 (by simp)
  simpa using e

/-- `natAt` variant of the read-back theorem. -/
theorem natAt_append (buf rest : List UInt8) (w : UInt256) (i : Nat)
    (h : buf.length = 32 * i) :
    natAt (buf ++ (bytesOfWord w ++ rest)) i = some w.toNat := by
  simp [natAt, wordAt_append buf rest w i h]

/-- Reading past the end of a short buffer fails gracefully. -/
theorem wordAt_none_of_short (buf : List UInt8) (i : Nat)
    (h : buf.length < 32 * i + 32) :
    wordAt buf i = none := by
  unfold wordAt
  have hn : ¬ (((buf.drop (32 * i)).take 32).length = 32) := by
    rw [List.length_take, List.length_drop]; omega
  rw [if_neg hn]

end EvmAbi
