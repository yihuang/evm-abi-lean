import EvmAbi.Static

/-!
# EvmAbi.StaticArray

Static arrays `T[k]` (roadmap node 6) over single-word static elements
(`uintM`, `intM`, `bool`, `address`, `bytesN`): the encoding of `T[k]` is the
concatenation of the `k` element words.

The decoder is naturally prefix-style (it consumes exactly `k` words from
the front of the buffer), which is what tuple decoding needs later.
-/

namespace EvmAbi

open Binary

/-- Encode a list of words as a static array: concatenated 32-byte words. -/
def encodeWordArray (ws : List UInt256) : List UInt8 := (ws.map bytesOfWord).flatten

/-- Cons decomposition of the encoding. -/
theorem encodeWordArray_cons (w : UInt256) (ws : List UInt256) :
    encodeWordArray (w :: ws) = bytesOfWord w ++ encodeWordArray ws := rfl

@[simp] theorem length_encodeWordArray (ws : List UInt256) :
    (encodeWordArray ws).length = 32 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simp [encodeWordArray_cons, List.length_append, length_bytesOfWord, ih]; omega

theorem dvd_length_encodeWordArray (ws : List UInt256) : 32 ∣ (encodeWordArray ws).length :=
  ⟨ws.length, by simp⟩

/-- Decode `k` consecutive words from the front of a buffer. -/
def decodeWordArray : Nat → List UInt8 → Option (List UInt256)
  | 0,     _   => some []
  | k + 1, buf =>
      match wordAt buf 0 with
      | none => none
      | some w => (decodeWordArray k (buf.drop 32)).map (w :: ·)

/-- **Roundtrip** for static arrays. -/
theorem decodeWordArray_encodeWordArray (ws : List UInt256) :
    decodeWordArray ws.length (encodeWordArray ws) = some ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      rw [List.length_cons, encodeWordArray_cons, decodeWordArray, wordAt_zero,
        drop_append_of_length (length_bytesOfWord w), ih]
      simp

/-- Reading a word one step in is reading in the tail of the buffer. -/
theorem wordAt_succ (buf : List UInt8) (i : Nat) :
    wordAt buf (i + 1) = wordAt (buf.drop 32) i := by
  unfold wordAt
  have e : 32 * (i + 1) = 32 + 32 * i := by omega
  rw [e, ← List.drop_drop]

/-- Element access: word `i` of an encoded static array is element `i`. -/
theorem wordAt_encodeWordArray (ws : List UInt256) (i : Nat) (hi : i < ws.length) :
    wordAt (encodeWordArray ws) i = some ws[i] := by
  induction ws generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons w ws ih =>
      cases i with
      | zero => rw [encodeWordArray_cons]; exact wordAt_zero w _
      | succ i =>
          rw [encodeWordArray_cons, wordAt_succ,
            drop_append_of_length (length_bytesOfWord w)]
          exact ih i (Nat.lt_of_succ_lt_succ hi)

end EvmAbi
