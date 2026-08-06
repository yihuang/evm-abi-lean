import Binary.UInt256
import EvmAbi.Word
import EvmAbi.Builder

/-!
# EvmAbi.Static

Static primitive ABI types (roadmap node 4): `uintM`, `intM`, `bool`,
`address`, `bytesN`.

Every static value occupies exactly one 32-byte word, so encodings land on
the word layer (`EvmAbi.Word`) and the roundtrips follow from `natAt_append`.
Decoders are total `Option`-valued functions; the `bool` and `bytesN`
decoders are *strict* — non-canonical words are rejected with `none`.
-/

namespace EvmAbi

open Binary

/-! ## uintM -/

/-- Encode an unsigned integer as a 32-byte big-endian word
(`uintM` for every `M ≤ 256`; out-of-range values wrap mod `2^256`). -/
def encodeUint (n : Nat) : List UInt8 := bytesOfWord (UInt256.ofNat n)

@[simp] theorem length_encodeUint (n : Nat) : (encodeUint n).length = 32 :=
  length_bytesOfWord _

/-- Decode the word at offset 0 as a natural number. -/
def decodeUint (buf : List UInt8) : Option Nat := natAt buf 0

/-- **Roundtrip**: decode after encode is the identity below `2^256`. -/
theorem decodeUint_encodeUint (h : n < 2 ^ 256) :
    decodeUint (encodeUint n) = some n := by
  have e := natAt_append ([] : List UInt8) [] (UInt256.ofNat n) 0 (by simp)
  simp only [List.nil_append, List.append_nil] at e
  have hn : (UInt256.ofNat n).toNat = n := by
    rw [UInt256.toNat_ofNat]; exact Nat.mod_eq_of_lt h
  unfold decodeUint encodeUint
  rw [e, hn]

/-! ## intM -/

/-- Encode a signed integer as two's complement in a 32-byte word. -/
def encodeInt (i : Int) : List UInt8 :=
  encodeUint (if 0 ≤ i then i.toNat else 2 ^ 256 - (-i).toNat)

/-- Decode a word as a signed integer (two's complement). -/
def decodeInt (buf : List UInt8) : Option Int :=
  (decodeUint buf).map fun (n : Nat) =>
    if n < 2 ^ 255 then (n : Int) else (n : Int) - 2 ^ 256

/-- The `M`-bit two's-complement value bounds fit inside the full
256-bit range, so the `M`-bit encoding decodes back through the 256-bit
word decoder.  Shared by `decodeInt_encodeInt` and `decodeInt_append`. -/
theorem intM_bounds_lt_255 {M : Nat} (hM0 : 0 < M) (hM : M ≤ 256)
    (hl : -(2 ^ (M - 1)) ≤ i) (hu : i < 2 ^ (M - 1)) :
    -(2 : Int) ^ 255 ≤ i ∧ i < (2 : Int) ^ 255 := by
  have hb : (2 : Int) ^ (M - 1) ≤ 2 ^ 255 := by
    have e : (2 : Int) ^ (M - 1) = ((2 ^ (M - 1) : Nat) : Int) :=
      (Int.natCast_pow 2 (M - 1)).symm
    have hle : (2 : Nat) ^ (M - 1) ≤ 2 ^ 255 :=
      Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
    rw [e]; exact Int.ofNat_le.mpr hle
  constructor <;> omega

/-- **Roundtrip for `intM`**: decode after encode is the identity in range. -/
theorem decodeInt_encodeInt {M : Nat} (hM0 : 0 < M) (hM : M ≤ 256)
    (hl : -(2 ^ (M - 1)) ≤ i) (hu : i < 2 ^ (M - 1)) :
    decodeInt (encodeInt i) = some i := by
  obtain ⟨hlb, hub⟩ := intM_bounds_lt_255 (M := M) hM0 hM hl hu
  by_cases hi : 0 ≤ i
  · have hn : i.toNat < 2 ^ 256 := by omega
    rw [encodeInt, if_pos hi, decodeInt, decodeUint_encodeUint hn, Option.map_some,
      if_pos (show i.toNat < 2 ^ 255 by omega), Int.toNat_of_nonneg hi]
  · have hn1 : 2 ^ 256 - (-i).toNat ≥ 2 ^ 255 ∧ 2 ^ 256 - (-i).toNat < 2 ^ 256 := by
      omega
    rw [encodeInt, if_neg hi, decodeInt, decodeUint_encodeUint hn1.2, Option.map_some,
      if_neg (show ¬ 2 ^ 256 - (-i).toNat < 2 ^ 255 by omega)]
    have heq : ((2 ^ 256 - (-i).toNat : Nat) : Int) - 2 ^ 256 = i := by omega
    rw [heq]

/-! ## bool -/

/-- Encode a boolean as `0` / `1` in a 32-byte word. -/
def encodeBool (b : Bool) : List UInt8 := encodeUint (if b then 1 else 0)

/-- Strict boolean decoder: any word other than `0` and `1` is rejected. -/
def decodeBool (buf : List UInt8) : Option Bool :=
  match decodeUint buf with
  | some 0 => some false
  | some 1 => some true
  | _      => none

/-! ## address -/

/-- EVM `address`: a 160-bit value, encoded exactly like `uint160`
(right-aligned in the word). -/
def encodeAddress (a : Nat) : List UInt8 := encodeUint a

/-- Decode an address word. -/
def decodeAddress (buf : List UInt8) : Option Nat := decodeUint buf

/-! ## bytesN -/

/-- Encode fixed-size bytes (`bytesN`): left-aligned, right zero-padded
to 32 bytes. -/
def encodeBytesN (bs : List UInt8) : List UInt8 := bs ++ List.replicate (32 - bs.length) 0

theorem length_encodeBytesN (h : bs.length ≤ 32) : (encodeBytesN bs).length = 32 := by
  simp [encodeBytesN]; omega

/-- Prefix-tolerant `bytesN` decoder: reads the 32-byte word at the front of
the buffer; the payload is its first `n` bytes and the rest of the *word*
must be zero padding.  Anything beyond the word is ignored, so the decoder
composes inside a head section (strictness is a separate concern). -/
def decodeBytesN (n : Nat) (buf : List UInt8) : Option (List UInt8) :=
  if ((buf.take 32).take n).length = n ∧ (buf.take 32).drop n = List.replicate (32 - n) 0 then
    some ((buf.take 32).take n)
  else none

/-- A successful `decodeBytesN` yields exactly `n` bytes. -/
theorem decodeBytesN_length {n : Nat} {buf bs : List UInt8}
    (h : decodeBytesN n buf = some bs) : bs.length = n := by
  unfold decodeBytesN at h
  split at h
  · next hc =>
      rw [Option.some.injEq] at h
      subst h
      exact hc.1
  · contradiction

/-! ## Builder form (roadmap node 9)

The same primitives in builder form (`EvmAbi.Builder`): puts compose
with `Builder.append` in `O(1)` and materialize via `toList`, matching
the list-based API above through the `toList_*` lemmas.
-/

/-- The word encoding as a plain big-endian byte string.  `256 ^ 32 = 2 ^ 256`,
so a width-32 encoding truncates exactly where `UInt256` does;
`encodeBEU_mod_of_dvd` wants that as a divisibility. -/
theorem encodeUint_eq (n : Nat) : encodeUint n = encodeBEU 32 n := by
  have h : 256 ^ 32 ∣ 2 ^ 256 := by omega
  simp [encodeUint, bytesOfWord, UInt256.toBEBytes, UInt256.toNat_ofNat,
    UInt256.byteSize, UInt256.size, encodeBEU_mod_of_dvd h]

theorem toList_chunk_encodeBEBytes (k n : Nat) :
    (Builder.chunk (encodeBEBytes k n)).toList = encodeBEU k n := by
  rw [Builder.toList_chunk, encodeBEBytes, List.toList_data_toByteArray]

/-- Write a `uintM` word, big-endian.  A width-32 encoding truncates to
`2 ^ 256` by itself, so the value is encoded directly — no `UInt256.ofNat`
round trip (a bignum mod) per word.

Words below `2 ^ 64` take `word32Small`, which computes only the bytes that
can be non-zero.  That is not a special case for small values: the ABI writes
a word for every array length, every dynamic offset, every `bytes` length and
every `bool`, and all of those are far below `2 ^ 64`.

The two branches produce the *same* builder shape — one `chunk` leaf — on
purpose.  Writing the zeros as a `zeros` run instead (`Builder.zeros 24 ++
Builder.chunk …`) also encodes correctly and is faster on `bytes[]`, but it
adds an `append` node and a second `emit` step per word, which measured 1.37×
*slower* on `bool[]`, where the word is already the cheap part. -/
def putUint (n : Nat) : Builder :=
  if n < 2 ^ 64 then Builder.chunk (word32Small n) else Builder.chunk (encodeBEBytes 32 n)

@[simp] theorem toList_putUint (n : Nat) : (putUint n).toList = encodeUint n := by
  rw [encodeUint_eq, putUint]
  split
  · rename_i h
    rw [Builder.toList_chunk, data_toList_word32Small h]
  · rw [toList_chunk_encodeBEBytes]


/-- Write an `intM` word (two's complement). -/
def putInt (i : Int) : Builder :=
  putUint (if 0 ≤ i then i.toNat else 2 ^ 256 - (-i).toNat)

@[simp] theorem toList_putInt (i : Int) : (putInt i).toList = encodeInt i := by
  simp [putInt, encodeInt]


/-- Write a `bool` word. -/
def putBool (b : Bool) : Builder := putUint (if b then 1 else 0)

@[simp] theorem toList_putBool (b : Bool) : (putBool b).toList = encodeBool b := by
  simp [putBool, encodeBool]


/-- Write an `address` word. -/
def putAddress (a : Nat) : Builder := putUint a

@[simp] theorem toList_putAddress (a : Nat) : (putAddress a).toList = encodeAddress a := by
  simp [putAddress, encodeAddress]


/-- Write fixed-size bytes (`bytesN`): left-aligned, right zero-padded
to 32 bytes.  The padding is a `zeros` run, so it is never materialised. -/
def putBytesN (bs : List UInt8) : Builder :=
  let len := bs.length
  Builder.appendZeros (Builder.ofListLen bs len (by rfl)) (32 - len)

@[simp] theorem toList_putBytesN (bs : List UInt8) : (putBytesN bs).toList = encodeBytesN bs := by
  simp [putBytesN, encodeBytesN]


end EvmAbi
