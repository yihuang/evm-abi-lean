import Binary.UInt256
import EvmAbi.Word

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

/-- **Roundtrip for `uintM`**: the tighter bound `n < 2^M` suffices. -/
theorem decodeUint_encodeUint_of_lt {M : Nat} (hM : M ≤ 256) (h : n < 2 ^ M) :
    decodeUint (encodeUint n) = some n :=
  decodeUint_encodeUint (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (n := 2) (by decide) hM))

/-! ## intM -/

/-- Encode a signed integer as two's complement in a 32-byte word. -/
def encodeInt (i : Int) : List UInt8 :=
  encodeUint (if 0 ≤ i then i.toNat else 2 ^ 256 - (-i).toNat)

/-- Decode a word as a signed integer (two's complement). -/
def decodeInt (buf : List UInt8) : Option Int :=
  (decodeUint buf).map fun (n : Nat) =>
    if n < 2 ^ 255 then (n : Int) else (n : Int) - 2 ^ 256

/-- **Roundtrip for `intM`**: decode after encode is the identity in range. -/
theorem decodeInt_encodeInt {M : Nat} (hM0 : 0 < M) (hM : M ≤ 256)
    (hl : -(2 ^ (M - 1)) ≤ i) (hu : i < 2 ^ (M - 1)) :
    decodeInt (encodeInt i) = some i := by
  have hb : (2 : Int) ^ (M - 1) ≤ 2 ^ 255 := by
    have e : (2 : Int) ^ (M - 1) = ((2 ^ (M - 1) : Nat) : Int) :=
      (Int.natCast_pow 2 (M - 1)).symm
    have hle : (2 : Nat) ^ (M - 1) ≤ 2 ^ 255 :=
      Nat.pow_le_pow_right (n := 2) (by decide) (by omega)
    rw [e]; exact Int.ofNat_le.mpr hle
  have hub : i < (2 : Int) ^ 255 := by omega
  have hlb : -(2 : Int) ^ 255 ≤ i := by omega
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

/-- **Roundtrip** for `bool`. -/
theorem decodeBool_encodeBool (b : Bool) : decodeBool (encodeBool b) = some b := by
  cases b <;> native_decide

/-! ## address -/

/-- EVM `address`: a 160-bit value, encoded exactly like `uint160`
(right-aligned in the word). -/
def encodeAddress (a : Nat) : List UInt8 := encodeUint a

/-- Decode an address word. -/
def decodeAddress (buf : List UInt8) : Option Nat := decodeUint buf

/-- **Roundtrip** for `address`. -/
theorem decodeAddress_encodeAddress (h : a < 2 ^ 160) :
    decodeAddress (encodeAddress a) = some a :=
  decodeUint_encodeUint_of_lt (M := 160) (by decide) h

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

/-- **Roundtrip** for `bytesN` (prefix-tolerant decoder). -/
theorem decodeBytesN_encodeBytesN {n : Nat} (h32 : n ≤ 32) (h : bs.length = n) :
    decodeBytesN n (encodeBytesN bs) = some bs := by
  unfold decodeBytesN encodeBytesN
  have hlen : (bs ++ List.replicate (32 - bs.length) 0).length = 32 := by
    rw [List.length_append, List.length_replicate]; omega
  have htk : (bs ++ List.replicate (32 - bs.length) 0).take 32 =
      bs ++ List.replicate (32 - bs.length) 0 := List.take_of_length_le (by omega)
  rw [htk, take_append_of_length h, drop_append_of_length h, if_pos ⟨h, by rw [h]⟩]

end EvmAbi
