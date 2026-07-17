import EvmAbi.Static
import EvmAbi.Bytes
import Binary.ByteArray

/-!
# EvmAbi.Dynamic

Dynamic `bytes` and `string` (roadmap node 5):

```
enc(X)  for  bytes X  =  enc(len(X)) ++ pad32(X)
```

i.e. the length word followed by the data right-padded with zeros to a
multiple of 32 bytes. `string` is `bytes` over the UTF-8 encoding.

The roundtrips proved here are the touchstone of the ABI project: they
exercise the word layer (`natAt_append`), the padding lemmas
(`take_length_pad32`, `drop_length_pad32`) and the take/drop algebra
(`drop_append_of_length`) together.
-/

namespace EvmAbi

open Binary

/-! ## bytes -/

/-- ABI encoding of dynamic `bytes`: the length word, then zero-padded data. -/
def encodeBytes (bs : List UInt8) : List UInt8 := encodeUint bs.length ++ pad32 bs

theorem length_encodeBytes (bs : List UInt8) :
    (encodeBytes bs).length = 32 + (pad32 bs).length := by
  simp [encodeBytes]

theorem dvd_length_encodeBytes (bs : List UInt8) : 32 ∣ (encodeBytes bs).length := by
  have hp := dvd_length_pad32 bs
  rw [length_encodeBytes]; omega

/-- Strict decoder: a length word, exactly `len` data bytes, then zero padding. -/
def decodeBytes (buf : List UInt8) : Option (List UInt8) :=
  (natAt buf 0).bind fun len =>
    if ((buf.drop 32).take len).length = len ∧
       (buf.drop 32).drop len = List.replicate ((32 - len % 32) % 32) 0 then
      some ((buf.drop 32).take len)
    else none

/-- **Roundtrip** — the dynamic-bytes touchstone. -/
theorem decodeBytes_encodeBytes (h : bs.length < 2 ^ 256) :
    decodeBytes (encodeBytes bs) = some bs := by
  have hw := natAt_append ([] : List UInt8) (pad32 bs) (UInt256.ofNat bs.length) 0 (by simp)
  simp only [List.nil_append] at hw
  have hlen : (UInt256.ofNat bs.length).toNat = bs.length := by
    rw [UInt256.toNat_ofNat]; exact Nat.mod_eq_of_lt h
  rw [hlen] at hw
  unfold decodeBytes encodeBytes encodeUint
  rw [hw, Option.bind_some, drop_append_of_length (length_bytesOfWord _),
    take_length_pad32, drop_length_pad32, if_pos ⟨rfl, rfl⟩]

/-! ## string -/

/-- ABI `string`: `bytes` over the UTF-8 encoding. -/
def encodeString (s : String) : List UInt8 := encodeBytes s.toUTF8.data.toList

/-- Decode a `string`, validating the UTF-8 encoding. -/
def decodeString (buf : List UInt8) : Option String :=
  (decodeBytes buf).bind fun bs => String.fromUTF8? bs.toByteArray

/-- UTF-8 decode/encode roundtrip — provable thanks to the byte-array-based
`String` representation (structure eta plus proof irrelevance). -/
theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  unfold String.fromUTF8?
  rw [String.toUTF8_eq_toByteArray, dif_pos s.isValidUTF8]
  rfl

/-- `ByteArray`/`List UInt8` roundtrip needed by the string layer. -/
theorem dataToList_toByteArray (ba : ByteArray) : ba.data.toList.toByteArray = ba := by
  apply ByteArray.data_inj
  rw [List.data_toByteArray, Array.toArray_toList]

/-- **Roundtrip** for `string`. -/
theorem decodeString_encodeString (h : s.toUTF8.data.toList.length < 2 ^ 256) :
    decodeString (encodeString s) = some s := by
  unfold decodeString encodeString
  rw [decodeBytes_encodeBytes h, Option.bind_some, dataToList_toByteArray, fromUTF8?_toUTF8]

end EvmAbi
