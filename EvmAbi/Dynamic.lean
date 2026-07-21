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

/-! ## string -/

/-- ABI `string`: `bytes` over the UTF-8 encoding. -/
def encodeString (s : String) : List UInt8 := encodeBytes s.toUTF8.data.toList

/-- UTF-8 decode/encode roundtrip — provable thanks to the byte-array-based
`String` representation (structure eta plus proof irrelevance). -/
theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  unfold String.fromUTF8?
  rw [String.toUTF8_eq_toByteArray, dif_pos s.isValidUTF8]
  rfl

/-- `fromUTF8?` inverse direction: a successfully decoded string re-encodes
to the same bytes. -/
theorem toUTF8_of_fromUTF8? {b : ByteArray} {s : String} (h : String.fromUTF8? b = some s) :
    s.toUTF8 = b := by
  unfold String.fromUTF8? at h
  split at h
  · next hv =>
    rw [Option.some.injEq] at h
    subst h
    rfl
  · contradiction

/-- `ByteArray`/`List UInt8` roundtrip needed by the string layer. -/
theorem dataToList_toByteArray (ba : ByteArray) : ba.data.toList.toByteArray = ba := by
  apply ByteArray.data_inj
  rw [List.data_toByteArray, Array.toArray_toList]

/-! ## prefix decoding (for composition inside tuples) -/

/-- Prefix decoder for dynamic `bytes`: reads a length word, exactly `len`
data bytes and the zero padding, returning the bytes and the number of
consumed bytes. Anything beyond the consumed prefix is ignored, so this
composes with the head/tail layout (`EvmAbi.Parts`). -/
def decodeBytesPrefix (buf : List UInt8) : Option (List UInt8 × Nat) :=
  (natAt buf 0).bind fun len =>
    if ((buf.drop 32).take len).length = len ∧
       ((buf.drop 32).drop len).take ((32 - len % 32) % 32) =
         List.replicate ((32 - len % 32) % 32) 0 then
      some ((buf.drop 32).take len, 32 + len + (32 - len % 32) % 32)
    else none

/-- **Prefix roundtrip**: an encoded `bytes` value is read back from the
front of a larger buffer, with the exact consumed length reported. -/
theorem decodeBytesPrefix_append (h : bs.length < 2 ^ 256) :
    decodeBytesPrefix (encodeBytes bs ++ rest) = some (bs, (encodeBytes bs).length) := by
  have hw := natAt_append ([] : List UInt8) (pad32 bs ++ rest) (UInt256.ofNat bs.length) 0
    (by simp)
  simp only [List.nil_append] at hw
  have hlen : (UInt256.ofNat bs.length).toNat = bs.length := by
    rw [UInt256.toNat_ofNat]; exact Nat.mod_eq_of_lt h
  rw [hlen] at hw
  have hdata : ((pad32 bs ++ rest).take bs.length) = bs := by
    rw [pad32, List.append_assoc]; exact take_append_of_length rfl
  have hpad : ((pad32 bs ++ rest).drop bs.length).take ((32 - bs.length % 32) % 32) =
      List.replicate ((32 - bs.length % 32) % 32) 0 := by
    rw [pad32, List.append_assoc, drop_append_of_length rfl]
    exact take_append_of_length (by simp)
  unfold decodeBytesPrefix encodeBytes encodeUint
  rw [List.append_assoc, hw, Option.bind_some, drop_append_of_length (length_bytesOfWord _),
    hdata, hpad, if_pos ⟨rfl, rfl⟩]
  congr 1
  simp [length_pad32, length_bytesOfWord] <;> omega

/-- A prefix-decoded `bytes` payload is bounded by its own length word —
what lets `decode` return refined values whose bound is intrinsic. -/
theorem length_lt_of_decodeBytesPrefix {buf bs : List UInt8} {n : Nat}
    (h : decodeBytesPrefix buf = some (bs, n)) : bs.length < 2 ^ 256 := by
  simp only [decodeBytesPrefix] at h
  cases hlen : natAt buf 0 with
  | none => simp only [hlen, Option.bind_none] at h; contradiction
  | some len =>
      simp only [hlen, Option.bind_some] at h
      by_cases hc : ((buf.drop 32).take len).length = len ∧
          ((buf.drop 32).drop len).take ((32 - len % 32) % 32) =
            List.replicate ((32 - len % 32) % 32) 0
      · rw [if_pos hc] at h
        have hbs : (buf.drop 32).take len = bs := congrArg Prod.fst (Option.some.inj h)
        rw [← hbs, hc.1]
        exact natAt_lt hlen
      · rw [if_neg hc] at h; contradiction

/-- The bound of a prefix-decoded `string` payload, transported through the
UTF-8 roundtrip onto the decoded string. -/
theorem size_toUTF8_lt_of_decodeBytesPrefix {buf bs : List UInt8} {n : Nat} {s : String}
    (hp : decodeBytesPrefix buf = some (bs, n))
    (hs : String.fromUTF8? bs.toByteArray = some s) : s.toUTF8.size < 2 ^ 256 := by
  rw [Binary.ByteArray.size_eq_toList_length, toUTF8_of_fromUTF8? hs]
  simpa [List.data_toByteArray] using length_lt_of_decodeBytesPrefix hp

end EvmAbi
