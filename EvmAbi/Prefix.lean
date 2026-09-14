import EvmAbi.Bytes

/-!
# EvmAbi.Prefix

Every primitive decoder in the codec reads its value out of a fixed-size
*prefix* of the buffer and ignores whatever follows: the word types take
the first 32 bytes, a packed scalar takes its own width, `bytesN n` takes
the word at the front.  That is the whole reason the families
`decodeUint_append`, `decodeInt_append`, … (standard) and
`decodeUintPacked_append`, … (packed) hold — "read back the value from the
front of an encoding followed by an arbitrary suffix" is one fact, and
each atom used to prove it again by hand over the word layer.

`PrefixCodec` records the fact once per atom: `dec_take` is the locality
(`dec` agrees with itself on `buf.take size`), `enc_length` the width of
the encoder, `dec_enc` the plain roundtrip.  `roundtrip_append` below is
then free for every atom, and the only per-atom work left is those three
obligations.

`P` carries the atom's well-formedness condition (`uintM` fits its word,
an `address` is 20 bytes, …).  The primitive decoders are total and their
roundtrips only hold on well-formed inputs, so the condition belongs to
the codec rather than to a refined value type — which also keeps the
read-back lemmas stated on the raw values (`decodeUint (encodeUint n ++
rest) = some n`, not on a subtype).

This is a `structure` rather than a `class` on purpose: `address`,
`bytesN n` and their packed mirrors all have the value type
`List UInt8`, so the instances would collide and instance search would
have nothing to resolve on.  The codecs are named and passed explicitly.
-/

namespace EvmAbi

/-- A primitive codec whose decoder reads a value from a fixed-size prefix
of its buffer.  `P` is the codec's well-formedness condition on values. -/
structure PrefixCodec (α : Type) where
  /-- The width of the encoded prefix. -/
  size : Nat
  /-- Well-formedness of a value — the domain the roundtrip holds on. -/
  P : α → Prop
  /-- Write a value; for `a` with `P a` this is exactly `size` bytes. -/
  enc : α → List UInt8
  /-- Read a value from the front of a buffer. -/
  dec : List UInt8 → Option α
  /-- The decoder reads no more than the first `size` bytes. -/
  dec_take : ∀ buf, dec buf = dec (buf.take size)
  /-- Well-formed values encode to the codec's width. -/
  enc_length : ∀ a, P a → (enc a).length = size
  /-- Plain roundtrip: an encoding decodes back. -/
  dec_enc : ∀ a, P a → dec (enc a) = some a

/-- **Suffix tolerance**: decoding an encoding followed by anything at all
recovers the value and leaves the suffix unread.  This is the single fact
behind every `_append` read-back of the codec. -/
theorem PrefixCodec.roundtrip_append (c : PrefixCodec α) (a : α) (ha : c.P a)
    (rest : List UInt8) :
    c.dec (c.enc a ++ rest) = some a := by
  rw [c.dec_take, take_append_of_length (c.enc_length a ha), c.dec_enc a ha]

end EvmAbi
