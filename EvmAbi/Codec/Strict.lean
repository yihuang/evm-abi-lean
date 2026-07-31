import EvmAbi.Codec.Roundtrip
import EvmAbi.Codec.Sound

/-!
# EvmAbi.Codec.Strict

The strict API: `decodeStrict` (canonical layout plus exact consumption, no
trailing garbage), the predicate `IsCanonical`, and the capstones
`isCanonical_iff` / `decodeStrict_eq_some_iff` — canonical buffers are
exactly the image of `encode`, with no bound conjunct anywhere (the dynamic
payload bounds are intrinsic to `Ty.Val`).

Depends on both theorem families: `decode_roundtrip` (encode ⇒ decode) and
`decode_sound` (decode ⇒ encode).
-/

namespace EvmAbi

open Ty
open Binary
open Builder

/-! ## the strictness API -/

/-- Strict decoder: canonical layout and exact length, via the linear
canonical reader `decode`.  For call data (selector ++ arguments),
decode the argument tuple on `buf.drop 4` and compare against `buf.length - 4`. -/
def decodeStrict (t : Ty) (buf : List UInt8) : Option t.Val :=
  match decode t buf with
  | some (v, _, rest) => if rest = [] then some v else none
  | none => none

/-- A buffer is a canonical encoding of type `t`: the strict decoder
`decodeStrict` succeeds on it — the canonical-layout walk passes and
the buffer is consumed exactly (no trailing garbage). -/
def IsCanonical (t : Ty) (buf : List UInt8) : Prop :=
  (decodeStrict t buf).isSome = true

/-- Decidability of `IsCanonical` (instance search does not unfold the
def on its own). -/
instance (t : Ty) (buf : List UInt8) : Decidable (IsCanonical t buf) := by
  unfold IsCanonical
  infer_instance

/-! ## corollaries -/

/-- **Canonical roundtrip**: strict decode after encode. -/
theorem decodeStrict_encode (t : Ty) (hv : t.Valid) (v : t.Val)
    (hb : (encode t v).length < 2 ^ 256) :
    decodeStrict t (encode t v) = some v := by
  simp only [decodeStrict]
  have hr := decode_roundtrip t hv v [] (by rwa [List.append_nil])
  rw [show decode t (encode t v) = decode t (encode t v ++ []) from by simp]
  rw [hr]
  dsimp only []
  rfl

/-- The encoder's output is canonical. -/
theorem isCanonical_encode (t : Ty) (hv : t.Valid) (v : t.Val)
    (hb : (encode t v).length < 2 ^ 256) : IsCanonical t (encode t v) := by
  simp [IsCanonical, decodeStrict_encode t hv v hb]

/-- **Canonical uniqueness**: a strictly decodable buffer IS the encoding of
its decoded value.  (Injectivity of `encode` itself is a one-liner from
`roundtrip`; this is the stronger statement that every canonical-decodable
byte string lies in the image of `encode`.) -/
theorem encode_of_decodeStrict (t : Ty) (hv : t.Valid) (buf : List UInt8) (v : t.Val)
    (h : decodeStrict t buf = some v) : encode t v = buf := by
  simp only [decodeStrict] at h
  cases hg : decode t buf with
  | none => simp only [hg] at h; contradiction
  | some p =>
      obtain ⟨v', c, rest⟩ := p
      simp only [hg] at h
      by_cases hrest : rest = []
      · rw [if_pos hrest] at h
        have hv' : v' = v := Option.some.inj h
        subst hv'
        have hsnd := (decode_sound t hv v' buf rest c hg).1
        rw [hrest, List.append_nil] at hsnd
        exact hsnd
      · rw [if_neg hrest] at h; contradiction

/-- **Image characterization** (capstone): under the buffer bound, the
canonical buffers of a valid type are exactly the encodings of its values —
with no bound conjunct anywhere, since the bounds live in `Val` itself. -/
theorem isCanonical_iff (t : Ty) (hv : t.Valid) (buf : List UInt8)
    (hb : buf.length < 2 ^ 256) :
    IsCanonical t buf ↔ ∃ v, encode t v = buf := by
  constructor
  · intro h
    have hdec : ∃ v, decodeStrict t buf = some v := by
      cases hd : decodeStrict t buf with
      | none => simp [IsCanonical, hd] at h
      | some v => exact ⟨v, rfl⟩
    obtain ⟨v, hd⟩ := hdec
    exact ⟨v, encode_of_decodeStrict t hv buf v hd⟩
  · rintro ⟨v, he⟩
    show (decodeStrict t buf).isSome = true
    rw [← he]
    exact isCanonical_encode t hv v (by rw [he]; exact hb)

/-- **Strict-decoder characterization** (capstone): `decodeStrict`
succeeds on exactly the encodings — no side condition on the value at all,
since every `t.Val` carries its own bounds. -/
theorem decodeStrict_eq_some_iff (t : Ty) (hv : t.Valid) (buf : List UInt8)
    (v : t.Val) (hb : buf.length < 2 ^ 256) :
    decodeStrict t buf = some v ↔ encode t v = buf := by
  constructor
  · intro h
    exact encode_of_decodeStrict t hv buf v h
  · intro he
    rw [← he]
    exact decodeStrict_encode t hv v (by rw [he]; exact hb)


end EvmAbi
