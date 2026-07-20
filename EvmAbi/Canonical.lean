import EvmAbi.Codec

/-!
# EvmAbi.Canonical

Canonical-layout validation (roadmap node 8, strictness half): the lenient
`decode` of `EvmAbi.Codec` accepts any offset that happens to land on a
decodable tail.  This module adds the missing check — dynamic components'
offset words must point to tails laid out *contiguously, in order,
immediately after the head section* — and the theorems that give the check
meaning.

The central definition is `validate : (t : Ty) → List UInt8 → Option Nat`,
an executable checker returning the number of bytes consumed by a canonical
encoding at the front of the buffer.  It walks head sections exactly like
`decodeElems`/`decodeTuple`, but threads an *expected tail frontier*: a
dynamic component's offset word must equal the frontier exactly, and the
frontier advances by the component's consumed tail size.  Returning the
consumed length is what makes the check composable (nested components are
prefixes of their parent's buffer); the top-level predicate `IsCanonical`
additionally requires exact consumption (no trailing garbage), and
`decodeCanonical` is the strict decoder built on top.

Theorems (packages C1–C3):

* **C1 completeness** — `validate_encode_append` family: every encoding
  validates, consuming exactly its length.  The checker is not too strict.
* **C2 lenient completeness on canonical input** — `validate_decode`
  family: whatever validates also lenient-decodes.
* **C3 soundness** — `encode_eq_take_of_validate` family: a buffer that
  validates and decodes to `v` has `encode t v` as its consumed prefix.
  The checker is not too lenient: canonical buffers are exactly the image
  of `encode`.

Corollaries: `decodeCanonical_encode` (strict roundtrip) and
`encode_of_decodeCanonical` (canonical uniqueness: a strictly decodable
buffer *is* the encoding of its decoded value).
-/

namespace EvmAbi

open Ty
open Binary

/-! ## helper lemmas -/

/-- The head section of an element list mapped through `partOf`, for
arbitrary (not only static) element types. -/
theorem headSizes_map_partOf_any (t : Ty) (hv : t.Valid) :
    (vs : List t.Val) → headSizes (vs.map (partOf t)) = vs.length * t.headSize
  | [] => by simp [headSizes]
  | v :: vs => by
      rw [List.map_cons]
      have ih := headSizes_map_partOf_any t hv vs
      by_cases hs : t.IsStatic
      · rw [partOf_static t v hs]
        simp only [headSizes, Part.headSize, List.length_cons]
        rw [encode_length_static t hs hv v, ih, Nat.add_mul, Nat.one_mul]
        omega
      · have hsf : t.IsStatic = false := by simp at hs; exact hs
        rw [partOf_dynamic t v hsf]
        simp only [headSizes, Part.headSize, List.length_cons]
        rw [ih, headSize_of_dynamic t hsf]
        omega

/-- The head section of a tuple part list, for arbitrary component types. -/
theorem headSizes_partsOfTuple_any : (ts : List Ty) → AllValid ts → (vs : TupleVal ts) →
    headSizes (partsOfTuple ts vs) = headSizeSum ts
  | [], _, _ => by simp [partsOfTuple, headSizes, headSizeSum]
  | t :: ts, hv, (v, vs) => by
      obtain ⟨hvt, hvs⟩ := hv
      simp only [partsOfTuple]
      have ih := headSizes_partsOfTuple_any ts hvs vs
      by_cases hs : t.IsStatic
      · rw [partOf_static t v hs]
        simp only [headSizes, Part.headSize, headSizeSum]
        rw [encode_length_static t hs hvt v, ih]
      · have hsf : t.IsStatic = false := by simp at hs; exact hs
        rw [partOf_dynamic t v hsf]
        simp only [headSizes, Part.headSize, headSizeSum]
        rw [ih, headSize_of_dynamic t hsf]

/-- A tuple part list has one part per component type. -/
theorem length_partsOfTuple : (ts : List Ty) → (vs : TupleVal ts) →
    (partsOfTuple ts vs).length = ts.length
  | [], _ => by simp [partsOfTuple]
  | t :: ts, (v, vs) => by
      simp only [partsOfTuple, List.length_cons, List.length_cons]
      rw [length_partsOfTuple ts vs]

/-- A successful word read determines the word's bytes: the 32 bytes at the
read position are the big-endian encoding of the value read. -/
theorem take_32_eq_encodeUint_of_natAt (buf : List UInt8) (i : Nat) (n : Nat)
    (h : natAt buf i = some n) : (buf.drop (32 * i)).take 32 = encodeUint n := by
  unfold natAt wordAt at h
  split at h
  · next hl =>
    rw [Option.map_some, Option.some.injEq] at h
    subst h
    show _ = UInt256.toBEBytes (UInt256.ofNat (UInt256.ofBEBytes _).toNat)
    rw [UInt256.ofNat_toNat, UInt256.toBEBytes_ofBEBytes hl]
  · contradiction

/-- The tail offset advances by exactly one part's tail. -/
theorem tailOffset_succ (ps : List Part) (xs : List Part) (p : Part) (ys : List Part)
    (h : ps = xs ++ p :: ys) :
    tailOffset ps (xs.length + 1) = tailOffset ps xs.length + p.tailSize := by
  subst h
  rw [tailOffset, tailOffset, take_append_of_length rfl]
  have htake : (xs ++ p :: ys).take (xs.length + 1) = xs ++ [p] := by
    simp [List.take_append, List.take_of_length_le (Nat.le_succ _)]
  rw [htake, tailSizes_append]
  simp [tailSizes]
  omega

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

/-- `encodeInt` of a two's-complement-decoded word is the word itself. -/
theorem encodeInt_eq_encodeUint_of_decodeInt (x : Nat) (hx : x < 2 ^ 256) (i : Int)
    (h : (if x < 2 ^ 255 then (x : Int) else (x : Int) - 2 ^ 256) = i) :
    encodeInt i = encodeUint x := by
  by_cases hx2 : x < 2 ^ 255
  · rw [if_pos hx2] at h
    subst h
    rw [encodeInt, if_pos (by omega)]
    congr 1
  · rw [if_neg hx2] at h
    subst h
    rw [encodeInt, if_neg (by omega)]
    congr 1
    omega

/-! ## the validate family -/

/- Canonical-layout validation.  `validate` checks that the front of the
buffer is a canonical encoding of *some* value of the type, returning the
number of bytes consumed.  The walkers step through a head section exactly
like `decodeElems`/`decodeTuple`, but additionally thread the *expected
tail frontier*: a dynamic component's offset word must contain precisely
the frontier position, i.e. tails must be laid out contiguously, in order,
immediately after the head section.  Static components need no frontier
update (they sit inline in the head); their validators reuse the strict
primitive decoders, which already reject non-canonical words. -/
mutual
/-- Canonical-layout validator (type-indexed, prefix form): the front of
`buf` is checked to be a canonical encoding of some value of type `t`;
on success the number of bytes consumed is returned. -/
def validate : (t : Ty) → List UInt8 → Option Nat
  | .uint m, buf => match decodeUint buf with
    | some n => if n < 2 ^ m then some 32 else none
    | none => none
  | .int m, buf => match decodeInt buf with
    | some i => if -((2 ^ (m - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m - 1) : Nat) : Int) then
        some 32
      else none
    | none => none
  | .bool, buf => match decodeBool buf with
    | some _ => some 32
    | none => none
  | .address, buf => match decodeAddress buf with
    | some n => if n < 2 ^ 160 then some 32 else none
    | none => none
  | .bytesN m, buf => match decodeBytesN m buf with
    | some bs => if bs.length = m then some 32 else none
    | none => none
  | .bytes, buf => (decodeBytesPrefix buf).map Prod.snd
  | .string, buf => match decodeBytesPrefix buf with
    | some (bs, n) => match String.fromUTF8? bs.toByteArray with
      | some _ => some n
      | none => none
    | none => none
  | .array t, buf => match natAt buf 0 with
    | none => none
    | some k => (validateElems t k (buf.drop 32) 0 (k * t.headSize)).map (32 + ·)
  | .fixedArray t n, buf => validateElems t n buf 0 (n * t.headSize)
  | .tuple ts, buf => validateTuple ts buf 0 (headSizeSum ts)
termination_by t => (sizeOf t, 0)

/-- Validate one component at head offset `off`.  A dynamic component's
offset word must equal `expectedTail` exactly — the canonical-layout check.
Returns the advanced tail frontier. -/
def validateElem (t : Ty) (buf : List UInt8) (off expectedTail : Nat) : Option Nat :=
  match t.IsStatic with
  | true => match validate t (buf.drop off) with
    | some _ => some expectedTail
    | none => none
  | false => match natAt buf (off / 32) with
    | none => none
    | some o => if o = expectedTail then
        match validate t (buf.drop o) with
        | some n => some (o + n)
        | none => none
      else none
termination_by (sizeOf t, 1)

/-- Validate `k` consecutive elements of type `t`, walking the head from
`off` and the tail frontier from `expectedTail`. -/
def validateElems (t : Ty) (k : Nat) (buf : List UInt8) (off expectedTail : Nat) :
    Option Nat :=
  match k with
  | 0 => some expectedTail
  | k + 1 => match validateElem t buf off expectedTail with
    | none => none
    | some E => validateElems t k buf (off + t.headSize) E
termination_by (sizeOf t, k + 2)

/-- Validate a tuple, walking the head from `off` and the tail frontier
from `expectedTail`. -/
def validateTuple : (ts : List Ty) → List UInt8 → Nat → Nat → Option Nat
  | [], _, _, expectedTail => some expectedTail
  | t :: ts, buf, off, expectedTail => match validateElem t buf off expectedTail with
    | none => none
    | some E => validateTuple ts buf (off + t.headSize) E
termination_by ts => (sizeOf ts, 2)
end

/-- `validateElem` of a static type validates in place and keeps the
frontier. -/
theorem validateElem_static (t : Ty) (buf : List UInt8) (off E : Nat) (h : t.IsStatic = true) :
    validateElem t buf off E = (match validate t (buf.drop off) with
      | some _ => some E
      | none => none) := by
  simp [validateElem, h]

/-- `validateElem` of a dynamic type checks the offset word against the
frontier. -/
theorem validateElem_dynamic (t : Ty) (buf : List UInt8) (off E : Nat) (h : t.IsStatic = false) :
    validateElem t buf off E = (match natAt buf (off / 32) with
      | none => none
      | some o => if o = E then
          match validate t (buf.drop o) with
          | some n => some (o + n)
          | none => none
        else none) := by
  simp [validateElem, h]

/-! ## the strictness API -/

/-- A buffer is a canonical encoding of type `t`: it validates and is
consumed exactly (no trailing garbage). -/
def IsCanonical (t : Ty) (buf : List UInt8) : Prop := validate t buf = some buf.length

/-- Strict decoder: canonical layout and exact length, then the lenient
decoder.  For call data (selector ++ arguments), validate the argument
tuple on `buf.drop 4` and compare against `buf.length - 4`. -/
def decodeCanonical (t : Ty) (buf : List UInt8) : Option t.Val :=
  match validate t buf with
  | some n => if n = buf.length then decode t buf else none
  | none => none

/-! ## static validators keep the frontier and consume exactly `headSize` -/

/-- A static component never advances the tail frontier. -/
theorem validateElem_static_E (t : Ty) (hs : t.IsStatic = true) (buf : List UInt8)
    (off E E' : Nat) (h : validateElem t buf off E = some E') : E' = E := by
  rw [validateElem_static t _ _ _ hs] at h
  cases hv : validate t (buf.drop off) with
  | none => simp only [hv] at h; contradiction
  | some _ =>
      simp only [hv] at h
      exact (Option.some.inj h).symm

/-- A run of static elements never advances the tail frontier. -/
theorem validateElems_static_E (t : Ty) (hs : t.IsStatic = true) (k : Nat)
    (buf : List UInt8) (off E E' : Nat)
    (h : validateElems t k buf off E = some E') : E' = E := by
  induction k generalizing off E with
  | zero =>
      simp only [validateElems] at h
      exact (Option.some.inj h).symm
  | succ k ih =>
      simp only [validateElems] at h
      cases he : validateElem t buf off E with
      | none => simp only [he] at h; contradiction
      | some E₁ =>
          simp only [he] at h
          have hE₁ : E₁ = E := validateElem_static_E t hs buf off E E₁ he
          subst hE₁
          exact ih _ _ h

/-- A run of static tuple components never advances the tail frontier. -/
theorem validateTuple_static_E : (ts : List Ty) → allStatic ts = true →
    (buf : List UInt8) → (off E E' : Nat) →
    validateTuple ts buf off E = some E' → E' = E
  | [], _, _, _, _, _, h => by
      simp only [validateTuple] at h
      exact (Option.some.inj h).symm
  | t :: ts, hall, buf, off, E, E', h => by
      simp only [allStatic] at hall
      rw [Bool.and_eq_true] at hall
      obtain ⟨hst, hss⟩ := hall
      simp only [validateTuple] at h
      cases he : validateElem t buf off E with
      | none => simp only [he] at h; contradiction
      | some E₁ =>
          simp only [he] at h
          have hE₁ : E₁ = E := validateElem_static_E t hst buf off E E₁ he
          subst hE₁
          exact validateTuple_static_E ts hss buf (off + t.headSize) E₁ E' h

/-- A static type's validator consumes exactly its head size. -/
theorem validate_static_len (t : Ty) (hs : t.IsStatic = true) (buf : List UInt8) (n : Nat)
    (h : validate t buf = some n) : n = t.headSize := by
  cases t with
  | uint m =>
      simp [headSize] at *
      simp [validate] at h
      cases hdu : decodeUint buf with
      | none => simp [hdu] at h
      | some x => simp [hdu] at h; simp [h]
  | int m =>
      simp [headSize] at *
      simp [validate] at h
      cases hdi : decodeInt buf with
      | none => simp [hdi] at h
      | some i => simp [hdi] at h; omega
  | bool =>
      simp [headSize] at *
      simp [validate] at h
      split at h <;> simp at h <;> omega
  | address =>
      simp [headSize] at *
      simp [validate] at h
      cases hda : decodeAddress buf with
      | none => simp [hda] at h
      | some x => simp [hda] at h; omega
  | bytesN m =>
      simp [headSize] at *
      simp [validate] at h
      cases hdb : decodeBytesN m buf with
      | none => simp [hdb] at h
      | some bs => simp [hdb] at h; omega
  | bytes => simp [IsStatic] at hs
  | string => simp [IsStatic] at hs
  | array t => simp [IsStatic] at hs
  | fixedArray t n' =>
      have hst : t.IsStatic = true := by simpa [IsStatic] using hs
      simp only [validate] at h
      have : n = n' * t.headSize := validateElems_static_E t hst n' buf 0 _ n h
      rw [this]
      simp [headSize, if_pos hst]
  | tuple ts =>
      have hss : allStatic ts = true := by simpa [IsStatic] using hs
      simp only [validate] at h
      have : n = headSizeSum ts := validateTuple_static_E ts hss buf 0 _ n h
      rw [this]
      simp [headSize, if_pos hss]

/-- The tail size of a static component's part is zero. -/
theorem tailSize_partOf_static (t : Ty) (v : t.Val) (h : t.IsStatic = true) :
    (partOf t v).tailSize = 0 := by
  rw [partOf_static t v h]
  rfl

/-- The tail size of a dynamic component's part is its encoding length. -/
theorem tailSize_partOf_dynamic (t : Ty) (v : t.Val) (h : t.IsStatic = false) :
    (partOf t v).tailSize = (encode t v).length := by
  rw [partOf_dynamic t v h]
  rfl

/-! ## Package C1: canonical completeness -/

/- Every encoding validates, consuming exactly its own length — the checker
accepts everything the encoder produces.  The walker lemmas thread the
frontier invariant `E = tailOffset ps xs.length` (the tail offset of the
current part) and advance it exactly along the tails, mirroring Package D
of `EvmAbi.Codec`. -/

mutual
/-- **Canonical completeness, prefix form**: the encoding of every value
validates, consuming exactly the encoding's length.  `hb` bounds the whole
buffer (so no offset word wraps); `hl` bounds the dynamic payloads (so no
length word wraps). -/
theorem validate_encode_append (t : Ty) (hv : t.Valid) (v : t.Val) (hl : LenBound t v)
    (rest : List UInt8) (hb : (encode t v ++ rest).length < 2 ^ 256) :
    validate t (encode t v ++ rest) = some (encode t v).length := by
  cases t with
  | uint m =>
      obtain ⟨n, hn⟩ := v
      have hdec : decodeUint (encodeUint n ++ rest) = some n :=
        decodeUint_append n rest
          (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (n := 2) (by decide) hv.2.1))
      simp only [validate, encode, hdec, if_pos hn, length_encodeUint]
  | int m =>
      obtain ⟨i, hi⟩ := v
      have h0 : 0 < m := by have h8 := hv.1; omega
      have hdec : decodeInt (encodeInt i ++ rest) = some i :=
        decodeInt_append h0 hv.2.1 hi.1 hi.2 rest
      simp only [validate, encode, hdec, if_pos hi]
      simp [encodeInt, length_encodeUint]
  | bool =>
      have hdec := decodeBool_append v rest
      simp only [validate, encode, hdec]
      simp [encodeBool, length_encodeUint]
  | address =>
      obtain ⟨n, hn⟩ := v
      have hdec : decodeAddress (encodeAddress n ++ rest) = some n :=
        decodeAddress_append n rest hn
      simp only [validate, encode, hdec, if_pos hn]
      simp [encodeAddress, length_encodeUint]
  | bytesN m =>
      obtain ⟨bs, hbs⟩ := v
      have hdec : decodeBytesN m (encodeBytesN bs ++ rest) = some bs :=
        decodeBytesN_append hv.2 hbs rest
      simp only [validate, encode, hdec, if_pos hbs]
      rw [length_encodeBytesN (by rw [hbs]; exact hv.2)]
  | bytes =>
      have hlb : v.length < 2 ^ 256 := by simpa [LenBound] using hl
      have hr := decodeBytesPrefix_append (bs := v) (rest := rest) hlb
      simp only [validate, encode, hr, Option.map_some]
  | string =>
      have hlb : v.toUTF8.size < 2 ^ 256 := by simpa [LenBound] using hl
      have hb2 : v.toUTF8.data.toList.length < 2 ^ 256 := by
        rw [← Binary.ByteArray.size_eq_toList_length v.toUTF8]
        exact hlb
      have hr := decodeBytesPrefix_append (bs := v.toUTF8.data.toList) (rest := rest) hb2
      simp only [validate, encode, encodeString, hr, dataToList_toByteArray,
        fromUTF8?_toUTF8]
  | array t =>
      have hla : v.length < 2 ^ 256 ∧ AllLenBound t v := by simpa [LenBound] using hl
      obtain ⟨hlk, hls⟩ := hla
      have hvt : t.Valid := hv
      have hbT : (encodeParts (v.map (partOf t)) ++ rest).length < 2 ^ 256 := by
        have hb' := hb
        simp only [encode, List.length_append, length_encodeUint] at hb'
        rw [List.length_append]
        omega
      have hwalk := validateElems_encode_append t hvt v v.length rfl hls [] []
        0 (by simp [headSizes]) (v.length * t.headSize) (by
          simp only [List.nil_append, List.append_nil, List.length_nil]
          rw [tailOffset, List.take_zero, tailSizes, Nat.add_zero,
            headSizes_map_partOf_any t hvt v])
        rest (by simpa using wf_map_partOf t hvt v) (by simpa using hbT)
      simp only [List.nil_append, List.append_nil] at hwalk
      have hcnt : natAt (encodeUint v.length ++ (encodeParts (v.map (partOf t)) ++ rest)) 0 =
          some v.length := by
        unfold encodeUint
        have hw := natAt_append ([] : List UInt8) (encodeParts (v.map (partOf t)) ++ rest)
          (UInt256.ofNat v.length) 0 (by simp)
        rw [List.nil_append] at hw
        rw [hw, UInt256.toNat_ofNat, Nat.mod_eq_of_lt
          (show v.length < UInt256.size from hlk)]
      have hdrop : (encodeUint v.length ++ (encodeParts (v.map (partOf t)) ++ rest)).drop 32 =
          encodeParts (v.map (partOf t)) ++ rest :=
        drop_append_of_length (length_encodeUint _)
      simp only [validate, encode, List.append_assoc, hcnt, hdrop, hwalk, Option.map_some]
      rw [List.length_append, length_encodeUint, length_encodeParts,
        headSizes_map_partOf_any t hvt v]
  | fixedArray t n =>
      obtain ⟨vs, hvs⟩ := v
      have hvt : t.Valid := hv
      have hls : AllLenBound t vs := by simpa [LenBound] using hl
      have hwalk := validateElems_encode_append t hvt vs n hvs hls [] [] 0 (by simp [headSizes])
        (n * t.headSize) (by
          simp only [List.nil_append, List.append_nil, List.length_nil]
          rw [tailOffset, List.take_zero, tailSizes, Nat.add_zero, ← hvs,
            headSizes_map_partOf_any t hvt vs])
        rest (by simpa using wf_map_partOf t hvt vs) (by simpa [encode] using hb)
      simp only [List.nil_append, List.append_nil] at hwalk
      simp only [validate, encode, hwalk]
      rw [length_encodeParts, ← hvs, headSizes_map_partOf_any t hvt vs]
  | tuple ts =>
      have hvts : AllValid ts := hv
      have hls : TupleLenBounds ts v := by simpa [LenBound] using hl
      have hwalk := validateTuple_encode_append ts hvts v hls [] [] 0 (by simp [headSizes])
        (headSizeSum ts) (by
          simp only [List.nil_append, List.append_nil, List.length_nil]
          rw [tailOffset, List.take_zero, tailSizes, Nat.add_zero,
            headSizes_partsOfTuple_any ts hvts v])
        rest (by simpa using wf_partsOfTuple ts hvts v) (by simpa [encode] using hb)
      simp only [List.nil_append, List.append_nil] at hwalk
      simp only [validate, encode, hwalk]
      rw [length_encodeParts, headSizes_partsOfTuple_any ts hvts v]
termination_by 8 * sizeOf t

/-- Element lists validate from their own encoding inside a larger
head/tail layout, the frontier advancing exactly along the tails. -/
theorem validateElems_encode_append (t : Ty) (hv : t.Valid) (vs : List t.Val) (k : Nat)
    (hk : vs.length = k) (hls : AllLenBound t vs)
    (xs ys : List Part) (off : Nat) (hoff : off = headSizes xs)
    (E : Nat) (hE : E = tailOffset (xs ++ vs.map (partOf t) ++ ys) xs.length)
    (rest : List UInt8)
    (hwf : WF (xs ++ vs.map (partOf t) ++ ys))
    (hb : (encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest).length < 2 ^ 256) :
    validateElems t k (encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest) off E =
      some (E + tailSizes (vs.map (partOf t))) := by
  induction vs generalizing k xs off E with
  | nil =>
      subst hk
      simp only [List.map_nil, List.length_nil, validateElems, tailSizes, Nat.add_zero]
  | cons w ws ih =>
      have hk' : k = ws.length + 1 := by rw [← hk, List.length_cons]
      subst hk'
      have hlc : LenBound t w ∧ AllLenBound t ws := by simpa [AllLenBound] using hls
      obtain ⟨hlw, hlsw⟩ := hlc
      simp only [List.map_cons, validateElems]
      simp only [List.map_cons] at hwf hb hE
      simp only [List.append_assoc, List.cons_append] at hwf hb hE ⊢
      have hre : xs ++ (partOf t w :: (ws.map (partOf t) ++ ys)) =
          ((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys := by
        simp [List.append_assoc]
      have hwf' : WF (((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys) := by rwa [← hre]
      have hb' : (encodeParts (((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys) ++ rest).length <
          2 ^ 256 := by rwa [← hre]
      by_cases hs : t.IsStatic
      · rw [validateElem_static t _ _ _ hs]
        rw [drop_head_partOf_static t hs w xs (ws.map (partOf t) ++ ys) rest off hoff]
        rw [validate_encode_append t hv w hlw _
          (by
            have heq := drop_head_partOf_static t hs w xs (ws.map (partOf t) ++ ys) rest off hoff
            rw [← heq, List.length_drop]
            omega)]
        dsimp only
        have hoff' : off + t.headSize = headSizes (xs ++ [partOf t w]) := by
          rw [hoff, headSizes_append]
          simp only [headSizes, partOf_static t w hs, Part.headSize]
          rw [encode_length_static t hs hv w]
          omega
        have hE' : E = tailOffset (((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys)
            (xs ++ [partOf t w]).length := by
          have hll : (xs ++ [partOf t w]).length = xs.length + 1 := by simp [List.length_append]
          rw [hll, tailOffset_succ _ _ _ _ hre.symm, tailSize_partOf_static t w hs,
            Nat.add_zero, ← hre]
          exact hE
        rw [hre] at hE ⊢
        rw [ih (ws.length) rfl hlsw (xs ++ [partOf t w]) (off + t.headSize) hoff' E hE' hwf' hb']
        simp only [tailSizes, tailSize_partOf_static t w hs, Nat.zero_add]
      · have hsf : t.IsStatic = false := by simp at hs; exact hs
        rw [validateElem_dynamic t _ _ _ hsf]
        rw [show off / 32 = headSizes xs / 32 by rw [hoff]]
        rw [natAt_offset_partOf_dynamic t w hsf xs (ws.map (partOf t) ++ ys) rest hwf hb]
        dsimp only
        rw [if_pos hE.symm]
        rw [drop_tail_partOf_dynamic t w hsf xs (ws.map (partOf t) ++ ys) rest]
        rw [validate_encode_append t hv w hlw _
          (by
            have heq := drop_tail_partOf_dynamic t w hsf xs (ws.map (partOf t) ++ ys) rest
            rw [← heq, List.length_drop]
            omega)]
        dsimp only
        have hoff' : off + t.headSize = headSizes (xs ++ [partOf t w]) := by
          rw [hoff, headSizes_append]
          simp only [headSizes, partOf_dynamic t w hsf, Part.headSize]
          rw [headSize_of_dynamic t hsf]
        have hE' : tailOffset (((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys) xs.length +
            (encode t w).length =
            tailOffset (((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys)
              (xs ++ [partOf t w]).length := by
          have hll : (xs ++ [partOf t w]).length = xs.length + 1 := by simp [List.length_append]
          rw [hll, tailOffset_succ _ _ _ _ hre.symm, tailSize_partOf_dynamic t w hsf]
        rw [hre] at hE ⊢
        rw [ih (ws.length) rfl hlsw (xs ++ [partOf t w]) (off + t.headSize) hoff' _ hE' hwf' hb']
        simp only [tailSizes, tailSize_partOf_dynamic t w hsf]
        rw [hE]
        congr 1
        omega
termination_by 8 * sizeOf t + 1

/-- Tuples validate from their own encoding inside a larger head/tail
layout, the frontier advancing exactly along the tails. -/
theorem validateTuple_encode_append : (ts : List Ty) → AllValid ts → (vs : TupleVal ts) →
    TupleLenBounds ts vs → (xs ys : List Part) → (off : Nat) → off = headSizes xs →
    (E : Nat) → E = tailOffset (xs ++ partsOfTuple ts vs ++ ys) xs.length →
    (rest : List UInt8) → WF (xs ++ partsOfTuple ts vs ++ ys) →
    (encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest).length < 2 ^ 256 →
    validateTuple ts (encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest) off E =
      some (E + tailSizes (partsOfTuple ts vs))
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => by
      simp only [partsOfTuple, validateTuple, tailSizes, Nat.add_zero]
  | t :: ts, hv, (v, vs), hls, xs, ys, off, hoff, E, hE, rest, hwf, hb => by
      obtain ⟨hvt, hvs⟩ := hv
      have hlc : LenBound t v ∧ TupleLenBounds ts vs := by simpa [TupleLenBounds] using hls
      obtain ⟨hlv, hlvs⟩ := hlc
      simp only [partsOfTuple, validateTuple]
      simp only [partsOfTuple] at hwf hb hE
      simp only [List.append_assoc, List.cons_append] at hwf hb hE ⊢
      have hre : xs ++ (partOf t v :: (partsOfTuple ts vs ++ ys)) =
          ((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys := by
        simp [List.append_assoc]
      have hwf' : WF (((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys) := by rwa [← hre]
      have hb' : (encodeParts (((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys) ++ rest).length <
          2 ^ 256 := by rwa [← hre]
      by_cases hs : t.IsStatic
      · rw [validateElem_static t _ _ _ hs]
        rw [drop_head_partOf_static t hs v xs (partsOfTuple ts vs ++ ys) rest off hoff]
        rw [validate_encode_append t hvt v hlv _
          (by
            have heq := drop_head_partOf_static t hs v xs (partsOfTuple ts vs ++ ys) rest off hoff
            rw [← heq, List.length_drop]
            omega)]
        dsimp only
        have hoff' : off + t.headSize = headSizes (xs ++ [partOf t v]) := by
          rw [hoff, headSizes_append]
          simp only [headSizes, partOf_static t v hs, Part.headSize]
          rw [encode_length_static t hs hvt v]
          omega
        have hE' : E = tailOffset (((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys)
            (xs ++ [partOf t v]).length := by
          have hll : (xs ++ [partOf t v]).length = xs.length + 1 := by simp [List.length_append]
          rw [hll, tailOffset_succ _ _ _ _ hre.symm, tailSize_partOf_static t v hs,
            Nat.add_zero, ← hre]
          exact hE
        rw [hre] at hE ⊢
        rw [validateTuple_encode_append ts hvs vs hlvs (xs ++ [partOf t v]) ys (off + t.headSize)
          hoff' E hE' rest hwf' hb']
        simp only [tailSizes, tailSize_partOf_static t v hs, Nat.zero_add]
      · have hsf : t.IsStatic = false := by simp at hs; exact hs
        rw [validateElem_dynamic t _ _ _ hsf]
        rw [show off / 32 = headSizes xs / 32 by rw [hoff]]
        rw [natAt_offset_partOf_dynamic t v hsf xs (partsOfTuple ts vs ++ ys) rest hwf hb]
        dsimp only
        rw [if_pos hE.symm]
        rw [drop_tail_partOf_dynamic t v hsf xs (partsOfTuple ts vs ++ ys) rest]
        rw [validate_encode_append t hvt v hlv _
          (by
            have heq := drop_tail_partOf_dynamic t v hsf xs (partsOfTuple ts vs ++ ys) rest
            rw [← heq, List.length_drop]
            omega)]
        dsimp only
        have hoff' : off + t.headSize = headSizes (xs ++ [partOf t v]) := by
          rw [hoff, headSizes_append]
          simp only [headSizes, partOf_dynamic t v hsf, Part.headSize]
          rw [headSize_of_dynamic t hsf]
        have hE' : tailOffset (((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys) xs.length +
            (encode t v).length =
            tailOffset (((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys)
              (xs ++ [partOf t v]).length := by
          have hll : (xs ++ [partOf t v]).length = xs.length + 1 := by simp [List.length_append]
          rw [hll, tailOffset_succ _ _ _ _ hre.symm, tailSize_partOf_dynamic t v hsf]
        rw [hre] at hE ⊢
        rw [validateTuple_encode_append ts hvs vs hlvs (xs ++ [partOf t v]) ys (off + t.headSize)
          hoff' _ hE' rest hwf' hb']
        simp only [tailSizes, tailSize_partOf_dynamic t v hsf]
        rw [hE]
        congr 1
        omega
termination_by ts => 8 * sizeOf ts + 2
end

/-! ## Package C2: lenient decoding is complete on canonical input -/

/- Every check `validate` performs is also performed (or subsumed) by the
lenient decoder, so a validating buffer always decodes.  Stated with
existentials since the decoded value is not needed here; C3 pins it down. -/
mutual
/-- **Lenient completeness on canonical input**: whatever validates also
lenient-decodes. -/
theorem validate_decode (t : Ty) (buf : List UInt8) (n : Nat)
    (h : validate t buf = some n) : ∃ v, decode t buf = some v := by
  cases t with
  | uint m =>
      simp only [validate] at h
      cases hdu : decodeUint buf with
      | none => simp only [hdu] at h; contradiction
      | some x =>
          simp only [hdu] at h
          by_cases hx : x < 2 ^ m
          · rw [if_pos hx] at h
            exact ⟨⟨x, hx⟩, by simp only [decode]; rw [hdu]; exact dif_pos hx⟩
          · rw [if_neg hx] at h; contradiction
  | int m =>
      simp only [validate] at h
      cases hdi : decodeInt buf with
      | none => simp only [hdi] at h; contradiction
      | some i =>
          simp only [hdi] at h
          by_cases hi : -((2 ^ (m - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m - 1) : Nat) : Int)
          · rw [if_pos hi] at h
            exact ⟨⟨i, hi⟩, by simp only [decode]; rw [hdi]; exact dif_pos hi⟩
          · rw [if_neg hi] at h; contradiction
  | bool =>
      simp only [validate] at h
      cases hdb : decodeBool buf with
      | none => simp only [hdb] at h; contradiction
      | some b => exact ⟨b, by simp only [decode]; exact hdb⟩
  | address =>
      simp only [validate] at h
      cases hda : decodeAddress buf with
      | none => simp only [hda] at h; contradiction
      | some x =>
          simp only [hda] at h
          by_cases hx : x < 2 ^ 160
          · rw [if_pos hx] at h
            exact ⟨⟨x, hx⟩, by simp only [decode]; rw [hda]; exact dif_pos hx⟩
          · rw [if_neg hx] at h; contradiction
  | bytesN m =>
      simp only [validate] at h
      cases hdb : decodeBytesN m buf with
      | none => simp only [hdb] at h; contradiction
      | some bs =>
          simp only [hdb] at h
          by_cases hbs : bs.length = m
          · rw [if_pos hbs] at h
            exact ⟨⟨bs, hbs⟩, by simp only [decode]; rw [hdb]; exact dif_pos hbs⟩
          · rw [if_neg hbs] at h; contradiction
  | bytes =>
      simp only [validate] at h
      cases hp : decodeBytesPrefix buf with
      | none => simp only [hp] at h; contradiction
      | some p =>
          obtain ⟨bs, m⟩ := p
          exact ⟨bs, by simp only [decode, hp, Option.map_some]⟩
  | string =>
      simp only [validate] at h
      cases hp : decodeBytesPrefix buf with
      | none => simp only [hp] at h; contradiction
      | some p =>
          obtain ⟨bs, m⟩ := p
          simp only [hp] at h
          cases hs : String.fromUTF8? bs.toByteArray with
          | none => simp only [hs] at h; contradiction
          | some s =>
              exact ⟨s, by simp only [decode, hp, Option.bind_some, hs]⟩
  | array t =>
      simp only [validate] at h
      cases hk : natAt buf 0 with
      | none => simp only [hk] at h; contradiction
      | some k =>
          simp only [hk] at h
          cases he : validateElems t k (buf.drop 32) 0 (k * t.headSize) with
          | none => simp only [he] at h; contradiction
          | some E₁ =>
              obtain ⟨vs, hvs⟩ := validateElems_decode t k (buf.drop 32) 0 (k * t.headSize) E₁ he
              exact ⟨vs.val, by simp only [decode, hk, hvs, Option.map_some]⟩
  | fixedArray t n' =>
      simp only [validate] at h
      obtain ⟨vs, hvs⟩ := validateElems_decode t n' buf 0 (n' * t.headSize) n h
      exact ⟨vs, by simp only [decode]; exact hvs⟩
  | tuple ts =>
      simp only [validate] at h
      obtain ⟨vs, hvs⟩ := validateTuple_decode ts buf 0 (headSizeSum ts) n h
      exact ⟨vs, by simp only [decode]; exact hvs⟩
termination_by 8 * sizeOf t

/-- A validating component read succeeds in the lenient decoder. -/
theorem validateElem_decode (t : Ty) (buf : List UInt8) (off E E' : Nat)
    (h : validateElem t buf off E = some E') : ∃ v, readElem t buf off = some v := by
  by_cases hs : t.IsStatic
  · rw [validateElem_static t _ _ _ hs] at h
    cases hv : validate t (buf.drop off) with
    | none => simp only [hv] at h; contradiction
    | some m =>
        obtain ⟨v, hd⟩ := validate_decode t (buf.drop off) m hv
        exact ⟨v, by rw [readElem_static t _ _ hs]; exact hd⟩
  · have hsf : t.IsStatic = false := by simp at hs; exact hs
    rw [validateElem_dynamic t _ _ _ hsf] at h
    cases hn : natAt buf (off / 32) with
    | none => simp only [hn] at h; contradiction
    | some o =>
        simp only [hn] at h
        by_cases ho : o = E
        · rw [if_pos ho] at h
          cases hv : validate t (buf.drop o) with
          | none => simp only [hv] at h; contradiction
          | some m =>
              obtain ⟨v, hd⟩ := validate_decode t (buf.drop o) m hv
              exact ⟨v, by rw [readElem_dynamic t _ _ hsf, hn]; exact hd⟩
        · rw [if_neg ho] at h; contradiction
termination_by 8 * sizeOf t + 1

/-- A validating element run lenient-decodes. -/
theorem validateElems_decode (t : Ty) (k : Nat) (buf : List UInt8) (off E E' : Nat)
    (h : validateElems t k buf off E = some E') :
    ∃ vs, decodeElems t k buf off = some vs := by
  induction k generalizing off E with
  | zero =>
      simp only [decodeElems]
      exact ⟨_, rfl⟩
  | succ k ih =>
      simp only [validateElems] at h
      cases he : validateElem t buf off E with
      | none => simp only [he] at h; contradiction
      | some E₁ =>
          simp only [he] at h
          obtain ⟨v, hv⟩ := validateElem_decode t buf off E E₁ he
          obtain ⟨vs, hvs⟩ := ih (off + t.headSize) E₁ h
          simp only [decodeElems, hv, hvs]
          exact ⟨_, rfl⟩
termination_by 8 * sizeOf t + 2

/-- A validating tuple walk lenient-decodes. -/
theorem validateTuple_decode : (ts : List Ty) → (buf : List UInt8) → (off E E' : Nat) →
    validateTuple ts buf off E = some E' → ∃ vs, decodeTuple ts buf off = some vs
  | [], _, _, _, _, h => by
      exact ⟨(), by simp only [decodeTuple]⟩
  | t :: ts, buf, off, E, E', h => by
      simp only [validateTuple] at h
      cases he : validateElem t buf off E with
      | none => simp only [he] at h; contradiction
      | some E₁ =>
          simp only [he] at h
          obtain ⟨v, hv⟩ := validateElem_decode t buf off E E₁ he
          obtain ⟨vs, hvs⟩ := validateTuple_decode ts buf (off + t.headSize) E₁ E' h
          simp only [decodeTuple, hv, hvs]
          exact ⟨_, rfl⟩
termination_by ts => 8 * sizeOf ts + 3
end

/-! ## Package C3: canonical soundness -/

/-- `decodeBool` succeeds exactly on the canonical boolean words. -/
theorem decodeBool_eq_some_iff (buf : List UInt8) (b : Bool) :
    decodeBool buf = some b ↔ decodeUint buf = some (if b then 1 else 0) := by
  unfold decodeBool
  cases hdu : decodeUint buf with
  | none => simp
  | some x =>
      cases x with
      | zero => cases b <;> simp
      | succ x =>
          cases x with
          | zero => cases b <;> simp
          | succ x => cases b <;> simp <;> omega

/-- A successful prefix decode determines the consumed prefix: it is exactly
the encoding of the decoded bytes. -/
theorem take_eq_encodeBytes_of_decodeBytesPrefix (buf : List UInt8) (bs : List UInt8) (m : Nat)
    (h : decodeBytesPrefix buf = some (bs, m)) :
    buf.take m = encodeBytes bs ∧ m = (encodeBytes bs).length := by
  simp only [decodeBytesPrefix] at h
  cases hlen : natAt buf 0 with
  | none => simp only [hlen, Option.bind_none] at h; contradiction
  | some len =>
      simp only [hlen, Option.bind_some] at h
      by_cases hc : ((buf.drop 32).take len).length = len ∧
          ((buf.drop 32).drop len).take ((32 - len % 32) % 32) =
            List.replicate ((32 - len % 32) % 32) 0
      · rw [if_pos hc] at h
        have h2 := Option.some.inj h
        have hbs : (buf.drop 32).take len = bs := congrArg Prod.fst h2
        have hm : 32 + len + (32 - len % 32) % 32 = m := congrArg Prod.snd h2
        have htake32 := take_32_eq_encodeUint_of_natAt buf 0 len hlen
        simp only [Nat.mul_zero, List.drop_zero] at htake32
        have hblen : bs.length = len := by rw [← hbs]; exact hc.1
        subst hm
        constructor
        · have hsplit : buf.take (32 + len + (32 - len % 32) % 32) =
              buf.take 32 ++ (buf.drop 32).take (len + (32 - len % 32) % 32) := by
            rw [← List.take_add]
            congr 1
            omega
          rw [hsplit, htake32, List.take_add, hbs, hc.2]
          rw [encodeBytes, pad32, ← hblen]
        · rw [encodeBytes, List.length_append, length_encodeUint, length_pad32, ← hblen]
          omega
      · rw [if_neg hc] at h; contradiction

/- A buffer that validates and lenient-decodes to `v` has `encode t v` as
its consumed prefix: canonical buffers are precisely the image of `encode`.
The walker lemmas establish this segment-wise: the head segment of the
walked section equals `encodeHeads` of the decoded components' parts (with
the frontier as the first tail offset), the tail segment equals
`encodeTails`, and the frontier advances exactly by the tails' total size.
`Valid` is needed for the head-size arithmetic; note the statement is
otherwise unconditional (no `2^256` bound — the offset-equality check
itself bounds every frontier). -/

/-- When `decodeUint` succeeds, the first 32 bytes of the buffer are the
big-endian encoding of the decoded value. -/
theorem buf_take_32_eq_encodeUint_of_decodeUint (buf : List UInt8) (x : Nat)
    (hdu : decodeUint buf = some x) : buf.take 32 = encodeUint x := by
  have h := take_32_eq_encodeUint_of_natAt buf 0 x hdu
  simp [Nat.mul_zero, List.drop_zero] at h
  exact h

mutual
/-- **Canonical soundness**: validation plus lenient decoding pins the
buffer down to the encoding of the decoded value. -/
theorem encode_eq_take_of_validate (t : Ty) (hv : t.Valid) (buf : List UInt8) (n : Nat)
    (hval : validate t buf = some n) (v : t.Val) (hd : decode t buf = some v) :
    buf.take n = encode t v ∧ n = (encode t v).length := by
  cases t with
  | uint m =>
      simp only [validate] at hval
      cases hdu : decodeUint buf with
      | none => simp only [hdu] at hval; contradiction
      | some x =>
          simp only [hdu] at hval
          by_cases hx : x < 2 ^ m
          · rw [if_pos hx] at hval
            have hn : n = 32 := (Option.some.inj hval).symm
            simp only [decode] at hd
            simp only [hdu] at hd
            rw [dif_pos hx] at hd
            have hv' : v = ⟨x, hx⟩ := (Option.some.inj hd).symm
            subst hv'; subst hn
            have htake := buf_take_32_eq_encodeUint_of_decodeUint buf x hdu
            simp [encode, length_encodeUint, htake]
          · rw [if_neg hx] at hval; contradiction
  | int m =>
      simp only [validate] at hval
      cases hdi : decodeInt buf with
      | none => simp only [hdi] at hval; contradiction
      | some i =>
          simp only [hdi] at hval
          by_cases hi : -((2 ^ (m - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m - 1) : Nat) : Int)
          · rw [if_pos hi] at hval
            have hn : n = 32 := (Option.some.inj hval).symm
            simp only [decode] at hd
            simp only [hdi] at hd
            rw [dif_pos hi] at hd
            have hv' : v = ⟨i, hi⟩ := (Option.some.inj hd).symm
            subst hv'
            subst hn
            simp only [decodeInt] at hdi
            cases hdu : decodeUint buf with
            | none => simp only [hdu, Option.map_none] at hdi; contradiction
            | some x =>
                simp only [hdu, Option.map_some] at hdi
                have hx256 : x < 2 ^ 256 := by
                  simp only [decodeUint, natAt] at hdu
                  cases hw : wordAt buf 0 with
                  | none => simp only [hw, Option.map_none] at hdu; contradiction
                  | some w =>
                      simp only [hw, Option.map_some, Option.some.injEq] at hdu
                      rw [← hdu]
                      exact UInt256.toNat_lt w
                have hxi : (if x < 2 ^ 255 then (x : Int) else (x : Int) - 2 ^ 256) = i :=
                  Option.some.inj hdi
                have henc := encodeInt_eq_encodeUint_of_decodeInt x hx256 i hxi
                have htake := take_32_eq_encodeUint_of_natAt buf 0 x hdu
                simp only [Nat.mul_zero, List.drop_zero] at htake
                constructor
                · simp only [encode]
                  rw [henc]
                  exact htake
                · simp only [encode, encodeInt, length_encodeUint]
          · rw [if_neg hi] at hval; contradiction
  | bool =>
      simp only [validate] at hval
      cases hdb : decodeBool buf with
      | none => simp only [hdb] at hval; contradiction
      | some b =>
          simp only [hdb] at hval
          have hn : n = 32 := (Option.some.inj hval).symm
          have hdu : decodeUint buf = some (if b then 1 else 0) :=
            (decodeBool_eq_some_iff buf b).mp hdb
          have htake := buf_take_32_eq_encodeUint_of_decodeUint buf (if b then 1 else 0) hdu
          simp only [decode] at hd
          rw [hdb] at hd
          have hbv : b = v := Option.some.inj hd
          subst hbv; subst hn
          simp [encode, encodeBool, length_encodeUint, htake]
  | address =>
      simp only [validate] at hval
      cases hda : decodeAddress buf with
      | none => simp only [hda] at hval; contradiction
      | some x =>
          simp only [hda] at hval
          by_cases hx : x < 2 ^ 160
          · rw [if_pos hx] at hval
            have hn : n = 32 := (Option.some.inj hval).symm
            simp only [decode] at hd
            simp only [hda] at hd
            rw [dif_pos hx] at hd
            have hv' : v = ⟨x, hx⟩ := (Option.some.inj hd).symm
            subst hv'; subst hn
            have htake := buf_take_32_eq_encodeUint_of_decodeUint buf x hda
            simp [encode, encodeAddress, length_encodeUint, htake]
          · rw [if_neg hx] at hval; contradiction
  | bytesN m =>
      simp only [validate] at hval
      cases hdb : decodeBytesN m buf with
      | none => simp only [hdb] at hval; contradiction
      | some bs =>
          simp only [hdb] at hval
          by_cases hbs : bs.length = m
          · rw [if_pos hbs] at hval
            have hn : n = 32 := (Option.some.inj hval).symm
            simp only [decode] at hd
            simp only [hdb] at hd
            rw [dif_pos hbs] at hd
            have hv' : v = ⟨bs, hbs⟩ := (Option.some.inj hd).symm
            subst hv'
            subst hn
            simp only [decodeBytesN] at hdb
            by_cases hc : ((buf.take 32).take m).length = m ∧
                (buf.take 32).drop m = List.replicate (32 - m) 0
            · rw [if_pos hc] at hdb
              have hbs' : bs = (buf.take 32).take m := (Option.some.inj hdb).symm
              constructor
              · simp only [encode]
                show buf.take 32 = bs ++ List.replicate (32 - bs.length) 0
                rw [hbs, hbs', ← hc.2, List.take_append_drop]
              · simp only [encode]
                show 32 = (encodeBytesN bs).length
                rw [length_encodeBytesN (by rw [hbs]; exact hv.2)]
            · rw [if_neg hc] at hdb; contradiction
          · rw [if_neg hbs] at hval; contradiction
  | bytes =>
      simp only [validate] at hval
      cases hp : decodeBytesPrefix buf with
      | none => simp only [hp] at hval; contradiction
      | some p =>
          obtain ⟨bs, m'⟩ := p
          simp only [hp, Option.map_some] at hval
          have hn : m' = n := Option.some.inj hval
          simp only [decode] at hd
          simp only [hp, Option.map_some] at hd
          have hv' : bs = v := Option.some.inj hd
          subst hv'
          subst hn
          simp only [encode]
          exact take_eq_encodeBytes_of_decodeBytesPrefix buf bs m' hp
  | string =>
      simp only [validate] at hval
      cases hp : decodeBytesPrefix buf with
      | none => simp only [hp] at hval; contradiction
      | some p =>
          obtain ⟨bs, m'⟩ := p
          simp only [hp] at hval
          cases hs : String.fromUTF8? bs.toByteArray with
          | none => simp only [hs] at hval; contradiction
          | some s =>
              simp only [hs] at hval
              have hn : m' = n := Option.some.inj hval
              simp only [decode] at hd
              simp only [hp, Option.bind_some, hs] at hd
              have hv' : s = v := Option.some.inj hd
              subst hv'
              subst hn
              obtain ⟨htake, hlen⟩ := take_eq_encodeBytes_of_decodeBytesPrefix buf bs m' hp
              have hutf : s.toUTF8 = bs.toByteArray := toUTF8_of_fromUTF8? hs
              have hbs : bs = s.toUTF8.data.toList := by
                have h1 : s.toUTF8.data.toList = bs := by
                  rw [hutf]
                  simp [List.data_toByteArray]
                exact h1.symm
              rw [hbs] at htake hlen
              simp only [encode, encodeString]
              exact ⟨htake, hlen⟩
  | array t =>
      simp only [validate] at hval
      cases hk : natAt buf 0 with
      | none => simp only [hk] at hval; contradiction
      | some k =>
          simp only [hk] at hval
          cases he : validateElems t k (buf.drop 32) 0 (k * t.headSize) with
          | none => simp only [he] at hval; contradiction
          | some E₁ =>
              simp only [he, Option.map_some] at hval
              have hn : n = 32 + E₁ := (Option.some.inj hval).symm
              simp only [decode] at hd
              simp only [hk] at hd
              cases hde : decodeElems t k (buf.drop 32) 0 with
              | none => simp only [hde] at hd; contradiction
              | some vs =>
                  simp only [hde, Option.map_some] at hd
                  have hv' : v = vs.val := (Option.some.inj hd).symm
                  have hvt : t.Valid := hv
                  obtain ⟨hhead, htail, hfront⟩ :=
                    segments_of_validateElems t hvt k (buf.drop 32) 0 (k * t.headSize) E₁
                      ⟨0, rfl⟩ he vs.val vs.property hde
                  have hE₀ : k * t.headSize = headSizes (vs.val.map (partOf t)) := by
                    rw [headSizes_map_partOf_any t hvt vs.val, vs.property]
                  subst hv'
                  subst hn
                  subst hfront
                  have hhead' : (buf.drop 32).take (k * t.headSize) =
                      encodeHeads (k * t.headSize) (vs.val.map (partOf t)) := by
                    simpa [List.drop_zero] using hhead
                  have htail' : ((buf.drop 32).drop (k * t.headSize)).take
                      (tailSizes (vs.val.map (partOf t))) = encodeTails (vs.val.map (partOf t)) := by
                    rw [Nat.add_sub_cancel_left] at htail
                    exact htail
                  have htake32 := take_32_eq_encodeUint_of_natAt buf 0 k hk
                  simp only [Nat.mul_zero, List.drop_zero] at htake32
                  constructor
                  · simp only [encode]
                    rw [List.take_add, htake32, List.take_add, hhead', htail', hE₀, vs.property]
                    rfl
                  · simp only [encode]
                    rw [List.length_append, length_encodeUint, length_encodeParts, hE₀]
  | fixedArray t n' =>
      obtain ⟨vs, hvs⟩ := v
      simp only [validate] at hval
      simp only [decode] at hd
      have hvt : t.Valid := hv
      obtain ⟨hhead, htail, hfront⟩ :=
        segments_of_validateElems t hvt n' buf 0 (n' * t.headSize) n ⟨0, rfl⟩ hval vs hvs hd
      have hE₀ : n' * t.headSize = headSizes (vs.map (partOf t)) := by
        rw [headSizes_map_partOf_any t hvt vs, hvs]
      subst hfront
      have hhead' : buf.take (n' * t.headSize) =
          encodeHeads (n' * t.headSize) (vs.map (partOf t)) := by
        simpa [List.drop_zero] using hhead
      have htail' : (buf.drop (n' * t.headSize)).take (tailSizes (vs.map (partOf t))) =
          encodeTails (vs.map (partOf t)) := by
        rw [Nat.add_sub_cancel_left] at htail
        exact htail
      constructor
      · simp only [encode]
        rw [List.take_add, hhead', htail', hE₀]
        rfl
      · simp only [encode]
        rw [length_encodeParts, hE₀]
  | tuple ts =>
      simp only [validate] at hval
      simp only [decode] at hd
      have hvts : AllValid ts := hv
      obtain ⟨hhead, htail, hfront⟩ :=
        segments_of_validateTuple ts hvts buf 0 (headSizeSum ts) n ⟨0, rfl⟩ hval v hd
      have hE₀ : headSizeSum ts = headSizes (partsOfTuple ts v) :=
        (headSizes_partsOfTuple_any ts hvts v).symm
      subst hfront
      have hhead' : buf.take (headSizeSum ts) =
          encodeHeads (headSizeSum ts) (partsOfTuple ts v) := by
        simpa [List.drop_zero] using hhead
      have htail' : (buf.drop (headSizeSum ts)).take (tailSizes (partsOfTuple ts v)) =
          encodeTails (partsOfTuple ts v) := by
        rw [Nat.add_sub_cancel_left] at htail
        exact htail
      constructor
      · simp only [encode]
        rw [List.take_add, hhead', htail', hE₀]
        rfl
      · simp only [encode]
        rw [length_encodeParts, hE₀]
termination_by 8 * sizeOf t

/-- Segment-wise soundness for element runs. -/
theorem segments_of_validateElems (t : Ty) (hv : t.Valid) (k : Nat)
    (buf : List UInt8) (off E E' : Nat) (ho : 32 ∣ off)
    (hval : validateElems t k buf off E = some E')
    (vs : List t.Val) (hvs : vs.length = k)
    (hd : decodeElems t k buf off = some ⟨vs, hvs⟩) :
    (buf.drop off).take (k * t.headSize) = encodeHeads E (vs.map (partOf t)) ∧
    (buf.drop E).take (E' - E) = encodeTails (vs.map (partOf t)) ∧
    E' = E + tailSizes (vs.map (partOf t)) := by
  induction vs generalizing k off E with
  | nil =>
      subst hvs
      simp only [List.length_nil, validateElems] at hval
      have hE' : E' = E := (Option.some.inj hval).symm
      subst hE'
      simp [List.map_nil, encodeHeads, encodeTails, tailSizes]
  | cons w ws ih =>
      have hk' : k = ws.length + 1 := by rw [← hvs, List.length_cons]
      subst hk'
      simp only [validateElems] at hval
      cases he : validateElem t buf off E with
      | none => simp only [he] at hval; contradiction
      | some E₁ =>
          simp only [he] at hval
          simp only [decodeElems] at hd
          cases hr : readElem t buf off with
          | none => simp only [hr] at hd; contradiction
          | some v =>
              simp only [hr] at hd
              cases hd' : decodeElems t ws.length buf (off + t.headSize) with
              | none => simp only [hd'] at hd; contradiction
              | some ws' =>
                  obtain ⟨wsl, hsl⟩ := ws'
                  simp only [hd'] at hd
                  have hvw : v :: wsl = w :: ws :=
                    Subtype.ext_iff.mp (Option.some.inj hd)
                  obtain ⟨hveq, hwseq⟩ := List.cons.inj hvw
                  subst hveq
                  subst hwseq
                  by_cases hs : t.IsStatic
                  · rw [validateElem_static t _ _ _ hs] at he
                    cases hvn : validate t (buf.drop off) with
                    | none => simp only [hvn] at he; contradiction
                    | some n₁ =>
                        simp only [hvn] at he
                        have hE₁ : E = E₁ := Option.some.inj he
                        subst hE₁
                        rw [readElem_static t _ _ hs] at hr
                        obtain ⟨htake₁, hlen₁⟩ :=
                          encode_eq_take_of_validate t hv (buf.drop off) n₁ hvn v hr
                        have hn₁ : n₁ = t.headSize := validate_static_len t hs _ _ hvn
                        subst hn₁
                        have ho' : 32 ∣ off + t.headSize :=
                          aligned_add ho (dvd_headSize_static t hs)
                        obtain ⟨hhead', htail', hfront'⟩ :=
                          ih wsl.length (off + t.headSize) E ho' hval rfl hd'
                        have hsplit : (wsl.length + 1) * t.headSize =
                            t.headSize + wsl.length * t.headSize := by
                          rw [Nat.add_mul, Nat.one_mul]
                          omega
                        refine ⟨?_, ?_, ?_⟩
                        · rw [hsplit, List.take_add, List.drop_drop,
                            htake₁, hhead', List.map_cons, partOf_static t v hs]
                          rfl
                        · rw [List.map_cons, partOf_static t v hs]
                          exact htail'
                        · rw [hfront', List.map_cons]
                          simp only [tailSizes, tailSize_partOf_static t v hs, Nat.zero_add]
                  · have hsf : t.IsStatic = false := by simp at hs; exact hs
                    rw [validateElem_dynamic t _ _ _ hsf] at he
                    cases hn : natAt buf (off / 32) with
                    | none => simp only [hn] at he; contradiction
                    | some o =>
                        simp only [hn] at he
                        by_cases hoE : o = E
                        · rw [if_pos hoE] at he
                          cases hvn : validate t (buf.drop o) with
                          | none => simp only [hvn] at he; contradiction
                          | some n₁ =>
                              simp only [hvn] at he
                              have hE₁ : E₁ = o + n₁ := (Option.some.inj he).symm
                              subst o
                              subst hE₁
                              rw [readElem_dynamic t _ _ hsf] at hr
                              simp only [hn] at hr
                              obtain ⟨htake₁, hlen₁⟩ :=
                                encode_eq_take_of_validate t hv (buf.drop E) n₁ hvn v hr
                              have h32 : t.headSize = 32 := headSize_of_dynamic t hsf
                              have ho' : 32 ∣ off + 32 := aligned_add ho ⟨1, rfl⟩
                              rw [h32] at hval hd' ⊢
                              obtain ⟨hhead', htail', hfront'⟩ :=
                                ih wsl.length (off + 32) (E + n₁) ho' hval rfl hd'
                              rw [h32] at hhead'
                              have hsplit : (wsl.length + 1) * 32 =
                                  32 + wsl.length * 32 := by omega
                              have hword : (buf.drop off).take 32 = encodeUint E := by
                                have h1 := take_32_eq_encodeUint_of_natAt buf (off / 32) E hn
                                rw [Nat.mul_div_cancel' ho] at h1
                                exact h1
                              refine ⟨?_, ?_, ?_⟩
                              · rw [hsplit, List.take_add, List.drop_drop,
                                  hword, hhead', List.map_cons, partOf_dynamic t v hsf,
                                  hlen₁]
                                rfl
                              · have hE'E : E' - E = n₁ + tailSizes (wsl.map (partOf t)) := by
                                  omega
                                have htail'' : (buf.drop (E + n₁)).take
                                    (tailSizes (wsl.map (partOf t))) =
                                    encodeTails (wsl.map (partOf t)) := by
                                  have h1 : E' - (E + n₁) = tailSizes (wsl.map (partOf t)) := by
                                    omega
                                  rw [h1] at htail'
                                  exact htail'
                                rw [hE'E, List.take_add, List.drop_drop, htake₁, htail'',
                                  List.map_cons, partOf_dynamic t v hsf]
                                rfl
                              · rw [hfront', List.map_cons]
                                simp only [tailSizes, tailSize_partOf_dynamic t v hsf]
                                rw [hlen₁]
                                omega
                        · rw [if_neg hoE] at he; contradiction
termination_by 8 * sizeOf t + 1

/-- Segment-wise soundness for tuple walks. -/
theorem segments_of_validateTuple : (ts : List Ty) → AllValid ts →
    (buf : List UInt8) → (off E E' : Nat) → 32 ∣ off →
    validateTuple ts buf off E = some E' →
    (vs : TupleVal ts) → decodeTuple ts buf off = some vs →
    (buf.drop off).take (headSizeSum ts) = encodeHeads E (partsOfTuple ts vs) ∧
    (buf.drop E).take (E' - E) = encodeTails (partsOfTuple ts vs) ∧
    E' = E + tailSizes (partsOfTuple ts vs)
  | [], _, _, _, E, E', _, hval, vs, hd => by
      simp only [validateTuple] at hval
      have hE' : E' = E := (Option.some.inj hval).symm
      subst hE'
      simp [partsOfTuple, headSizeSum, encodeHeads, encodeTails, tailSizes]
  | t :: ts, hv, buf, off, E, E', ho, hval, (v, vs), hd => by
      obtain ⟨hvt, hvs⟩ := hv
      simp only [validateTuple] at hval
      cases he : validateElem t buf off E with
      | none => simp only [he] at hval; contradiction
      | some E₁ =>
          simp only [he] at hval
          simp only [decodeTuple] at hd
          cases hr : readElem t buf off with
          | none => simp only [hr] at hd; contradiction
          | some w =>
              simp only [hr] at hd
              cases hd' : decodeTuple ts buf (off + t.headSize) with
              | none => simp only [hd'] at hd; contradiction
              | some vs' =>
                  simp only [hd', Option.map_some] at hd
                  have hvw : (w, vs') = (v, vs) := Option.some.inj hd
                  injection hvw with hwe hve
                  subst w
                  subst vs'
                  by_cases hs : t.IsStatic
                  · rw [validateElem_static t _ _ _ hs] at he
                    cases hvn : validate t (buf.drop off) with
                    | none => simp only [hvn] at he; contradiction
                    | some n₁ =>
                        simp only [hvn] at he
                        have hE₁ : E = E₁ := Option.some.inj he
                        subst hE₁
                        rw [readElem_static t _ _ hs] at hr
                        obtain ⟨htake₁, hlen₁⟩ :=
                          encode_eq_take_of_validate t hvt (buf.drop off) n₁ hvn v hr
                        have hn₁ : n₁ = t.headSize := validate_static_len t hs _ _ hvn
                        subst hn₁
                        have ho' : 32 ∣ off + t.headSize :=
                          aligned_add ho (dvd_headSize_static t hs)
                        obtain ⟨hhead', htail', hfront'⟩ :=
                          segments_of_validateTuple ts hvs buf (off + t.headSize) E E' ho'
                            hval vs hd'
                        refine ⟨?_, ?_, ?_⟩
                        · simp only [headSizeSum]
                          rw [List.take_add, List.drop_drop, htake₁, hhead']
                          simp only [partsOfTuple]
                          rw [partOf_static t v hs]
                          rfl
                        · simp only [partsOfTuple]
                          rw [partOf_static t v hs]
                          exact htail'
                        · rw [hfront']
                          simp only [partsOfTuple, tailSizes, tailSize_partOf_static t v hs,
                            Nat.zero_add]
                  · have hsf : t.IsStatic = false := by simp at hs; exact hs
                    rw [validateElem_dynamic t _ _ _ hsf] at he
                    cases hn : natAt buf (off / 32) with
                    | none => simp only [hn] at he; contradiction
                    | some o =>
                        simp only [hn] at he
                        by_cases hoE : o = E
                        · rw [if_pos hoE] at he
                          cases hvn : validate t (buf.drop o) with
                          | none => simp only [hvn] at he; contradiction
                          | some n₁ =>
                              simp only [hvn] at he
                              have hE₁ : E₁ = o + n₁ := (Option.some.inj he).symm
                              subst o
                              subst hE₁
                              rw [readElem_dynamic t _ _ hsf] at hr
                              simp only [hn] at hr
                              obtain ⟨htake₁, hlen₁⟩ :=
                                encode_eq_take_of_validate t hvt (buf.drop E) n₁ hvn v hr
                              have h32 : t.headSize = 32 := headSize_of_dynamic t hsf
                              have ho' : 32 ∣ off + 32 := aligned_add ho ⟨1, rfl⟩
                              rw [h32] at hval hd'
                              obtain ⟨hhead', htail', hfront'⟩ :=
                                segments_of_validateTuple ts hvs buf (off + 32) (E + n₁) E' ho'
                                  hval vs hd'
                              have hword : (buf.drop off).take 32 = encodeUint E := by
                                have h1 := take_32_eq_encodeUint_of_natAt buf (off / 32) E hn
                                rw [Nat.mul_div_cancel' ho] at h1
                                exact h1
                              refine ⟨?_, ?_, ?_⟩
                              · simp only [headSizeSum, h32]
                                rw [List.take_add, List.drop_drop, hword, hhead']
                                simp only [partsOfTuple]
                                rw [partOf_dynamic t v hsf, hlen₁]
                                rfl
                              · have hE'E : E' - E =
                                    n₁ + tailSizes (partsOfTuple ts vs) := by omega
                                have htail'' : (buf.drop (E + n₁)).take
                                    (tailSizes (partsOfTuple ts vs)) =
                                    encodeTails (partsOfTuple ts vs) := by
                                  have h1 : E' - (E + n₁) = tailSizes (partsOfTuple ts vs) := by
                                    omega
                                  rw [h1] at htail'
                                  exact htail'
                                rw [hE'E, List.take_add, List.drop_drop, htake₁, htail'']
                                simp only [partsOfTuple]
                                rw [partOf_dynamic t v hsf]
                                rfl
                              · rw [hfront']
                                simp only [partsOfTuple, tailSizes,
                                  tailSize_partOf_dynamic t v hsf]
                                rw [hlen₁]
                                omega
                        · rw [if_neg hoE] at he; contradiction
termination_by ts => 8 * sizeOf ts + 2
end

/-! ## corollaries -/

/-- **Canonical completeness**: encodings validate, consuming exactly their
length. -/
theorem validate_encode (t : Ty) (hv : t.Valid) (v : t.Val) (hl : LenBound t v)
    (hb : (encode t v).length < 2 ^ 256) :
    validate t (encode t v) = some (encode t v).length := by
  have h := validate_encode_append t hv v hl [] (by rwa [List.append_nil])
  rwa [List.append_nil] at h

/-- The encoder's output is canonical. -/
theorem isCanonical_encode (t : Ty) (hv : t.Valid) (v : t.Val) (hl : LenBound t v)
    (hb : (encode t v).length < 2 ^ 256) : IsCanonical t (encode t v) :=
  validate_encode t hv v hl hb

/-- **Canonical roundtrip**: strict decode after encode. -/
theorem decodeCanonical_encode (t : Ty) (hv : t.Valid) (v : t.Val) (hl : LenBound t v)
    (hb : (encode t v).length < 2 ^ 256) :
    decodeCanonical t (encode t v) = some v := by
  simp only [decodeCanonical, validate_encode t hv v hl hb, ite_true]
  exact roundtrip t hv v hl hb

/-- **Canonical uniqueness**: a strictly decodable buffer IS the encoding of
its decoded value.  (Injectivity of `encode` itself is a one-liner from
`roundtrip`; this is the stronger statement that every canonical-decodable
byte string lies in the image of `encode`.) -/
theorem encode_of_decodeCanonical (t : Ty) (hv : t.Valid) (buf : List UInt8) (v : t.Val)
    (h : decodeCanonical t buf = some v) : encode t v = buf := by
  simp only [decodeCanonical] at h
  cases hv' : validate t buf with
  | none => simp only [hv'] at h; contradiction
  | some n =>
      simp only [hv'] at h
      by_cases hn : n = buf.length
      · rw [if_pos hn] at h
        have hC3 := (encode_eq_take_of_validate t hv buf n hv' v h).1
        rw [hn, List.take_length] at hC3
        exact hC3.symm
      · rw [if_neg hn] at h; contradiction

end EvmAbi
