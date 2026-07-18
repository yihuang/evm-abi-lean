import EvmAbi.Ty
import EvmAbi.Static
import EvmAbi.Dynamic
import EvmAbi.Align
import EvmAbi.Word
import EvmAbi.Parts

/-!
# EvmAbi.Codec

The full ABI codec (roadmap node 8): a single `encode : (t : Ty) → t.Val →
List UInt8` / `decode : (t : Ty) → List UInt8 → Option t.Val` over the whole
type universe, built on the head/tail combinator of `EvmAbi.Parts`.

Layout of the module:

* **encode family** — `encode` / `partOf` / `partsOfTuple` (mutual).  A
  component's `Part` is its inline encoding when static, or an empty head
  plus its encoding as tail when dynamic; `encodeParts` fills in the offset
  words.

* **decode family** — `decode` / `readElem` / `decodeElems` / `decodeTuple`
  (mutual).  Every decoder is *prefix-tolerant*: it reads its value from the
  front of the buffer and ignores the rest, so components compose inside a
  head/tail layout.  `readElem` follows the offset word for dynamic
  components; `decodeElems`/`decodeTuple` step through the head by
  `headSize`.

* **length and alignment packages** — static encodings occupy exactly their
  `headSize`; every encoding is 32-byte aligned (`WF` of the part lists).

* **roundtrip packages** — the static-prefix roundtrip
  (`decode_encode_append_static` family) and the full roundtrip
  (`decode_encode_append` family), ending in the unified `roundtrip`.

The mutual blocks use explicit measures (`sizeOf` with constant offsets
distinguishing the sibling levels) so the default `decreasing_tactic`
discharges every goal.
-/

namespace EvmAbi

open Ty
open Binary

/-! ## encode family -/

/- The encoder: `encode` assembles a value; `partOf` views a typed value as
a head/tail `Part`; `partsOfTuple` maps a tuple value to a list of parts. -/
mutual
/-- ABI encoder (type-indexed). -/
def encode : (t : Ty) → t.Val → List UInt8
  | .uint _, ⟨n, _⟩   => encodeUint n
  | .int _,  ⟨i, _⟩   => encodeInt i
  | .bool,   b         => encodeBool b
  | .address, ⟨n, _⟩  => encodeAddress n
  | .bytesN _, ⟨bs, _⟩ => encodeBytesN bs
  | .bytes,   bs       => encodeBytes bs
  | .string,  s        => encodeString s
  | .array t, vs       => encodeUint vs.length ++ encodeParts (vs.map (partOf t))
  | .fixedArray t _, ⟨vs, _⟩ => encodeParts (vs.map (partOf t))
  | .tuple ts, vs      => encodeParts (partsOfTuple ts vs)
termination_by t => (sizeOf t, 0)

/-- A value seen as a head/tail part: static values sit in the head,
dynamic values in the tail (their head is the offset word). -/
def partOf (t : Ty) (v : t.Val) : Part :=
  match t.IsStatic with
  | true => ⟨encode t v, [], false⟩
  | false => ⟨[], encode t v, true⟩
termination_by (sizeOf t, 1)

/-- A tuple value seen as a list of parts. -/
def partsOfTuple : (ts : List Ty) → TupleVal ts → List Part
  | [], _ => []
  | t :: ts, (v, vs) => partOf t v :: partsOfTuple ts vs
termination_by ts => (sizeOf ts, 2)
end

/-! ## decode family -/

/- The decoder, prefix-tolerant throughout.  `readElem` reads one component
at head offset `off`: static components are decoded in place, dynamic
components are reached by following the offset word.  `decodeElems` reads
`k` consecutive elements of the same type; `decodeTuple` walks a type list. -/
mutual
/-- ABI decoder (type-indexed, prefix-tolerant).  A malformed buffer or an
out-of-range value yields `none`. -/
def decode : (t : Ty) → List UInt8 → Option t.Val
  | .uint m, buf => match decodeUint buf with
    | some n => if h : n < 2 ^ m then some ⟨n, h⟩ else none
    | none => none
  | .int m, buf => match decodeInt buf with
    | some i => if h : -((2 ^ (m - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m - 1) : Nat) : Int) then
        some ⟨i, h⟩
      else none
    | none => none
  | .bool, buf => decodeBool buf
  | .address, buf => match decodeAddress buf with
    | some n => if h : n < 2 ^ 160 then some ⟨n, h⟩ else none
    | none => none
  | .bytesN m, buf => match decodeBytesN m buf with
    | some bs => if h : bs.length = m then some ⟨bs, h⟩ else none
    | none => none
  | .bytes, buf => (decodeBytesPrefix buf).map Prod.fst
  | .string, buf => (decodeBytesPrefix buf).bind fun (bs, _) =>
      String.fromUTF8? bs.toByteArray
  | .array t, buf => match natAt buf 0 with
    | none => none
    | some k =>
        (decodeElems t k (buf.drop 32) 0).bind fun ⟨vs, _⟩ =>
          if buf.take (encode (.array t) vs).length = encode (.array t) vs then some vs else none
  | .fixedArray t n, buf =>
      (decodeElems t n buf 0).bind fun vs =>
        if buf.take (encode (.fixedArray t n) vs).length = encode (.fixedArray t n) vs then
          some vs
        else
          none
  | .tuple ts, buf =>
      (decodeTuple ts buf 0).bind fun vs =>
        if buf.take (encode (.tuple ts) vs).length = encode (.tuple ts) vs then some vs else none
termination_by t => (sizeOf t, 0)

/-- Read one component at head offset `off`. -/
def readElem (t : Ty) (buf : List UInt8) (off : Nat) : Option t.Val :=
  match t.IsStatic with
  | true => decode t (buf.drop off)
  | false => match natAt buf (off / 32) with
    | none => none
    | some o => decode t (buf.drop o)
termination_by (sizeOf t, 1)

/-- Read `k` consecutive elements of type `t`, starting at head offset `off`. -/
def decodeElems (t : Ty) (k : Nat) (buf : List UInt8) (off : Nat) :
    Option { vs : List t.Val // vs.length = k } :=
  match k with
  | 0 => some ⟨[], rfl⟩
  | k + 1 => match readElem t buf off with
    | none => none
    | some v => match decodeElems t k buf (off + t.headSize) with
      | none => none
      | some ⟨vs, h⟩ => some ⟨v :: vs, by simp [List.length_cons, h]⟩
termination_by (sizeOf t, k + 2)

/-- Read a tuple, walking the head from offset `off`. -/
def decodeTuple : (ts : List Ty) → List UInt8 → Nat → Option (TupleVal ts)
  | [], _, _ => some ()
  | t :: ts, buf, off => match readElem t buf off with
    | none => none
    | some v => (decodeTuple ts buf (off + t.headSize)).map (v, ·)
termination_by ts => (sizeOf ts, 2)
end

/-! ## helper lemmas -/

/-- Dropping fewer bytes than the prefix length splits the append. -/
theorem drop_append_of_le {A B : List α} {i : Nat} (h : i ≤ A.length) :
    (A ++ B).drop i = A.drop i ++ B := by
  rw [List.drop_append, Nat.sub_eq_zero_of_le h, List.drop_zero]

/-- Taking fewer bytes than the prefix length truncates the append. -/
theorem take_append_of_le {A B : List α} {i : Nat} (h : i ≤ A.length) :
    (A ++ B).take i = A.take i := by
  rw [List.take_append, Nat.sub_eq_zero_of_le h, List.take_zero, List.append_nil]

/-- A word fully inside the prefix reads the same over an appended buffer. -/
theorem wordAt_append_left (A B : List UInt8) (i : Nat) (h : 32 * (i + 1) ≤ A.length) :
    wordAt (A ++ B) i = wordAt A i := by
  unfold wordAt
  have hdr : (A ++ B).drop (32 * i) = A.drop (32 * i) ++ B :=
    drop_append_of_le (by omega)
  have htk : (A.drop (32 * i) ++ B).take 32 = (A.drop (32 * i)).take 32 := by
    apply take_append_of_le
    rw [List.length_drop]
    omega
  rw [hdr, htk]

/-- `natAt` variant of `wordAt_append_left`. -/
theorem natAt_append_left (A B : List UInt8) (i : Nat) (h : 32 * (i + 1) ≤ A.length) :
    natAt (A ++ B) i = natAt A i := by
  simp only [natAt, wordAt_append_left A B i h]

/-- `partOf` of a static value is the inline head part. -/
theorem partOf_static (t : Ty) (v : t.Val) (h : t.IsStatic = true) :
    partOf t v = ⟨encode t v, [], false⟩ := by
  simp [partOf, h]

/-- `partOf` of a dynamic value is the offset-word head plus tail part. -/
theorem partOf_dynamic (t : Ty) (v : t.Val) (h : t.IsStatic = false) :
    partOf t v = ⟨[], encode t v, true⟩ := by
  simp [partOf, h]

/-- `readElem` of a static type decodes in place. -/
theorem readElem_static (t : Ty) (buf : List UInt8) (off : Nat) (h : t.IsStatic = true) :
    readElem t buf off = decode t (buf.drop off) := by
  simp [readElem, h]

/-- `readElem` of a dynamic type follows the offset word. -/
theorem readElem_dynamic (t : Ty) (buf : List UInt8) (off : Nat) (h : t.IsStatic = false) :
    readElem t buf off = match natAt buf (off / 32) with
      | none => none
      | some o => decode t (buf.drop o) := by
  simp [readElem, h]

/-- Dynamic types occupy exactly one offset word in the head. -/
theorem headSize_of_dynamic (t : Ty) (h : t.IsStatic = false) : t.headSize = 32 := by
  cases t
  case fixedArray t n =>
      have h' : t.IsStatic = false := by simpa [IsStatic] using h
      simp [headSize, h']
  case tuple ts =>
      have h' : allStatic ts = false := by simpa [IsStatic] using h
      simp [headSize, h']
  all_goals simp [headSize]

/-! ## Package A: head sizes and static encoding lengths -/

/- The head size of a static type is always a multiple of 32, and a static
encoding occupies exactly its head size.  The list siblings use the
`+1`-offset measure so the default decreasing tactic closes every goal. -/
mutual
/-- The head size of a static type is 32-byte aligned. -/
theorem dvd_headSize_static : (t : Ty) → t.IsStatic = true → 32 ∣ t.headSize
  | uint _, _ | int _, _ | Ty.bool, _ | address, _ | bytesN _, _ => ⟨1, by simp [headSize]⟩
  | bytes, hs | string, hs | array _, hs => by simp [IsStatic] at hs
  | fixedArray t n, hs => by
      have hst : t.IsStatic = true := by simp only [IsStatic] at hs; exact hs
      obtain ⟨k, hk⟩ := dvd_headSize_static t hst
      exact ⟨n * k, by simp only [headSize]; rw [if_pos hst, hk]; ac_rfl⟩
  | tuple ts, hs => by
      have hss : allStatic ts = true := by simp only [IsStatic] at hs; exact hs
      obtain ⟨k, hk⟩ := dvd_headSizeSum_static ts hss
      exact ⟨k, by simp only [headSize]; rw [if_pos hss, hk]⟩
termination_by t => 2 * sizeOf t

/-- The head size sum of an all-static type list is 32-byte aligned. -/
theorem dvd_headSizeSum_static : (ts : List Ty) → allStatic ts = true → 32 ∣ headSizeSum ts
  | [], _ => ⟨0, by simp [headSizeSum]⟩
  | t :: ts, hs => by
      simp only [allStatic] at hs
      rw [Bool.and_eq_true] at hs
      obtain ⟨hst, hss⟩ := hs
      obtain ⟨k1, hk1⟩ := dvd_headSize_static t hst
      obtain ⟨k2, hk2⟩ := dvd_headSizeSum_static ts hss
      exact ⟨k1 + k2, by simp only [headSizeSum]; rw [hk1, hk2]; omega⟩
termination_by ts => 2 * sizeOf ts + 1
end

mutual
/-- Static encodings occupy exactly their head size. -/
theorem encode_length_static : (t : Ty) → t.IsStatic = true → t.Valid → (v : t.Val) →
    (encode t v).length = t.headSize
  | uint _, _, _, ⟨n, _⟩ => by simp [encode, length_encodeUint, headSize]
  | int _, _, _, ⟨i, _⟩ => by
      simp only [encode]
      simp [encodeInt, length_encodeUint, headSize]
  | Ty.bool, _, _, b => by simp [encode, encodeBool, length_encodeUint, headSize]
  | address, _, _, ⟨n, _⟩ => by simp [encode, encodeAddress, length_encodeUint, headSize]
  | bytesN m, _, hv, ⟨bs, hbs⟩ => by
      obtain ⟨h1, h32⟩ := hv
      have hlen : (encodeBytesN bs).length = 32 := length_encodeBytesN (by omega)
      simp only [encode]
      rw [hlen]
      simp [headSize]
  | bytes, hs, _, _ | string, hs, _, _ | array _, hs, _, _ => by simp [IsStatic] at hs
  | fixedArray t n, hs, hv, ⟨vs, hvs⟩ => by
      have hst : t.IsStatic = true := by simp only [IsStatic] at hs; exact hs
      have hvt : t.Valid := hv
      have hlen : ∀ vs' : List t.Val, headSizes (vs'.map (partOf t)) =
          vs'.length * t.headSize ∧ tailSizes (vs'.map (partOf t)) = 0 := by
        intro vs'
        induction vs' with
        | nil => exact ⟨by simp [headSizes], by simp [tailSizes]⟩
        | cons w ws ih =>
            obtain ⟨ih1, ih2⟩ := ih
            rw [List.map_cons, partOf_static t w hst]
            constructor
            · simp only [headSizes, Part.headSize, List.length_cons]
              rw [ih1, encode_length_static t hst hvt w, Nat.add_mul, Nat.one_mul]
              omega
            · simp only [tailSizes, Part.tailSize, ih2]
      simp only [encode]
      rw [length_encodeParts, (hlen vs).1, (hlen vs).2, hvs, Nat.add_zero]
      simp only [headSize]
      rw [if_pos hst]
  | tuple ts, hs, hv, vs => by
      have hss : allStatic ts = true := by simp only [IsStatic] at hs; exact hs
      have hvts : AllValid ts := hv
      have hgoal : headSize (tuple ts) = headSizeSum ts := by
        simp only [headSize]
        rw [if_pos hss]
      rw [hgoal]
      simp only [encode]
      exact encode_length_static_tuple ts hss hvts vs
termination_by t => 2 * sizeOf t

/-- Static tuple encodings occupy exactly their head size sum. -/
theorem encode_length_static_tuple : (ts : List Ty) → allStatic ts = true → AllValid ts →
    (vs : TupleVal ts) → (encodeParts (partsOfTuple ts vs)).length = headSizeSum ts
  | [], _, _, _ => by
      simp [length_encodeParts, partsOfTuple, headSizes, tailSizes, headSizeSum]
  | t :: ts, hs, hv, (v, vs) => by
      simp only [allStatic] at hs
      rw [Bool.and_eq_true] at hs
      obtain ⟨hst, hss⟩ := hs
      obtain ⟨hvt, hvs⟩ := hv
      have hlen := encode_length_static_tuple ts hss hvs vs
      have hcom : headSizes (partsOfTuple ts vs) + tailSizes (partsOfTuple ts vs) =
          headSizeSum ts := by
        rw [← length_encodeParts]
        exact hlen
      simp only [partsOfTuple]
      rw [partOf_static t v hst, length_encodeParts]
      simp only [headSizes, tailSizes, Part.headSize, Part.tailSize, headSizeSum]
      rw [encode_length_static t hst hvt v]
      omega
termination_by ts => 2 * sizeOf ts + 1
end

/-- The head section of a static tuple encoding is exactly `headSizeSum ts` bytes. -/
theorem headSizes_partsOfTuple : (ts : List Ty) → allStatic ts = true → AllValid ts →
    (vs : TupleVal ts) → headSizes (partsOfTuple ts vs) = headSizeSum ts
  | [], _, _, _ => by simp [partsOfTuple, headSizes, headSizeSum]
  | t :: ts, hs, hv, (v, vs) => by
      simp only [allStatic] at hs
      rw [Bool.and_eq_true] at hs
      obtain ⟨hvt, hvs⟩ := hv
      simp only [partsOfTuple]
      rw [partOf_static t v hs.1]
      simp only [headSizes, Part.headSize, headSizeSum]
      rw [encode_length_static t hs.1 hvt v, headSizes_partsOfTuple ts hs.2 hvs vs]

/-- The head section of a static element list mapped through `partOf`. -/
theorem headSizes_map_partOf (t : Ty) (hs : t.IsStatic = true) (hv : t.Valid) :
    (vs : List t.Val) → headSizes (vs.map (partOf t)) = vs.length * t.headSize
  | [] => by simp [headSizes]
  | v :: vs => by
      rw [List.map_cons, partOf_static t v hs]
      simp only [headSizes, Part.headSize, List.length_cons]
      rw [encode_length_static t hs hv v, headSizes_map_partOf t hs hv vs,
        Nat.add_mul, Nat.one_mul]
      omega

/-! ## Package B: alignment and well-formedness -/

/- Every encoding is 32-byte aligned; equivalently every part list produced
by `partOf`/`partsOfTuple` is well-formed.  The three theorems are mutual:
alignment of a compound encoding reduces to well-formedness of its part
list, which reduces to alignment of each component. -/
mutual
/-- Every encoding is 32-byte aligned. -/
theorem encode_length_aligned (t : Ty) (hv : t.Valid) (v : t.Val) :
    Aligned (encode t v).length := by
  by_cases hs : t.IsStatic
  · rw [encode_length_static t hs hv v]
    exact dvd_headSize_static t hs
  · have hsf : t.IsStatic = false := by simp at hs; exact hs
    cases t with
    | uint m => simp [IsStatic] at hsf
    | int m => simp [IsStatic] at hsf
    | bool => simp [IsStatic] at hsf
    | address => simp [IsStatic] at hsf
    | bytesN m => simp [IsStatic] at hsf
    | bytes =>
        simp only [encode, encodeBytes, List.length_append, length_encodeUint]
        exact aligned_add (aligned_mul 1) (dvd_length_pad32 _)
    | string =>
        simp only [encode, encodeString, encodeBytes, List.length_append, length_encodeUint]
        exact aligned_add (aligned_mul 1) (dvd_length_pad32 _)
    | array t =>
        have hvt : t.Valid := hv
        simp only [encode, List.length_append, length_encodeUint]
        exact aligned_add (aligned_mul 1) (dvd_length_encodeParts (wf_map_partOf t hvt v))
    | fixedArray t n =>
        obtain ⟨vs, hvs⟩ := v
        have hvt : t.Valid := hv
        simp only [encode]
        exact dvd_length_encodeParts (wf_map_partOf t hvt vs)
    | tuple ts =>
        have hvts : AllValid ts := hv
        simp only [encode]
        exact dvd_length_encodeParts (wf_partsOfTuple ts hvts v)
termination_by 4 * sizeOf t

/-- Element lists mapped through `partOf` are well-formed. -/
theorem wf_map_partOf (t : Ty) (hv : t.Valid) (vs : List t.Val) :
    WF (vs.map (partOf t)) := by
  induction vs with
  | nil =>
      simp only [List.map_nil]
      exact wf_nil
  | cons w ws ih =>
      rw [List.map_cons]
      apply wf_cons
      · by_cases hs : t.IsStatic
        · rw [partOf_static t w hs]
          constructor
          · show 32 ∣ (encode t w).length
            rw [encode_length_static t hs hv w]
            exact dvd_headSize_static t hs
          · exact ⟨0, rfl⟩
        · have hsf : t.IsStatic = false := by simp at hs; exact hs
          rw [partOf_dynamic t w hsf]
          constructor
          · exact ⟨0, rfl⟩
          · show 32 ∣ (encode t w).length
            exact encode_length_aligned t hv w
      · exact ih
termination_by 4 * sizeOf t + 1

/-- Tuple part lists are well-formed. -/
theorem wf_partsOfTuple : (ts : List Ty) → AllValid ts → (vs : TupleVal ts) →
    WF (partsOfTuple ts vs)
  | [], _, _ => by
      simp only [partsOfTuple]
      exact wf_nil
  | t :: ts, hv, (v, vs) => by
      obtain ⟨hvt, hvs⟩ := hv
      simp only [partsOfTuple]
      apply wf_cons
      · by_cases hs : t.IsStatic
        · rw [partOf_static t v hs]
          constructor
          · show 32 ∣ (encode t v).length
            rw [encode_length_static t hs hvt v]
            exact dvd_headSize_static t hs
          · exact ⟨0, rfl⟩
        · have hsf : t.IsStatic = false := by simp at hs; exact hs
          rw [partOf_dynamic t v hsf]
          constructor
          · exact ⟨0, rfl⟩
          · show 32 ∣ (encode t v).length
            exact encode_length_aligned t hvt v
      · exact wf_partsOfTuple ts hvs vs
termination_by ts => 4 * sizeOf ts + 2
end

/-! ## Package C: static-prefix roundtrip -/

/- Appended-buffer read lemmas: every primitive decoder reads through a
suffix it does not care about.  Together with `drop_head_partOf_static`
(a static part's head sits at its head offset) they give the static
roundtrip in *prefix* form — the shape tuple and array decoding need. -/

/-- `uintM` read-back over an appended suffix. -/
theorem decodeUint_append (n : Nat) (rest : List UInt8) (h : n < 2 ^ 256) :
    decodeUint (encodeUint n ++ rest) = some n := by
  unfold decodeUint encodeUint
  have hw := natAt_append ([] : List UInt8) rest (UInt256.ofNat n) 0 (by simp)
  rw [List.nil_append] at hw
  rw [hw, UInt256.toNat_ofNat, Nat.mod_eq_of_lt (show n < UInt256.size from h)]

/-- `intM` read-back over an appended suffix. -/
theorem decodeInt_append {M : Nat} (hM0 : 0 < M) (hM : M ≤ 256)
    (hl : -((2 ^ (M - 1) : Nat) : Int) ≤ i) (hu : i < ((2 ^ (M - 1) : Nat) : Int))
    (rest : List UInt8) : decodeInt (encodeInt i ++ rest) = some i := by
  have hcast : ((2 ^ (M - 1) : Nat) : Int) = (2 : Int) ^ (M - 1) := Int.natCast_pow 2 (M - 1)
  rw [hcast] at hl hu
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
    rw [encodeInt, if_pos hi, decodeInt, decodeUint_append _ rest hn, Option.map_some,
      if_pos (show i.toNat < 2 ^ 255 by omega), Int.toNat_of_nonneg hi]
  · have hn1 : 2 ^ 256 - (-i).toNat ≥ 2 ^ 255 ∧ 2 ^ 256 - (-i).toNat < 2 ^ 256 := by
      omega
    rw [encodeInt, if_neg hi, decodeInt, decodeUint_append _ rest hn1.2, Option.map_some,
      if_neg (show ¬ 2 ^ 256 - (-i).toNat < 2 ^ 255 by omega)]
    have heq : ((2 ^ 256 - (-i).toNat : Nat) : Int) - 2 ^ 256 = i := by omega
    rw [heq]

/-- `bool` read-back over an appended suffix. -/
theorem decodeBool_append (b : Bool) (rest : List UInt8) :
    decodeBool (encodeBool b ++ rest) = some b := by
  cases b
  · show decodeBool (encodeUint 0 ++ rest) = some false
    unfold decodeBool
    rw [decodeUint_append 0 rest (by decide)]
    rfl
  · show decodeBool (encodeUint 1 ++ rest) = some true
    unfold decodeBool
    rw [decodeUint_append 1 rest (by decide)]
    rfl

/-- `address` read-back over an appended suffix. -/
theorem decodeAddress_append (a : Nat) (rest : List UInt8) (h : a < 2 ^ 160) :
    decodeAddress (encodeAddress a ++ rest) = some a :=
  decodeUint_append a rest
    (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (n := 2) (by decide) (by decide)))

/-- `bytesN` read-back over an appended suffix. -/
theorem decodeBytesN_append {n : Nat} (h32 : n ≤ 32) (h : bs.length = n)
    (rest : List UInt8) :
    decodeBytesN n (encodeBytesN bs ++ rest) = some bs := by
  unfold decodeBytesN encodeBytesN
  have hlen : (bs ++ List.replicate (32 - bs.length) 0).length = 32 := by
    rw [List.length_append, List.length_replicate]; omega
  have htk : ((bs ++ List.replicate (32 - bs.length) 0) ++ rest).take 32 =
      bs ++ List.replicate (32 - bs.length) 0 := take_append_of_length hlen
  rw [htk, take_append_of_length h, drop_append_of_length h, if_pos ⟨h, by rw [h]⟩]

/-- A static part's encoding sits at its head offset, even with further
parts and a trailing suffix after it. -/
theorem drop_head_partOf_static (t : Ty) (hs : t.IsStatic = true) (v : t.Val)
    (xs ys : List Part) (rest : List UInt8) (off : Nat) (hoff : off = headSizes xs) :
    (encodeParts (xs ++ (partOf t v :: ys)) ++ rest).drop off =
      encode t v ++ (encodeHeads (headSizes (xs ++ (partOf t v :: ys)) + tailSizes xs) ys ++
        (encodeTails (xs ++ (partOf t v :: ys)) ++ rest)) := by
  rw [partOf_static t v hs]
  have hle : off ≤ (encodeParts (xs ++ ⟨encode t v, [], false⟩ :: ys)).length := by
    rw [hoff, length_encodeParts, headSizes_append]
    omega
  rw [drop_append_of_le hle, hoff, drop_headOffset_static]
  simp only [List.append_assoc]

/- The static roundtrip, prefix form.  `decode_encode_append_static` is the
single-component statement; `decodeElems_static_append` and
`decodeTuple_static_append` generalize it to a run of static components
inside a larger head (the `xs` already-encoded prefix, the `ys` remaining
parts, `rest` everything after the encoding). -/
mutual
/-- **Static roundtrip, prefix form**: a static value decodes from the front
of its own encoding followed by an arbitrary suffix. -/
theorem decode_encode_append_static : (t : Ty) → t.IsStatic = true → t.Valid →
    (v : t.Val) → (rest : List UInt8) → decode t (encode t v ++ rest) = some v
  | uint m, hs, hv, ⟨n, hn⟩, rest => by
      have hdec : decodeUint (encodeUint n ++ rest) = some n :=
        decodeUint_append n rest
          (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (n := 2) (by decide) hv.2.1))
      simp only [encode, decode]
      rw [hdec]
      exact dif_pos hn
  | int m, hs, hv, ⟨i, hi⟩, rest => by
      have h0 : 0 < m := by have h8 := hv.1; omega
      have hdec : decodeInt (encodeInt i ++ rest) = some i :=
        decodeInt_append h0 hv.2.1 hi.1 hi.2 rest
      simp only [encode, decode]
      rw [hdec]
      exact dif_pos hi
  | Ty.bool, hs, hv, b, rest => by
      simp only [encode, decode]
      exact decodeBool_append b rest
  | address, hs, hv, ⟨n, hn⟩, rest => by
      have hdec : decodeAddress (encodeAddress n ++ rest) = some n :=
        decodeAddress_append n rest hn
      simp only [encode, decode]
      rw [hdec]
      exact dif_pos hn
  | bytesN m, hs, hv, ⟨bs, hbs⟩, rest => by
      have hdec : decodeBytesN m (encodeBytesN bs ++ rest) = some bs :=
        decodeBytesN_append hv.2 hbs rest
      simp only [encode, decode]
      rw [hdec]
      exact dif_pos hbs
  | bytes, hs, _, _, _ | string, hs, _, _, _ | array _, hs, _, _, _ => by
      simp [IsStatic] at hs
  | fixedArray t n, hs, hv, v, rest => by
      obtain ⟨vs, hvs⟩ := v
      have hst : t.IsStatic = true := by simp only [IsStatic] at hs; exact hs
      have hvt : t.Valid := hv
      simp only [decode, encode]
      have hraw := decodeElems_static_append t hst hvt vs n hvs [] [] 0 (by simp [headSizes]) rest
      have h : decodeElems t n (encodeParts (vs.map (partOf t)) ++ rest) 0 = some ⟨vs, hvs⟩ := by
        simpa [List.nil_append, List.append_nil] using hraw
      have henc :
          (encodeParts (vs.map (partOf t)) ++ rest).take
              (encode (.fixedArray t n) ⟨vs, hvs⟩).length =
            encode (.fixedArray t n) ⟨vs, hvs⟩ := by
        simp [encode, take_append_of_length]
      rw [h, Option.bind_some, if_pos henc]
  | tuple ts, hs, hv, v, rest => by
      have hss : allStatic ts = true := by simp only [IsStatic] at hs; exact hs
      have hvts : AllValid ts := hv
      simp only [decode, encode]
      have hraw := decodeTuple_static_append ts hss hvts v [] [] 0 (by simp [headSizes]) rest
      have h : decodeTuple ts (encodeParts (partsOfTuple ts v) ++ rest) 0 = some v := by
        simpa [List.nil_append, List.append_nil] using hraw
      have henc : (encodeParts (partsOfTuple ts v) ++ rest).take
          (encodeParts (partsOfTuple ts v)).length = encodeParts (partsOfTuple ts v) := by
        exact take_append_of_length rfl
      rw [h, Option.bind_some, if_pos henc]
termination_by t => 4 * sizeOf t

/-- Static element lists decode from their own encoding inside a larger
head/tail layout. -/
theorem decodeElems_static_append (t : Ty) (hs : t.IsStatic = true) (hv : t.Valid)
    (vs : List t.Val) (k : Nat) (hk : vs.length = k) (xs ys : List Part) (off : Nat)
    (hoff : off = headSizes xs) (rest : List UInt8) :
    decodeElems t k (encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest) off =
      some ⟨vs, hk⟩ := by
  induction vs generalizing k xs off with
  | nil =>
      subst hk
      simp only [List.map_nil, List.length_nil, decodeElems]
  | cons w ws ih =>
      have hk' : k = ws.length + 1 := by rw [← hk, List.length_cons]
      subst hk'
      simp only [List.map_cons, decodeElems]
      simp only [List.append_assoc, List.cons_append]
      rw [readElem_static t _ _ hs]
      rw [drop_head_partOf_static t hs w xs (ws.map (partOf t) ++ ys) rest off hoff]
      rw [decode_encode_append_static t hs hv w _]
      have hre : xs ++ (partOf t w :: (ws.map (partOf t) ++ ys)) =
          ((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys := by
        simp [List.append_assoc]
      have hoff' : off + t.headSize = headSizes (xs ++ [partOf t w]) := by
        rw [hoff, headSizes_append]
        simp only [headSizes, partOf_static t w hs, Part.headSize]
        rw [encode_length_static t hs hv w]
        omega
      rw [hre]
      rw [ih (ws.length) rfl (xs ++ [partOf t w]) (off + t.headSize) hoff']
termination_by 4 * sizeOf t + 1

/-- Static tuples decode from their own encoding inside a larger head/tail
layout. -/
theorem decodeTuple_static_append : (ts : List Ty) → allStatic ts = true → AllValid ts →
    (vs : TupleVal ts) → (xs ys : List Part) → (off : Nat) → off = headSizes xs →
    (rest : List UInt8) →
    decodeTuple ts (encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest) off = some vs
  | [], _, _, _, _, _, _, _, _ => by
      simp only [partsOfTuple, decodeTuple]
  | t :: ts, hall, hv, (v, vs), xs, ys, off, hoff, rest => by
      simp only [allStatic] at hall
      rw [Bool.and_eq_true] at hall
      obtain ⟨hst, hss⟩ := hall
      obtain ⟨hvt, hvs⟩ := hv
      simp only [partsOfTuple]
      simp only [decodeTuple]
      simp only [List.append_assoc, List.cons_append]
      rw [readElem_static t _ _ hst]
      rw [drop_head_partOf_static t hst v xs (partsOfTuple ts vs ++ ys) rest off hoff]
      rw [decode_encode_append_static t hst hvt v _]
      have hre : xs ++ (partOf t v :: (partsOfTuple ts vs ++ ys)) =
          ((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys := by
        simp [List.append_assoc]
      have hoff' : off + t.headSize = headSizes (xs ++ [partOf t v]) := by
        rw [hoff, headSizes_append]
        simp only [headSizes, partOf_static t v hst, Part.headSize]
        rw [encode_length_static t hst hvt v]
        omega
      rw [hre]
      rw [decodeTuple_static_append ts hss hvs vs (xs ++ [partOf t v]) ys
        (off + t.headSize) hoff' rest]
      rfl
termination_by ts => 4 * sizeOf ts + 2
end

/-! ## Roundtrips derived from the prefix forms -/

/-- **Static roundtrip**: every static type decodes its own encoding without
any side condition. -/
theorem roundtrip_static (t : Ty) (hs : t.IsStatic = true) (hv : t.Valid) (v : t.Val) :
    decode t (encode t v) = some v := by
  have h := decode_encode_append_static t hs hv v []
  rwa [List.append_nil] at h

/-- **Roundtrip** for dynamic `bytes` (requires the length word not to wrap). -/
theorem roundtrip_bytes (bs : List UInt8) (h : bs.length < 2 ^ 256) :
    decode .bytes (encode .bytes bs) = some bs := by
  have hr := decodeBytesPrefix_append (bs := bs) (rest := []) h
  rw [List.append_nil] at hr
  simp only [decode, encode]
  rw [hr]
  rfl

/-- **Roundtrip** for dynamic `string`. -/
theorem roundtrip_string (s : String) (h : s.toUTF8.size < 2 ^ 256) :
    decode .string (encode .string s) = some s := by
  have hb : s.toUTF8.data.toList.length < 2 ^ 256 := by
    rw [← Binary.ByteArray.size_eq_toList_length s.toUTF8]
    exact h
  have hr := decodeBytesPrefix_append (bs := s.toUTF8.data.toList) (rest := []) hb
  rw [List.append_nil] at hr
  simp only [decode, encode, encodeString]
  rw [hr, Option.bind_some, dataToList_toByteArray, fromUTF8?_toUTF8]

/-! ## Package D: the dynamic roundtrip -/

/- The static roundtrip (Package C) handled components sitting in the head.
Dynamic components sit in the tail and are reached through an offset word in
the head.  The lemmas below locate a dynamic part's tail inside a larger
head/tail layout (`drop_tail_partOf_dynamic`), show its offset word reads
back the correct tail offset (`natAt_offset_partOf_dynamic`), and combine
both into a single `readElem` rewrite (`readElem_partOf_dynamic`).  The
mutual block `decode_encode_append` / `decodeElems_append` /
`decodeTuple_append` then proves the roundtrip in prefix form for *all*
types, ending in the unified `roundtrip`. -/

/-- The tail offset of a dynamic part never exceeds the total encoding
length. -/
theorem tailOffset_partOf_dynamic_le (t : Ty) (v : t.Val) (h : t.IsStatic = false)
    (xs ys : List Part) :
    tailOffset (xs ++ (partOf t v :: ys)) xs.length ≤
      (encodeParts (xs ++ (partOf t v :: ys))).length := by
  rw [partOf_dynamic t v h, length_encodeParts, tailOffset, take_append_of_length rfl,
    tailSizes_append]
  simp [tailSizes, Part.tailSize]

/-- Dropping to a dynamic part's tail offset lands exactly on its tail, even
with a trailing suffix after the whole layout. -/
theorem drop_tail_partOf_dynamic (t : Ty) (v : t.Val) (h : t.IsStatic = false)
    (xs ys : List Part) (rest : List UInt8) :
    (encodeParts (xs ++ (partOf t v :: ys)) ++ rest).drop
      (tailOffset (xs ++ (partOf t v :: ys)) xs.length) =
    encode t v ++ (encodeTails ys ++ rest) := by
  have hle := tailOffset_partOf_dynamic_le t v h xs ys
  rw [partOf_dynamic t v h] at hle ⊢
  rw [drop_append_of_le hle, drop_tailOffset_append]
  simp only [List.append_assoc]

/-- The offset word of a dynamic part reads back its tail offset, even with a
trailing suffix after the whole layout. -/
theorem natAt_offset_partOf_dynamic (t : Ty) (v : t.Val) (h : t.IsStatic = false)
    (xs ys : List Part) (rest : List UInt8)
    (hwf : WF (xs ++ (partOf t v :: ys)))
    (hb : (encodeParts (xs ++ (partOf t v :: ys)) ++ rest).length < 2 ^ 256) :
    natAt (encodeParts (xs ++ (partOf t v :: ys)) ++ rest) (headSizes xs / 32) =
      some (tailOffset (xs ++ (partOf t v :: ys)) xs.length) := by
  have hle := tailOffset_partOf_dynamic_le t v h xs ys
  have hb0 : (encodeParts (xs ++ (partOf t v :: ys))).length < 2 ^ 256 := by
    rw [List.length_append] at hb
    omega
  rw [partOf_dynamic t v h] at hwf hle hb0 ⊢
  have hle32 : 32 * (headSizes xs / 32 + 1) ≤
      (encodeParts (xs ++ (⟨[], encode t v, true⟩ : Part) :: ys)).length := by
    have hd : 32 ∣ headSizes xs := dvd_headSizes fun q hq => hwf q (List.mem_append_left _ hq)
    rw [length_encodeParts, headSizes_append]
    simp only [headSizes, Part.headSize]
    omega
  rw [natAt_append_left _ _ _ hle32]
  simp only [natAt, wordAt_offset_append hwf, Option.map_some, UInt256.toNat_ofNat,
    Option.some.injEq]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hb0)

/-- Reading a dynamic component resolves its offset word and lands on its
tail. -/
theorem readElem_partOf_dynamic (t : Ty) (v : t.Val) (h : t.IsStatic = false)
    (xs ys : List Part) (rest : List UInt8) (off : Nat) (hoff : off = headSizes xs)
    (hwf : WF (xs ++ (partOf t v :: ys)))
    (hb : (encodeParts (xs ++ (partOf t v :: ys)) ++ rest).length < 2 ^ 256) :
    readElem t (encodeParts (xs ++ (partOf t v :: ys)) ++ rest) off =
      decode t (encode t v ++ (encodeTails ys ++ rest)) := by
  rw [readElem_dynamic t _ _ h, hoff,
    natAt_offset_partOf_dynamic t v h xs ys rest hwf hb]
  show decode t ((encodeParts (xs ++ (partOf t v :: ys)) ++ rest).drop
      (tailOffset (xs ++ (partOf t v :: ys)) xs.length)) =
    decode t (encode t v ++ (encodeTails ys ++ rest))
  rw [drop_tail_partOf_dynamic t v h xs ys rest]

mutual
/-- **Roundtrip, prefix form**: a value decodes from the front of its own
encoding followed by an arbitrary suffix.  `hb` bounds the whole buffer (so
no offset word wraps); `hl` bounds the dynamic payloads (so no length word
wraps). -/
theorem decode_encode_append (t : Ty) (hv : t.Valid) (v : t.Val) (hl : LenBound t v)
    (rest : List UInt8) (hb : (encode t v ++ rest).length < 2 ^ 256) :
    decode t (encode t v ++ rest) = some v := by
  by_cases hs : t.IsStatic
  · exact decode_encode_append_static t hs hv v rest
  · have hsf : t.IsStatic = false := by simp at hs; exact hs
    cases t with
    | uint m => simp [IsStatic] at hsf
    | int m => simp [IsStatic] at hsf
    | bool => simp [IsStatic] at hsf
    | address => simp [IsStatic] at hsf
    | bytesN m => simp [IsStatic] at hsf
    | bytes =>
        have hlb : v.length < 2 ^ 256 := by simpa [LenBound] using hl
        have hr := decodeBytesPrefix_append (bs := v) (rest := rest) hlb
        simp only [decode, encode]
        rw [hr]
        rfl
    | string =>
        have hlb : v.toUTF8.size < 2 ^ 256 := by simpa [LenBound] using hl
        have hb2 : v.toUTF8.data.toList.length < 2 ^ 256 := by
          rw [← Binary.ByteArray.size_eq_toList_length v.toUTF8]
          exact hlb
        have hr := decodeBytesPrefix_append (bs := v.toUTF8.data.toList) (rest := rest) hb2
        simp only [decode, encode, encodeString]
        rw [hr, Option.bind_some, dataToList_toByteArray, fromUTF8?_toUTF8]
    | array t =>
        have hla : v.length < 2 ^ 256 ∧ AllLenBound t v := by simpa [LenBound] using hl
        obtain ⟨hlk, hls⟩ := hla
        have hvt : t.Valid := hv
        have hbT : (encodeParts (v.map (partOf t)) ++ rest).length < 2 ^ 256 := by
          have hb' := hb
          simp only [encode, List.length_append, length_encodeUint] at hb'
          rw [List.length_append]
          omega
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
        have hde : decodeElems t v.length (encodeParts (v.map (partOf t)) ++ rest) 0 =
            some ⟨v, rfl⟩ := by
          have h := decodeElems_append t hvt v v.length rfl hls [] [] 0 (by simp [headSizes])
            rest (by simpa using wf_map_partOf t hvt v) (by simpa using hbT)
          simpa using h
        have henc :
            (encodeUint v.length ++ (encodeParts (v.map (partOf t)) ++ rest)).take
                (32 + (encodeParts (v.map (partOf t))).length) =
              encodeUint v.length ++ encodeParts (v.map (partOf t)) := by
          rw [← List.append_assoc]
          exact take_append_of_length (by simp [length_encodeUint])
        simpa [decode, encode, hcnt, hdrop, hde, henc, List.append_assoc]
    | fixedArray t n =>
        obtain ⟨vs, hvs⟩ := v
        have hvt : t.Valid := hv
        have hls : AllLenBound t vs := by simpa [LenBound] using hl
        have hraw := decodeElems_append t hvt vs n hvs hls [] [] 0 (by simp [headSizes]) rest
          (by simpa using wf_map_partOf t hvt vs) (by simpa [encode] using hb)
        have h : decodeElems t n (encodeParts (vs.map (partOf t)) ++ rest) 0 = some ⟨vs, hvs⟩ := by
          simpa [List.nil_append, List.append_nil] using hraw
        simp only [decode, encode]
        have henc :
            (encodeParts (vs.map (partOf t)) ++ rest).take
                (encode (.fixedArray t n) ⟨vs, hvs⟩).length =
              encode (.fixedArray t n) ⟨vs, hvs⟩ := by
          simp [encode, take_append_of_length]
        rw [h, Option.bind_some, if_pos henc]
    | tuple ts =>
        have hvts : AllValid ts := hv
        have hls : TupleLenBounds ts v := by simpa [LenBound] using hl
        have hraw := decodeTuple_append ts hvts v hls [] [] 0 (by simp [headSizes]) rest
          (by simpa using wf_partsOfTuple ts hvts v) (by simpa [encode] using hb)
        have h : decodeTuple ts (encodeParts (partsOfTuple ts v) ++ rest) 0 = some v := by
          simpa [List.nil_append, List.append_nil] using hraw
        simp only [decode, encode]
        have henc : (encodeParts (partsOfTuple ts v) ++ rest).take
            (encodeParts (partsOfTuple ts v)).length = encodeParts (partsOfTuple ts v) := by
          exact take_append_of_length rfl
        rw [h, Option.bind_some, if_pos henc]
termination_by 8 * sizeOf t

/-- Element lists decode from their own encoding inside a larger head/tail
layout, static components in place and dynamic ones through their offset
words. -/
theorem decodeElems_append (t : Ty) (hv : t.Valid) (vs : List t.Val) (k : Nat)
    (hk : vs.length = k) (hls : AllLenBound t vs)
    (xs ys : List Part) (off : Nat) (hoff : off = headSizes xs)
    (rest : List UInt8)
    (hwf : WF (xs ++ vs.map (partOf t) ++ ys))
    (hb : (encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest).length < 2 ^ 256) :
    decodeElems t k (encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest) off =
      some ⟨vs, hk⟩ := by
  induction vs generalizing k xs off with
  | nil =>
      subst hk
      simp only [List.map_nil, List.length_nil, decodeElems]
  | cons w ws ih =>
      have hk' : k = ws.length + 1 := by rw [← hk, List.length_cons]
      subst hk'
      have hlc : LenBound t w ∧ AllLenBound t ws := by simpa [AllLenBound] using hls
      obtain ⟨hlw, hlsw⟩ := hlc
      simp only [List.map_cons, decodeElems] at ⊢
      simp only [List.map_cons] at hwf hb
      simp only [List.append_assoc, List.cons_append] at hwf hb ⊢
      have hre : xs ++ (partOf t w :: (ws.map (partOf t) ++ ys)) =
          ((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys := by
        simp [List.append_assoc]
      have hwf' : WF (((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys) := by
        rwa [← hre]
      have hb' : (encodeParts (((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys) ++ rest).length <
          2 ^ 256 := by
        rwa [← hre]
      by_cases hs : t.IsStatic
      · rw [readElem_static t _ _ hs]
        rw [drop_head_partOf_static t hs w xs (ws.map (partOf t) ++ ys) rest off hoff]
        rw [decode_encode_append t hv w hlw _
          (by
            have heq := drop_head_partOf_static t hs w xs (ws.map (partOf t) ++ ys) rest off hoff
            rw [← heq, List.length_drop]
            omega)]
        have hoff' : off + t.headSize = headSizes (xs ++ [partOf t w]) := by
          rw [hoff, headSizes_append]
          simp only [headSizes, partOf_static t w hs, Part.headSize]
          rw [encode_length_static t hs hv w]
          omega
        rw [hre]
        rw [ih (ws.length) rfl hlsw (xs ++ [partOf t w]) (off + t.headSize) hoff' hwf' hb']
      · have hsf : t.IsStatic = false := by simp at hs; exact hs
        rw [readElem_partOf_dynamic t w hsf xs (ws.map (partOf t) ++ ys) rest off hoff hwf hb]
        rw [decode_encode_append t hv w hlw _
          (by
            have heq := drop_tail_partOf_dynamic t w hsf xs (ws.map (partOf t) ++ ys) rest
            rw [← heq, List.length_drop]
            omega)]
        have hoff' : off + t.headSize = headSizes (xs ++ [partOf t w]) := by
          rw [hoff, headSizes_append]
          simp only [headSizes, partOf_dynamic t w hsf, Part.headSize]
          rw [headSize_of_dynamic t hsf]
        rw [hre]
        rw [ih (ws.length) rfl hlsw (xs ++ [partOf t w]) (off + t.headSize) hoff' hwf' hb']
termination_by 8 * sizeOf t + 1

/-- Tuples decode from their own encoding inside a larger head/tail layout. -/
theorem decodeTuple_append : (ts : List Ty) → AllValid ts → (vs : TupleVal ts) →
    TupleLenBounds ts vs → (xs ys : List Part) → (off : Nat) → off = headSizes xs →
    (rest : List UInt8) → WF (xs ++ partsOfTuple ts vs ++ ys) →
    (encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest).length < 2 ^ 256 →
    decodeTuple ts (encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest) off = some vs
  | [], _, _, _, _, _, _, _, _, _, _ => by
      simp only [partsOfTuple, decodeTuple]
  | t :: ts, hv, (v, vs), hls, xs, ys, off, hoff, rest, hwf, hb => by
      obtain ⟨hvt, hvs⟩ := hv
      have hlc : LenBound t v ∧ TupleLenBounds ts vs := by simpa [TupleLenBounds] using hls
      obtain ⟨hlv, hlvs⟩ := hlc
      simp only [partsOfTuple] at hwf hb ⊢
      simp only [decodeTuple]
      simp only [List.append_assoc, List.cons_append] at hwf hb ⊢
      have hre : xs ++ (partOf t v :: (partsOfTuple ts vs ++ ys)) =
          ((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys := by
        simp [List.append_assoc]
      have hwf' : WF (((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys) := by
        rwa [← hre]
      have hb' : (encodeParts (((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys) ++ rest).length <
          2 ^ 256 := by
        rwa [← hre]
      by_cases hs : t.IsStatic
      · rw [readElem_static t _ _ hs]
        rw [drop_head_partOf_static t hs v xs (partsOfTuple ts vs ++ ys) rest off hoff]
        rw [decode_encode_append t hvt v hlv _
          (by
            have heq := drop_head_partOf_static t hs v xs (partsOfTuple ts vs ++ ys) rest off hoff
            rw [← heq, List.length_drop]
            omega)]
        have hoff' : off + t.headSize = headSizes (xs ++ [partOf t v]) := by
          rw [hoff, headSizes_append]
          simp only [headSizes, partOf_static t v hs, Part.headSize]
          rw [encode_length_static t hs hvt v]
          omega
        rw [hre]
        rw [decodeTuple_append ts hvs vs hlvs (xs ++ [partOf t v]) ys (off + t.headSize) hoff'
          rest hwf' hb']
        rfl
      · have hsf : t.IsStatic = false := by simp at hs; exact hs
        rw [readElem_partOf_dynamic t v hsf xs (partsOfTuple ts vs ++ ys) rest off hoff hwf hb]
        rw [decode_encode_append t hvt v hlv _
          (by
            have heq := drop_tail_partOf_dynamic t v hsf xs (partsOfTuple ts vs ++ ys) rest
            rw [← heq, List.length_drop]
            omega)]
        have hoff' : off + t.headSize = headSizes (xs ++ [partOf t v]) := by
          rw [hoff, headSizes_append]
          simp only [headSizes, partOf_dynamic t v hsf, Part.headSize]
          rw [headSize_of_dynamic t hsf]
        rw [hre]
        rw [decodeTuple_append ts hvs vs hlvs (xs ++ [partOf t v]) ys (off + t.headSize) hoff'
          rest hwf' hb']
        rfl
termination_by ts => 8 * sizeOf ts + 2
end

/-- **Unified roundtrip**: every value of a valid type decodes from its own
encoding, provided every length word stays below `2^256`. -/
theorem roundtrip (t : Ty) (hv : t.Valid) (v : t.Val) (hl : LenBound t v)
    (hb : (encode t v).length < 2 ^ 256) : decode t (encode t v) = some v := by
  have h := decode_encode_append t hv v hl [] (by rwa [List.append_nil])
  rwa [List.append_nil] at h

/-! ## Canonical decoding -/

/-- Prefix-canonical input for `t`: decoding succeeds and re-encoding matches
the consumed prefix (trailing bytes are ignored). -/
def IsCanonical (t : Ty) (buf : List UInt8) : Prop :=
  ∃ v : t.Val, decode t buf = some v ∧ buf.take (encode t v).length = encode t v

end EvmAbi
