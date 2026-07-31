import EvmAbi.Ty
import EvmAbi.Static
import EvmAbi.Dynamic
import EvmAbi.Align
import EvmAbi.Word
import EvmAbi.Parts

/-!
# EvmAbi.Codec

The full ABI codec (roadmap node 8): `encode : (t : Ty) → t.Val → List
UInt8` and the linear decoder `decode : (t : Ty) → List UInt8 → Option
(t.Val × List UInt8)`, built on the head/tail combinator of `EvmAbi.Parts`
and the dual-cursor `Get2` monad of `EvmAbi.Builder`.

Layout of the module:

* **encode family** — `encode` / `partOf` / `partsOfTuple` (mutual).  A
  component's `Part` is its inline encoding when static, or an empty head
  plus its encoding as tail when dynamic; `encodeParts` fills in the offset
  words.

* **length and alignment packages** — static encodings occupy exactly their
  `headSize`; every encoding is 32-byte aligned (`WF` of the part lists).

* **appended-buffer read lemmas** — the primitive decoders read through a
  suffix they do not care about; `drop_head_partOf_static`,
  `drop_tail_partOf_dynamic` and `natAt_offset_partOf_dynamic` locate a
  component's head and tail inside a larger head/tail layout.

* **the linear decoder** — `decode` and its `Get2` walkers (`decodeElem` /
  `decodeElems` / `decodeTuple`): two monotonic cursors (head section,
  tails) thread an *expected tail frontier*, and a dynamic component's
  offset word must equal it exactly.  `decode` is prefix-form: it returns
  the value together with the untouched remainder, so nested components are
  prefixes of their parent's buffer.  Its theorem families are the
  roundtrips (`decode_roundtrip`: every encoding decodes back), the
  soundness (`decode_sound`: the decoder only produces encodings), and the
  bound-free static delegation (`decode_static_append` — static types carry
  no offset words, so no `2^256` bound is needed).

* **strict API** — `decodeStrict` (exact consumption, no trailing
  garbage), `IsCanonical`, and the capstones `isCanonical_iff` /
  `decodeStrict_eq_some_iff`: canonical buffers are exactly the image of
  `encode`, with no bound conjunct anywhere (the dynamic payload bounds are
  intrinsic to `Ty.Val`).

The mutual blocks use explicit measures (`sizeOf` with constant offsets
distinguishing the sibling levels) so the default `decreasing_tactic`
discharges every goal.
-/

namespace EvmAbi

open Ty
open Binary
open Builder

/-! ## encode family -/

/- The encoder lives in builder form: `put` assembles a value with `O(1)`
sequencing, `partOf` views it as a head/tail `Part`, `partsOfTuple` maps a
tuple value to a list of parts.  The list form `encode` is the
materialization of `put` (`Builder.toList`), so every specification is
still stated about the byte list. -/

mutual
/-- ABI encoder, builder form: O(1) sequencing via `Builder`. -/
def put : (t : Ty) → t.Val → Builder
  | .uint _, ⟨n, _⟩   => putUint n
  | .int _,  ⟨i, _⟩   => putInt i
  | .bool,   b         => putBool b
  | .address, ⟨n, _⟩  => putAddress n
  | .bytesN _, ⟨bs, _⟩ => putBytesN bs
  | .bytes,   ⟨bs, _⟩  => putBytes bs
  | .string,  ⟨s, _⟩   => putString s
  | .array t, ⟨vs, _⟩  => putUint vs.length ++ putParts (vs.map (partOf t))
  | .fixedArray t _, ⟨vs, _⟩ => putParts (vs.map (partOf t))
  | .tuple ts, vs      => putParts (partsOfTuple ts vs)
termination_by t => (sizeOf t, 0)

/-- A value seen as a head/tail part: static values sit in the head,
dynamic values in the tail (their head is the offset word). -/
def partOf (t : Ty) (v : t.Val) : Part :=
  match t.IsStatic with
  | true => ⟨put t v, ∅, false⟩
  | false => ⟨∅, put t v, true⟩
termination_by (sizeOf t, 1)

/-- A tuple value seen as a list of parts. -/
def partsOfTuple : (ts : List Ty) → TupleVal ts → List Part
  | [], _ => []
  | t :: ts, (v, vs) => partOf t v :: partsOfTuple ts vs
termination_by ts => (sizeOf ts, 2)
end

/-- ABI encoder (type-indexed): the materialization of `put`. -/
def encode (t : Ty) (v : t.Val) : List UInt8 := (put t v).toList

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
    partOf t v = ⟨put t v, ∅, false⟩ := by
  simp [partOf, h]

/-- `partOf` of a dynamic value is the offset-word head plus tail part. -/
theorem partOf_dynamic (t : Ty) (v : t.Val) (h : t.IsStatic = false) :
    partOf t v = ⟨∅, put t v, true⟩ := by
  simp [partOf, h]

/-- A component contributes its part's tail to the tail section: nothing for
a static component (whose part has an empty tail), its encoding for a
dynamic one. -/
theorem encodeTails_cons_partOf (t : Ty) (v : t.Val) (ps : List Part) :
    encodeTails (partOf t v :: ps) = (partOf t v).tail.toList ++ encodeTails ps := by
  cases hs : t.IsStatic
  · rw [partOf_dynamic t v hs, encodeTails_cons_dynamic]
  · rw [partOf_static t v hs, encodeTails_cons_static]; simp [Builder.toList_empty]

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

/-- Every head slot is 32-byte aligned — a static one because its encoding
is, a dynamic one because it is a single offset word. -/
theorem dvd_headSize (t : Ty) : 32 ∣ t.headSize := by
  cases hs : t.IsStatic
  · rw [headSize_of_dynamic t hs]; exact ⟨1, rfl⟩
  · exact dvd_headSize_static t hs

mutual
/-- Static encodings occupy exactly their head size. -/
theorem encode_length_static : (t : Ty) → t.IsStatic = true → t.Valid → (v : t.Val) →
    (encode t v).length = t.headSize
  | uint _, _, _, ⟨n, _⟩ => by simp [encode, put, length_encodeUint, headSize]
  | int _, _, _, ⟨i, _⟩ => by
      simp only [encode, put]
      simp [encodeInt, length_encodeUint, headSize]
  | Ty.bool, _, _, b => by simp [encode, put, encodeBool, length_encodeUint, headSize]
  | address, _, _, ⟨n, _⟩ => by simp [encode, put, encodeAddress, length_encodeUint, headSize]
  | bytesN m, _, hv, ⟨bs, hbs⟩ => by
      obtain ⟨h1, h32⟩ := hv
      have hlen : (encodeBytesN bs).length = 32 := length_encodeBytesN (by omega)
      simp only [encode, put, toList_putBytesN]
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
              change (encode t w).length + headSizes (List.map (partOf t) ws) =
                (ws.length + 1) * t.headSize
              rw [ih1, encode_length_static t hst hvt w, Nat.add_mul, Nat.one_mul]
              omega
            · simp only [tailSizes, Part.tailSize, ih2]
      simp only [encode, put]
      rw [<- encodeParts, length_encodeParts, (hlen vs).1, (hlen vs).2, hvs, Nat.add_zero]
      simp only [headSize]
      rw [if_pos hst]
  | tuple ts, hs, hv, vs => by
      have hss : allStatic ts = true := by simp only [IsStatic] at hs; exact hs
      have hvts : AllValid ts := hv
      have hgoal : headSize (tuple ts) = headSizeSum ts := by
        simp only [headSize]
        rw [if_pos hss]
      rw [hgoal]
      simp only [encode, put]
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
      change (encode t v).length + headSizes (partsOfTuple ts vs) +
          (0 + tailSizes (partsOfTuple ts vs)) = t.headSize + headSizeSum ts
      rw [encode_length_static t hst hvt v]
      omega
termination_by ts => 2 * sizeOf ts + 1
end

/-- A component's part occupies exactly the component's head size: its own
encoding when static, one offset word when dynamic.  This is the single
static/dynamic split that the head-section lemmas all reduce to. -/
theorem headSize_partOf (t : Ty) (hv : t.Valid) (v : t.Val) :
    (partOf t v).headSize = t.headSize := by
  cases hs : t.IsStatic
  · rw [partOf_dynamic t v hs]
    exact (headSize_of_dynamic t hs).symm
  · rw [partOf_static t v hs, Part.headSize]
    exact encode_length_static t hs hv v

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
        obtain ⟨bs, _⟩ := v
        simp only [encode, put, toList_putBytes, encodeBytes, List.length_append, length_encodeUint]
        exact aligned_add (aligned_mul 1) (dvd_length_pad32 _)
    | string =>
        obtain ⟨s, _⟩ := v
        simp only [encode, put, toList_putString, encodeString, encodeBytes, List.length_append, length_encodeUint]
        exact aligned_add (aligned_mul 1) (dvd_length_pad32 _)
    | array t =>
        obtain ⟨vs, _⟩ := v
        have hvt : t.Valid := hv
        simp only [encode, put, toList_append, toList_putUint, List.length_append, length_encodeUint]
        exact aligned_add (aligned_mul 1) (dvd_length_encodeParts (wf_map_partOf t hvt vs))
    | fixedArray t n =>
        obtain ⟨vs, hvs⟩ := v
        have hvt : t.Valid := hv
        simp only [encode, put]
        exact dvd_length_encodeParts (wf_map_partOf t hvt vs)
    | tuple ts =>
        have hvts : AllValid ts := hv
        simp only [encode, put]
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
          · change 32 ∣ (encode t w).length
            rw [encode_length_static t hs hv w]; exact dvd_headSize_static t hs
          · exact ⟨0, rfl⟩
        · have hsf : t.IsStatic = false := by simp at hs; exact hs
          rw [partOf_dynamic t w hsf]
          constructor
          · exact ⟨0, rfl⟩
          · change 32 ∣ (encode t w).length
            simpa [Aligned] using encode_length_aligned t hv w
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
          · change 32 ∣ (encode t v).length
            rw [encode_length_static t hs hvt v]; exact dvd_headSize_static t hs
          · exact ⟨0, rfl⟩
        · have hsf : t.IsStatic = false := by simp at hs; exact hs
          rw [partOf_dynamic t v hsf]
          constructor
          · exact ⟨0, rfl⟩
          · change 32 ∣ (encode t v).length
            simpa [Aligned] using encode_length_aligned t hvt v
      · exact wf_partsOfTuple ts hvs vs
termination_by ts => 4 * sizeOf ts + 2
end

/-! ## Package C: appended-buffer read lemmas -/

/- Every primitive decoder reads through a suffix it does not care about;
`drop_head_partOf_static` locates a static part's head at its head offset.
The linear decoder's bound-free static roundtrip
(`decode_static_append` below) is the bound-free static roundtrip. -/

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
  obtain ⟨hlb, hub⟩ := intM_bounds_lt_255 (M := M) hM0 hM hl hu
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
  have hle : off ≤ (encodeParts (xs ++ ⟨put t v, ∅, false⟩ :: ys)).length := by
    rw [hoff, length_encodeParts, headSizes_append]
    omega
  rw [drop_append_of_le hle, hoff, drop_headOffset_static]
  simp only [List.append_assoc]
  rfl

/-- Extending the already-encoded head prefix by one component advances the
head offset by that component's head size — for static components because
their head *is* their encoding, for dynamic ones because it is an offset
word. -/
theorem headSizes_snoc_partOf (t : Ty) (hv : t.Valid) (v : t.Val) (xs : List Part)
    (off : Nat) (hoff : off = headSizes xs) :
    off + t.headSize = headSizes (xs ++ [partOf t v]) := by
  rw [hoff, headSizes_append]
  simp [headSizes, headSize_partOf t hv v]
/-! ## Package D: locating dynamic tails in the layout -/

/- Dynamic components sit in the tail and are reached through an offset word
in the head.  The lemmas below locate a dynamic part's tail inside a larger
head/tail layout (`drop_tail_partOf_dynamic`) and show its offset word reads
back the correct tail offset (`natAt_offset_partOf_dynamic`) — used by the
linear decoder's roundtrip (`decodeElem_roundtrip` below). -/

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
  rfl

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
      (encodeParts (xs ++ (⟨∅, put t v, true⟩ : Part) :: ys)).length := by
    have hd : 32 ∣ headSizes xs := dvd_headSizes fun q hq => hwf q (List.mem_append_left _ hq)
    rw [length_encodeParts, headSizes_append]
    simp only [headSizes, Part.headSize]
    omega
  rw [natAt_append_left _ _ _ hle32]
  simp only [natAt, wordAt_offset_append hwf, Option.map_some, UInt256.toNat_ofNat,
    Option.some.injEq]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle hb0)

/-! ## decoder helpers: sizes and word recovery -/

/-- The head section of an element list mapped through `partOf`, for
arbitrary (not only static) element types. -/
theorem headSizes_map_partOf_any (t : Ty) (hv : t.Valid) :
    (vs : List t.Val) → headSizes (vs.map (partOf t)) = vs.length * t.headSize
  | [] => by simp [headSizes]
  | v :: vs => by
      rw [List.map_cons]
      simp only [headSizes, headSize_partOf t hv v, List.length_cons]
      rw [headSizes_map_partOf_any t hv vs, Nat.succ_mul]
      omega

/-- The head section of a tuple part list, for arbitrary component types. -/
theorem headSizes_partsOfTuple_any : (ts : List Ty) → AllValid ts → (vs : TupleVal ts) →
    headSizes (partsOfTuple ts vs) = headSizeSum ts
  | [], _, _ => by simp [partsOfTuple, headSizes, headSizeSum]
  | t :: ts, hv, (v, vs) => by
      obtain ⟨hvt, hvs⟩ := hv
      simp only [partsOfTuple, headSizes, headSize_partOf t hvt v, headSizeSum]
      rw [headSizes_partsOfTuple_any ts hvs vs]


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

/- The soundness theorems in both directions need the inverse of the
appended-buffer read lemmas: a successful primitive decode pins the front
of the buffer to the encoding of the decoded value. -/

/- The soundness theorems in both directions (the linear-decoder soundness
below and the C3 soundness) need the inverse of the append roundtrips: a
successful primitive decode pins the front of the buffer to the encoding
of the decoded value. -/

/-- When `decodeUint` succeeds, the front word is the big-endian encoding
of the decoded value. -/
theorem buf_take_32_eq_encodeUint_of_decodeUint (buf : List UInt8) (x : Nat)
    (hdu : decodeUint buf = some x) : buf.take 32 = encodeUint x := by
  have h := take_32_eq_encodeUint_of_natAt buf 0 x hdu
  simpa using h

/-- The `int` decoder recovers the word it read. -/
theorem encodeInt_eq_encodeUint_of_decodeInt {buf : List UInt8} {i : Int} {x : Nat}
    (hdi : decodeInt buf = some i) (hdu : decodeUint buf = some x) :
    encodeInt i = encodeUint x := by
  have hx256 : x < 2 ^ 256 := natAt_lt hdu
  have hxi : (if x < 2 ^ 255 then (x : Int) else (x : Int) - 2 ^ 256) = i := by
    simpa [decodeInt, hdu] using hdi
  by_cases hx2 : x < 2 ^ 255
  · rw [if_pos hx2] at hxi
    subst hxi
    rw [encodeInt, if_pos (by omega)]
    rfl
  · rw [if_neg hx2] at hxi
    subst hxi
    rw [encodeInt, if_neg (by omega)]
    congr 1
    omega

/-- The `bool` decoder succeeds exactly on the canonical boolean words. -/
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

/-- A successful `decodeBytesN` pins the front word to the encoding. -/
theorem buf_take_32_eq_encodeBytesN_of_decodeBytesN {m : Nat} {buf bs : List UInt8}
    (h : decodeBytesN m buf = some bs) : buf.take 32 = encodeBytesN bs := by
  unfold decodeBytesN at h
  split at h
  · next hc =>
      rw [Option.some.injEq] at h
      have hlen : bs.length = m := by rw [← h]; exact hc.1
      rw [encodeBytesN, hlen, ← h, ← hc.2]
      exact (List.take_append_drop m (buf.take 32)).symm
  · contradiction

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


/-! ## the linear decoder -/

/- Canonical layouts are *sequential* — offset words must equal the
frontier, and tails follow the head contiguously — so the decoder is a
pure front-consumer: at the compound level two cursors (head section, tail
section) advance monotonically and every byte is touched at most once. -/

/-- Reading a word from a dropped buffer reads the original at a larger
index. -/
theorem wordAt_drop_add (buf : List UInt8) (i j : Nat) :
    wordAt (buf.drop (32 * j)) i = wordAt buf (i + j) := by
  unfold wordAt
  simp [List.drop_drop, Nat.mul_add, Nat.add_comm]

/-- `natAt` variant of `wordAt_drop_add`. -/
theorem natAt_drop_add (buf : List UInt8) (i j : Nat) :
    natAt (buf.drop (32 * j)) i = natAt buf (i + j) := by
  simp [natAt, wordAt_drop_add]

/-- `natAt` on the front of a dropped buffer reads the word at the drop
index. -/
theorem natAt_drop (buf : List UInt8) (off i : Nat) (h : off = 32 * i) :
    natAt (buf.drop off) 0 = natAt buf i := by
  rw [h]
  simpa using natAt_drop_add buf 0 i

mutual
/-- **Canonical decoder, prefix form**: reads one canonical value of type
`t` from the front of the buffer, returning it together with the untouched
remainder. -/
def decode : (t : Ty) → List UInt8 → Option (t.Val × List UInt8)
  | .uint m, buf => match decodeUint buf with
      | some n => if h : n < 2 ^ m then some (⟨n, h⟩, buf.drop 32) else none
      | none => none
  | .int m, buf => match decodeInt buf with
      | some i => if h : -((2 ^ (m - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m - 1) : Nat) : Int) then
          some (⟨i, h⟩, buf.drop 32)
        else none
      | none => none
  | .bool, buf => match decodeBool buf with
      | some b => some (b, buf.drop 32)
      | none => none
  | .address, buf => match decodeAddress buf with
      | some n => if h : n < 2 ^ 160 then some (⟨n, h⟩, buf.drop 32) else none
      | none => none
  | .bytesN m, buf => match decodeBytesN m buf with
      | some bs => if h : bs.length = m then some (⟨bs, h⟩, buf.drop 32) else none
      | none => none
  | .bytes, buf => match hp : decodeBytesPrefix buf with
      | some (bs, n) => some (⟨bs, length_lt_of_decodeBytesPrefix hp⟩, buf.drop n)
      | none => none
  | .string, buf => match hp : decodeBytesPrefix buf with
      | some (bs, n) => match hs : String.fromUTF8? bs.toByteArray with
          | some s => some (⟨s, size_toUTF8_lt_of_decodeBytesPrefix hp hs⟩, buf.drop n)
          | none => none
      | none => none
  | .array t, buf => match hk : natAt buf 0 with
      | none => none
      | some k => match (decodeElems t k).run (buf.drop 32) (buf.drop (32 + k * t.headSize)) (k * t.headSize) with
          | some (vs, _, rest, _) => some (⟨vs.val, by rw [vs.property]; exact natAt_lt hk⟩, rest)
          | none => none
  | .fixedArray t n, buf => match (decodeElems t n).run buf (buf.drop (n * t.headSize)) (n * t.headSize) with
      | some (vs, _, rest, _) => some (vs, rest)
      | none => none
  | .tuple ts, buf => match (decodeTuple ts).run buf (buf.drop (headSizeSum ts)) (headSizeSum ts) with
      | some (vs, _, rest, _) => some (vs, rest)
      | none => none
termination_by t => (sizeOf t, 0)

/-- Read one component at its head slot, as a `Get2` program: static
components decode in place from the head cursor; dynamic components must
have their offset word equal to the frontier `E` and decode from the tail
cursor. -/
def decodeElem (t : Ty) : Get2 t.Val := ⟨fun head tails E =>
  match t.IsStatic with
  | true => match decode t head with
      | some (v, rest) => some (v, rest, tails, E)
      | none => none
  | false => match natAt head 0 with
      | none => none
      | some o => if o = E then
          match decode t tails with
          | some (v, rest) => some (v, head.drop 32, rest, E + (tails.length - rest.length))
          | none => none
        else none⟩
termination_by (sizeOf t, 1)

/-- Read `k` consecutive canonical elements as a `Get2` program, walking
the head from the head cursor and the tails from the tail cursor. -/
def decodeElems (t : Ty) (k : Nat) : Get2 ({ vs : List t.Val // vs.length = k }) :=
  match k with
  | 0 => pure ⟨[], rfl⟩
  | k + 1 => do
      let v ← decodeElem t
      let ⟨vs, h⟩ ← decodeElems t k
      pure ⟨v :: vs, by simp [List.length_cons, h]⟩
termination_by (sizeOf t, k + 2)

/-- Read a canonical tuple as a `Get2` program, walking the head and
tails. -/
def decodeTuple : (ts : List Ty) → Get2 (TupleVal ts)
  | [] => pure ()
  | t :: ts => do
      let v ← decodeElem t
      let vs ← decodeTuple ts
      pure (v, vs)
termination_by ts => (sizeOf ts, 2)
end

/- ## static delegation: static types decode bound-free -/

/- Static types carry no offset words: the frontier never moves and the
tail cursor is never read, so the roundtrips hold without the `2^256`
bound that compound layouts need for their offset words.  This is what
`decodePacked` (`EvmAbi.Packed`) relies on. -/

/-- The tails of a static part list are empty. -/
theorem encodeTails_map_partOf_static (t : Ty) (hs : t.IsStatic = true) (vs : List t.Val) :
    encodeTails (vs.map (partOf t)) = [] := by
  induction vs with
  | nil => simp [encodeTails, putTails, Builder.toList_empty]
  | cons v vs ih =>
      rw [List.map_cons, partOf_static t v hs, encodeTails_cons_static, ih]

/-- The tails of an all-static tuple part list are empty. -/
theorem encodeTails_partsOfTuple_static : (ts : List Ty) → allStatic ts = true →
    (vs : TupleVal ts) → encodeTails (partsOfTuple ts vs) = []
  | [], _, _ => by simp [partsOfTuple, encodeTails, putTails, Builder.toList_empty]
  | t :: ts, hs, (v, vs) => by
      simp only [allStatic] at hs
      rw [Bool.and_eq_true] at hs
      obtain ⟨hst, hss⟩ := hs
      rw [partsOfTuple, partOf_static t v hst, encodeTails_cons_static,
        encodeTails_partsOfTuple_static ts hss vs]

mutual
/-- A static component's head slot reads back in place. -/
theorem decodeElem_static_append (t : Ty) (hs : t.IsStatic = true) (hv : t.Valid)
    (v : t.Val) (head tails : List UInt8) (E : Nat) :
    (decodeElem t).run (encode t v ++ head) tails E = some (v, head, tails, E) := by
  simp only [decodeElem, hs]
  rw [decode_static_append t hs hv v head]
termination_by 8 * sizeOf t + 1

/-- A run of static elements reads back from its flattened encodings,
leaving the suffix and the tail cursor untouched. -/
theorem decodeElems_static_append (t : Ty) (hs : t.IsStatic = true) (hv : t.Valid)
    (vs : List t.Val) (k : Nat) (hk : vs.length = k) (E : Nat) (head tails : List UInt8) :
    (decodeElems t k).run (encodeHeads E (vs.map (partOf t)) ++ head) tails E =
      some (⟨vs, hk⟩, head, tails, E) := by
  induction vs generalizing k with
  | nil =>
      subst hk
      simp [decodeElems, Get2.pure_run, encodeHeads, putHeads, Builder.toList_empty]
  | cons w ws ih =>
      have hk' : k = ws.length + 1 := by rw [← hk, List.length_cons]
      subst hk'
      simp only [List.map_cons, decodeElems, Get2.bind_run, Get2.pure_run]
      rw [partOf_static t w hs, encodeHeads_cons_static]
      rw [List.append_assoc]
      rw [show (put t w).toList = encode t w from rfl]
      rw [decodeElem_static_append t hs hv w (encodeHeads E (ws.map (partOf t)) ++ head) tails E]
      dsimp only []
      rw [ih ws.length rfl]
termination_by 8 * sizeOf t + 2

/-- An all-static tuple reads back from its flattened heads, leaving the
suffix and the tail cursor untouched. -/
theorem decodeTuple_static_append : (ts : List Ty) → allStatic ts = true → AllValid ts →
    (vs : TupleVal ts) → (E : Nat) → (head tails : List UInt8) →
    (decodeTuple ts).run (encodeHeads E (partsOfTuple ts vs) ++ head) tails E =
      some (vs, head, tails, E)
  | [], _, _, _, E, head, tails => by
      simp [decodeTuple, Get2.pure_run, partsOfTuple, encodeHeads, putHeads,
        Builder.toList_empty]
  | t :: ts, hs, hv, (v, vs), E, head, tails => by
      simp only [allStatic] at hs
      rw [Bool.and_eq_true] at hs
      obtain ⟨hst, hss⟩ := hs
      obtain ⟨hvt, hvs⟩ := hv
      simp only [decodeTuple, Get2.bind_run, Get2.pure_run]
      rw [partsOfTuple, partOf_static t v hst, encodeHeads_cons_static]
      rw [List.append_assoc]
      rw [show (put t v).toList = encode t v from rfl]
      rw [decodeElem_static_append t hst hvt v (encodeHeads E (partsOfTuple ts vs) ++ head) tails E]
      dsimp only []
      rw [decodeTuple_static_append ts hss hvs vs E head tails]
termination_by ts => 8 * sizeOf ts + 3

/-- **Static roundtrip, prefix form**: a static value reads back from the
front of its own encoding followed by an arbitrary suffix — bound-free,
since static types have no offset words. -/
theorem decode_static_append (t : Ty) (hs : t.IsStatic = true) (hv : t.Valid)
    (v : t.Val) (rest : List UInt8) :
    decode t (encode t v ++ rest) = some (v, rest) := by
  cases t with
  | uint m =>
      obtain ⟨n, hn⟩ := v
      have hdec : decodeUint (encodeUint n ++ rest) = some n :=
        decodeUint_append n rest
          (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (n := 2) (by decide) hv.2.1))
      simp only [encode, put, decode, toList_putUint]
      rw [hdec]
      exact dif_pos hn
  | int m =>
      obtain ⟨i, hi⟩ := v
      have h0 : 0 < m := by have h8 := hv.1; omega
      have hdec : decodeInt (encodeInt i ++ rest) = some i :=
        decodeInt_append h0 hv.2.1 hi.1 hi.2 rest
      simp only [encode, put, decode, toList_putInt]
      rw [hdec]
      exact dif_pos hi
  | bool =>
      simp only [encode, put, decode, toList_putBool]
      rw [decodeBool_append v rest]
      rfl
  | address =>
      obtain ⟨n, hn⟩ := v
      have hdec : decodeAddress (encodeAddress n ++ rest) = some n :=
        decodeAddress_append n rest hn
      simp only [encode, put, decode, toList_putAddress]
      rw [hdec]
      exact dif_pos hn
  | bytesN m =>
      obtain ⟨bs, hbs⟩ := v
      have hdec : decodeBytesN m (encodeBytesN bs ++ rest) = some bs :=
        decodeBytesN_append hv.2 hbs rest
      have hlen : (encodeBytesN bs).length = 32 :=
        length_encodeBytesN (by rw [hbs]; exact hv.2)
      simp only [encode, put, decode, toList_putBytesN]
      rw [hdec]
      dsimp only []
      rw [dif_pos hbs]
      rw [show (encodeBytesN bs ++ rest).drop 32 = rest from drop_append_of_length hlen]
  | bytes => simp [IsStatic] at hs
  | string => simp [IsStatic] at hs
  | array t => simp [IsStatic] at hs
  | fixedArray t n =>
      obtain ⟨vs, hvs⟩ := v
      have hst : t.IsStatic = true := by simpa [IsStatic] using hs
      have hvt : t.Valid := hv
      have hlen : headSizes (vs.map (partOf t)) = n * t.headSize := by
        rw [headSizes_map_partOf_any t hvt vs, hvs]
      have hbuf : encodeParts (vs.map (partOf t)) ++ rest =
          encodeHeads (n * t.headSize) (vs.map (partOf t)) ++ rest := by
        rw [encodeParts_unfold, hlen, encodeTails_map_partOf_static t hst vs]
        simp
      have hdr : (encodeHeads (n * t.headSize) (vs.map (partOf t)) ++ rest).drop
          (n * t.headSize) = rest := by
        rw [drop_append_of_length (by rw [length_encodeHeads, hlen])]
      simp only [encode, put, decode]
      rw [← encodeParts, hbuf, hdr,
        decodeElems_static_append t hst hvt vs n hvs (n * t.headSize) rest rest]
  | tuple ts =>
      have hss : allStatic ts = true := by simpa [IsStatic] using hs
      have hvts : AllValid ts := hv
      have hlen : headSizes (partsOfTuple ts v) = headSizeSum ts :=
        headSizes_partsOfTuple_any ts hvts v
      have hbuf : encodeParts (partsOfTuple ts v) ++ rest =
          encodeHeads (headSizeSum ts) (partsOfTuple ts v) ++ rest := by
        rw [encodeParts_unfold, hlen, encodeTails_partsOfTuple_static ts hss v]
        simp
      have hdr : (encodeHeads (headSizeSum ts) (partsOfTuple ts v) ++ rest).drop
          (headSizeSum ts) = rest := by
        rw [drop_append_of_length (by rw [length_encodeHeads, hlen])]
      simp only [encode, put, decode]
      rw [← encodeParts, hbuf, hdr,
        decodeTuple_static_append ts hss hvts v (headSizeSum ts) rest rest]
termination_by 8 * sizeOf t
end

/-- The tail size of a static component's part is zero. -/
theorem tailSize_partOf_static (t : Ty) (v : t.Val) (h : t.IsStatic = true) :
    (partOf t v).tailSize = 0 := by
  rw [partOf_static t v h]
  rfl

/-- The tail size of a dynamic component's part is its encoding length. -/
theorem tailSize_partOf_dynamic (t : Ty) (v : t.Val) (h : t.IsStatic = false) :
    (partOf t v).tailSize = (encode t v).length := by
  rw [partOf_dynamic t v h, Part.tailSize]
  rfl

/-- The frontier invariant is preserved by extending the head prefix: a part
advances the expected tail position by its own tail size — zero for a static
component, its encoding length for a dynamic one. -/
theorem tailOffset_snoc (p : Part) (xs zs : List Part) (E : Nat)
    (hE : E = tailOffset (xs ++ p :: zs) xs.length) :
    E + p.tailSize = tailOffset (xs ++ p :: zs) (xs ++ [p]).length := by
  have hll : (xs ++ [p]).length = xs.length + 1 := by simp [List.length_append]
  rw [hll]
  have h_succ : tailOffset (xs ++ p :: zs) (xs.length + 1) =
      tailOffset (xs ++ p :: zs) xs.length + p.tailSize := by
    rw [tailOffset, tailOffset, take_append_of_length rfl]
    have htake : (xs ++ p :: zs).take (xs.length + 1) = xs ++ [p] := by
      simp [List.take_append, List.take_of_length_le (Nat.le_succ _)]
    rw [htake, tailSizes_append]
    simp [tailSizes]
    omega
  rw [h_succ, hE]

/- ## roundtrip: the linear decoder recovers encodings -/

/- The frontier check is *free* on encodings: the offset word written by
`putParts` for a dynamic component is exactly the frontier, by the offset
correctness theorems of `EvmAbi.Parts`. -/
/-- `decode` at `bytes` through a known prefix-decode result. -/
theorem decode_bytes_pos {buf bs : List UInt8} {n : Nat}
    (hp : decodeBytesPrefix buf = some (bs, n)) :
    decode .bytes buf = some (⟨bs, length_lt_of_decodeBytesPrefix hp⟩, buf.drop n) := by
  simp only [decode]
  split
  · next bs' n' hp' =>
      rw [hp] at hp'
      simp only [Option.some.injEq, Prod.mk.injEq] at hp'
      obtain ⟨rfl, rfl⟩ := hp'
      rfl
  · next hp' => rw [hp] at hp'; contradiction

/-- `decode` at `string` through known prefix-decode and UTF-8
results. -/
theorem decode_string_pos {buf bs : List UInt8} {n : Nat} {s : String}
    (hp : decodeBytesPrefix buf = some (bs, n))
    (hs : String.fromUTF8? bs.toByteArray = some s) :
    decode .string buf = some (⟨s, size_toUTF8_lt_of_decodeBytesPrefix hp hs⟩, buf.drop n) := by
  simp only [decode]
  split
  · next bs' n' hp' =>
      rw [hp] at hp'
      simp only [Option.some.injEq, Prod.mk.injEq] at hp'
      obtain ⟨rfl, rfl⟩ := hp'
      split
      · next s' hs' =>
          rw [hs] at hs'
          obtain rfl := Option.some.inj hs'
          rfl
      · next hs' => rw [hs] at hs'; contradiction
  · next hp' => rw [hp] at hp'; contradiction

mutual
/-- **Roundtrip, per-component**: one canonical component reads back from
its head slot — static in place, dynamic through its offset word (which the
frontier check `offset = E` verifies) — and the frontier advances by the
component's tail size. -/
theorem decodeElem_roundtrip (t : Ty) (hv : t.Valid) (v : t.Val)
    (xs zs : List Part) (off : Nat) (hoff : off = headSizes xs)
    (E : Nat) (hE : E = tailOffset (xs ++ partOf t v :: zs) xs.length)
    (rest : List UInt8)
    (hwf : WF (xs ++ partOf t v :: zs))
    (hb : (encodeParts (xs ++ partOf t v :: zs) ++ rest).length < 2 ^ 256) :
    (decodeElem t).run
      ((encodeParts (xs ++ partOf t v :: zs) ++ rest).drop off)
      ((encodeParts (xs ++ partOf t v :: zs) ++ rest).drop E) E =
    some (v, (encodeParts (xs ++ partOf t v :: zs) ++ rest).drop (off + t.headSize),
          (encodeParts (xs ++ partOf t v :: zs) ++ rest).drop (E + (partOf t v).tailSize),
          E + (partOf t v).tailSize) := by
  cases hs : t.IsStatic
  · have hsf : t.IsStatic = false := hs
    have hhead32 : t.headSize = 32 := headSize_of_dynamic t hsf
    have htailLen : (partOf t v).tailSize = (encode t v).length := tailSize_partOf_dynamic t v hs
    have hnat0 := natAt_offset_partOf_dynamic t v hsf xs zs rest hwf hb
    have hnat : natAt ((encodeParts (xs ++ partOf t v :: zs) ++ rest).drop off) 0 = some E := by
      have hd : 32 ∣ headSizes xs := dvd_headSizes (fun q hq => hwf q (List.mem_append_left _ hq))
      have hoff32 : headSizes xs = 32 * (headSizes xs / 32) := by
        simpa [Nat.mul_comm] using (Nat.div_mul_cancel hd).symm
      rw [hoff, natAt_drop _ _ _ hoff32, hnat0, hE]
    have hdropTail := drop_tail_partOf_dynamic t v hsf xs zs rest
    have hb' : (encode t v ++ (encodeTails zs ++ rest)).length < 2 ^ 256 := by
      rw [← hdropTail, ← hE]
      rw [List.length_drop]
      omega
    have hr := decode_roundtrip t hv v (encodeTails zs ++ rest) hb'
    unfold decodeElem
    simp only [hs]
    rw [hnat]
    dsimp only []
    simp only [if_true]
    rw [show (encodeParts (xs ++ partOf t v :: zs) ++ rest).drop E =
        encode t v ++ (encodeTails zs ++ rest) from by rw [hE, hdropTail]]
    rw [hr]
    dsimp only []
    rw [htailLen]
    have htlen' : (encode t v ++ (encodeTails zs ++ rest)).length -
        (encodeTails zs ++ rest).length = (encode t v).length := by
      rw [List.length_append, Nat.add_sub_cancel]
    rw [← List.drop_drop, ← hhead32, htlen']
    rw [show (encodeParts (xs ++ partOf t v :: zs) ++ rest).drop (E + (encode t v).length) =
        encodeTails zs ++ rest from by
      rw [hE, ← List.drop_drop, hdropTail]
      exact drop_append_of_length rfl]
  · have hstatic := drop_head_partOf_static t hs v xs zs rest off hoff
    have hlen : (encode t v).length = t.headSize := encode_length_static t hs hv v
    have htail0 : (partOf t v).tailSize = 0 := tailSize_partOf_static t v hs
    have hb' : (encode t v ++ (encodeHeads (headSizes (xs ++ partOf t v :: zs) + tailSizes xs) zs ++
        (encodeTails (xs ++ partOf t v :: zs) ++ rest))).length < 2 ^ 256 := by
      rw [← hstatic]
      rw [List.length_drop]
      omega
    have hr := decode_roundtrip t hv v
      (encodeHeads (headSizes (xs ++ partOf t v :: zs) + tailSizes xs) zs ++
        (encodeTails (xs ++ partOf t v :: zs) ++ rest)) hb'
    simp only [decodeElem, hs]
    rw [hstatic, hr, htail0]
    dsimp only []
    simp only [Nat.add_zero]
    congr 1
    rw [← List.drop_drop, hstatic, drop_append_of_length hlen]
termination_by 8 * sizeOf t + 1

/-- **Roundtrip, element lists**: a run of canonical elements reads back
from their own head/tail layout, the frontier advancing exactly along the
tails. -/
theorem decodeElems_roundtrip (t : Ty) (hv : t.Valid) (vs : List t.Val) (k : Nat)
    (hk : vs.length = k)
    (xs ys : List Part) (off : Nat) (hoff : off = headSizes xs)
    (E : Nat) (hE : E = tailOffset (xs ++ vs.map (partOf t) ++ ys) xs.length)
    (rest : List UInt8)
    (hwf : WF (xs ++ vs.map (partOf t) ++ ys))
    (hb : (encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest).length < 2 ^ 256) :
    (decodeElems t k).run
      ((encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest).drop off)
      ((encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest).drop E) E =
    some (⟨vs, hk⟩,
      (encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest).drop (off + k * t.headSize),
      (encodeParts (xs ++ vs.map (partOf t) ++ ys) ++ rest).drop (E + tailSizes (vs.map (partOf t))),
      E + tailSizes (vs.map (partOf t))) := by
  induction vs generalizing k xs off E with
  | nil =>
      subst hk
      simp only [List.map_nil, List.length_nil, decodeElems, Get2.pure_run, tailSizes,
        Nat.add_zero, Nat.zero_mul]
  | cons w ws ih =>
      have hk' : k = ws.length + 1 := by rw [← hk, List.length_cons]
      subst hk'
      simp only [List.map_cons, decodeElems, Get2.bind_run, Get2.pure_run]
      simp only [List.map_cons] at hwf hb hE
      simp only [List.append_assoc, List.cons_append] at hwf hb hE ⊢
      have hre : xs ++ (partOf t w :: (ws.map (partOf t) ++ ys)) =
          ((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys := by
        simp [List.append_assoc]
      have hwf' : WF (((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys) := by
        rwa [← hre]
      have hb' : (encodeParts (((xs ++ [partOf t w]) ++ ws.map (partOf t)) ++ ys) ++ rest).length <
          2 ^ 256 := by
        rwa [← hre]
      have hoff' : off + t.headSize = headSizes (xs ++ [partOf t w]) := by
        rw [headSizes_snoc_partOf t hv w xs off hoff]
      have hE' : E + (partOf t w).tailSize =
          tailOffset ((xs ++ [partOf t w]) ++ ws.map (partOf t) ++ ys)
            (xs ++ [partOf t w]).length := by
        rw [← hre]
        rw [tailOffset_snoc (partOf t w) xs (ws.map (partOf t) ++ ys) E hE]
      have helem := decodeElem_roundtrip t hv w xs (ws.map (partOf t) ++ ys) off hoff E hE rest hwf hb
      rw [helem]
      dsimp only []
      rw [hre,
        ih (ws.length) rfl (xs ++ [partOf t w]) (off + t.headSize) hoff'
          (E + (partOf t w).tailSize) hE' hwf' hb']
      dsimp only []
      simp only [Option.some.injEq]
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Prod.ext
        · rw [show off + t.headSize + ws.length * t.headSize =
              off + (ws.length + 1) * t.headSize from by
            rw [Nat.add_mul, Nat.one_mul]
            ac_rfl]
        · apply Prod.ext
          · rw [show E + (partOf t w).tailSize + tailSizes (List.map (partOf t) ws) =
                E + tailSizes (partOf t w :: List.map (partOf t) ws) from by
              simp [tailSizes, Nat.add_assoc]]
          · rw [show E + (partOf t w).tailSize + tailSizes (List.map (partOf t) ws) =
                E + tailSizes (partOf t w :: List.map (partOf t) ws) from by
              simp [tailSizes, Nat.add_assoc]]
termination_by 8 * sizeOf t + 2

/-- **Roundtrip, tuples**: a canonical tuple reads back from its own
head/tail layout. -/
theorem decodeTuple_roundtrip : (ts : List Ty) → AllValid ts → (vs : TupleVal ts) →
    (xs ys : List Part) → (off : Nat) → off = headSizes xs →
    (E : Nat) → E = tailOffset (xs ++ partsOfTuple ts vs ++ ys) xs.length →
    (rest : List UInt8) → WF (xs ++ partsOfTuple ts vs ++ ys) →
    (encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest).length < 2 ^ 256 →
    (decodeTuple ts).run
      ((encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest).drop off)
      ((encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest).drop E) E =
    some (vs,
      (encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest).drop (off + headSizeSum ts),
      (encodeParts (xs ++ partsOfTuple ts vs ++ ys) ++ rest).drop (E + tailSizes (partsOfTuple ts vs)),
      E + tailSizes (partsOfTuple ts vs))
  | [], _, _, _, _, _, _, _, _, _, _, _ => by
      simp only [partsOfTuple, decodeTuple, Get2.pure_run, tailSizes, Nat.add_zero]
      rfl
  | t :: ts, hv, (v, vs), xs, ys, off, hoff, E, hE, rest, hwf, hb => by
      obtain ⟨hvt, hvs⟩ := hv
      simp only [partsOfTuple, decodeTuple, Get2.bind_run, Get2.pure_run]
      simp only [partsOfTuple] at hwf hb hE
      simp only [List.append_assoc, List.cons_append] at hwf hb hE ⊢
      have hre : xs ++ (partOf t v :: (partsOfTuple ts vs ++ ys)) =
          ((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys := by
        simp [List.append_assoc]
      have hwf' : WF (((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys) := by
        rwa [← hre]
      have hb' : (encodeParts (((xs ++ [partOf t v]) ++ partsOfTuple ts vs) ++ ys) ++ rest).length <
          2 ^ 256 := by
        rwa [← hre]
      have hoff' : off + t.headSize = headSizes (xs ++ [partOf t v]) := by
        rw [headSizes_snoc_partOf t hvt v xs off hoff]
      have hE' : E + (partOf t v).tailSize =
          tailOffset ((xs ++ [partOf t v]) ++ partsOfTuple ts vs ++ ys)
            (xs ++ [partOf t v]).length := by
        rw [← hre]
        rw [tailOffset_snoc (partOf t v) xs (partsOfTuple ts vs ++ ys) E hE]
      have helem := decodeElem_roundtrip t hvt v xs (partsOfTuple ts vs ++ ys) off hoff E hE rest hwf hb
      rw [helem]
      dsimp only []
      rw [hre,
        decodeTuple_roundtrip ts hvs vs (xs ++ [partOf t v]) ys (off + t.headSize) hoff'
          (E + (partOf t v).tailSize) hE' rest hwf' hb']
      dsimp only []
      simp only [tailSizes, Nat.add_assoc]
      rfl
termination_by ts => 8 * sizeOf ts + 3

/-- **Roundtrip, prefix form**: every value of a valid type reads back
canonically from the front of its own encoding, leaving the suffix
touched.  `hb` bounds the whole buffer (so no offset word wraps); the
dynamic payload bounds are intrinsic to `Val`. -/
theorem decode_roundtrip (t : Ty) (hv : t.Valid) (v : t.Val)
    (rest : List UInt8) (hb : (encode t v ++ rest).length < 2 ^ 256) :
    decode t (encode t v ++ rest) = some (v, rest) := by
  cases t with
  | uint m =>
      obtain ⟨n, hn⟩ := v
      have hdec : decodeUint (encodeUint n ++ rest) = some n :=
        decodeUint_append n rest
          (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (n := 2) (by decide) hv.2.1))
      simp only [encode, put, decode, toList_putUint]
      rw [hdec]
      dsimp only []
      rw [dif_pos hn]
      simp [length_encodeUint]
  | int m =>
      obtain ⟨i, hi⟩ := v
      have h0 : 0 < m := by have h8 := hv.1; omega
      have hdec : decodeInt (encodeInt i ++ rest) = some i :=
        decodeInt_append h0 hv.2.1 hi.1 hi.2 rest
      simp only [encode, put, decode, toList_putInt]
      rw [hdec]
      dsimp only []
      rw [dif_pos hi]
      simp [encodeInt, length_encodeUint]
  | bool =>
      simp only [encode, put, decode, toList_putBool]
      rw [decodeBool_append v rest]
      simp [encodeBool, length_encodeUint]
  | address =>
      obtain ⟨n, hn⟩ := v
      have hdec : decodeAddress (encodeAddress n ++ rest) = some n :=
        decodeAddress_append n rest hn
      simp only [encode, put, decode, toList_putAddress]
      rw [hdec]
      dsimp only []
      rw [dif_pos hn]
      simp [encodeAddress, length_encodeUint]
  | bytesN m =>
      obtain ⟨bs, hbs⟩ := v
      have hdec : decodeBytesN m (encodeBytesN bs ++ rest) = some bs :=
        decodeBytesN_append hv.2 hbs rest
      have hlen : (encodeBytesN bs).length = 32 :=
        length_encodeBytesN (by rw [hbs]; exact hv.2)
      simp only [encode, put, decode, toList_putBytesN]
      rw [hdec]
      dsimp only []
      rw [dif_pos hbs]
      rw [show (encodeBytesN bs ++ rest).drop 32 = rest from drop_append_of_length hlen]
  | bytes =>
      obtain ⟨bs, hlb⟩ := v
      have hr := decodeBytesPrefix_append (bs := bs) (rest := rest) hlb
      simp only [encode, put, toList_putBytes]
      rw [decode_bytes_pos hr]
      rw [drop_append_of_length rfl]
  | string =>
      obtain ⟨s, hlb⟩ := v
      have hb2 : s.toUTF8.data.toList.length < 2 ^ 256 := by
        rw [← Binary.ByteArray.size_eq_toList_length s.toUTF8]
        exact hlb
      have hr := decodeBytesPrefix_append (bs := s.toUTF8.data.toList) (rest := rest) hb2
      have hus : String.fromUTF8? (s.toUTF8.data.toList).toByteArray = some s := by
        rw [dataToList_toByteArray]
        exact fromUTF8?_toUTF8 s
      simp only [encode, put, toList_putString, encodeString]
      rw [decode_string_pos hr hus]
      rw [drop_append_of_length rfl]
  | array t =>
      obtain ⟨vs, hlk⟩ := v
      have hvt : t.Valid := hv
      have hbT : (encodeParts (vs.map (partOf t)) ++ rest).length < 2 ^ 256 := by
        have hb' := hb
        simp only [encode, put, toList_append, toList_putUint, List.length_append,
          length_encodeUint] at hb'
        simp only [encodeParts, List.length_append]
        omega
      have hlenH : headSizes (vs.map (partOf t)) = vs.length * t.headSize := by
        rw [headSizes_map_partOf_any t hvt vs]
      have hE : vs.length * t.headSize = tailOffset ([] ++ vs.map (partOf t) ++ []) 0 := by
        simp [tailOffset, tailSizes, hlenH]
      have hwalk := decodeElems_roundtrip t hvt vs vs.length rfl [] [] 0 (by simp [headSizes])
        (vs.length * t.headSize) hE rest (by simpa using wf_map_partOf t hvt vs) (by simpa using hbT)
      simp only [List.nil_append, List.append_nil, List.drop_zero] at hwalk
      have hheads : (encodeParts (vs.map (partOf t)) ++ rest).drop (vs.length * t.headSize) =
          encodeTails (vs.map (partOf t)) ++ rest := by
        rw [encodeParts_unfold, List.append_assoc, ← hlenH,
          drop_append_of_length (length_encodeHeads _ _)]
      have htails : (encodeParts (vs.map (partOf t)) ++ rest).drop
          (vs.length * t.headSize + tailSizes (vs.map (partOf t))) = rest := by
        rw [encodeParts_unfold, ← List.drop_drop, List.append_assoc, ← hlenH]
        rw [drop_append_of_length (length_encodeHeads _ _)]
        rw [drop_append_of_length (length_encodeTails _)]
      have hcnt : natAt (encodeUint vs.length ++ (encodeParts (vs.map (partOf t)) ++ rest)) 0 =
          some vs.length := by
        unfold encodeUint
        have hw := natAt_append ([] : List UInt8) (encodeParts (vs.map (partOf t)) ++ rest)
          (UInt256.ofNat vs.length) 0 (by simp)
        rw [List.nil_append] at hw
        rw [hw, UInt256.toNat_ofNat, Nat.mod_eq_of_lt
          (show vs.length < UInt256.size from hlk)]
      simp only [encode, put, decode, toList_append, toList_putUint, List.append_assoc]
      rw [← encodeParts]
      split
      · next hk' => rw [hcnt] at hk'; contradiction
      · next k hk' =>
          rw [hcnt] at hk'
          obtain rfl := Option.some.inj hk'
          rw [← List.drop_drop]
          rw [show (encodeUint vs.length ++ (encodeParts (vs.map (partOf t)) ++ rest)).drop 32 =
              encodeParts (vs.map (partOf t)) ++ rest from drop_append_of_length (length_encodeUint _)]
          rw [hwalk]
          dsimp only []
          rw [htails]
  | fixedArray t n =>
      obtain ⟨vs, hvs⟩ := v
      have hvt : t.Valid := hv
      have hbT : (encodeParts (vs.map (partOf t)) ++ rest).length < 2 ^ 256 := by
        have hb' := hb
        simp only [encode, put, List.length_append] at hb'
        simp only [encodeParts, List.length_append]
        omega
      have hlenH : headSizes (vs.map (partOf t)) = n * t.headSize := by
        rw [headSizes_map_partOf_any t hvt vs, hvs]
      have hE : n * t.headSize = tailOffset ([] ++ vs.map (partOf t) ++ []) 0 := by
        simp [tailOffset, tailSizes, hlenH]
      have hwalk := decodeElems_roundtrip t hvt vs n hvs [] [] 0 (by simp [headSizes])
        (n * t.headSize) hE rest (by simpa using wf_map_partOf t hvt vs) (by simpa using hbT)
      simp only [List.nil_append, List.append_nil, List.drop_zero] at hwalk
      have hheads : (encodeParts (vs.map (partOf t)) ++ rest).drop (n * t.headSize) =
          encodeTails (vs.map (partOf t)) ++ rest := by
        rw [encodeParts_unfold, List.append_assoc, ← hlenH,
          drop_append_of_length (length_encodeHeads _ _)]
      have htails : (encodeParts (vs.map (partOf t)) ++ rest).drop
          (n * t.headSize + tailSizes (vs.map (partOf t))) = rest := by
        rw [encodeParts_unfold, ← List.drop_drop, List.append_assoc, ← hlenH]
        rw [drop_append_of_length (length_encodeHeads _ _)]
        rw [drop_append_of_length (length_encodeTails _)]
      simp only [encode, put, decode]
      rw [← encodeParts]
      rw [hwalk]
      dsimp only []
      rw [htails]
  | tuple ts =>
      have hvts : AllValid ts := hv
      have hbT : (encodeParts (partsOfTuple ts v) ++ rest).length < 2 ^ 256 := by
        have hb' := hb
        simp only [encode, put, List.length_append] at hb'
        simp only [encodeParts, List.length_append]
        omega
      have hlenH : headSizes (partsOfTuple ts v) = headSizeSum ts := by
        rw [headSizes_partsOfTuple_any ts hvts v]
      have hE : headSizeSum ts = tailOffset ([] ++ partsOfTuple ts v ++ []) 0 := by
        simp [tailOffset, tailSizes, ← hlenH]
      have hwalk := decodeTuple_roundtrip ts hvts v [] [] 0 (by simp [headSizes])
        (headSizeSum ts) hE rest (by simpa using wf_partsOfTuple ts hvts v) (by simpa using hbT)
      simp only [List.nil_append, List.append_nil, List.drop_zero] at hwalk
      have hheads : (encodeParts (partsOfTuple ts v) ++ rest).drop (headSizeSum ts) =
          encodeTails (partsOfTuple ts v) ++ rest := by
        rw [encodeParts_unfold, List.append_assoc, ← hlenH,
          drop_append_of_length (length_encodeHeads _ _)]
      have htails : (encodeParts (partsOfTuple ts v) ++ rest).drop
          (headSizeSum ts + tailSizes (partsOfTuple ts v)) = rest := by
        rw [encodeParts_unfold, ← List.drop_drop, List.append_assoc, ← hlenH]
        rw [drop_append_of_length (length_encodeHeads _ _)]
        rw [drop_append_of_length (length_encodeTails _)]
      simp only [encode, put, decode]
      rw [← encodeParts]
      rw [hwalk]
      dsimp only []
      rw [htails]
termination_by 8 * sizeOf t
end

/-! ## soundness: the linear decoder only produces encodings -/

/- The mirror of the roundtrips: whenever the linear decoder succeeds, the
consumed front of the buffer is exactly the encoding of the decoded value.
This is what makes `decodeStrict` -- the decoder plus an
exact-consumption check -- the strict counterpart of `encode`.

The section is layered like the roundtrip section:

* **word atoms** -- one lemma per constructor.  Each unpacks the single
  `decode` step, projects the pair, and recombines the buffer with
  `List.take_append_drop`; the `int`/`bool`/`bytesN` arms reuse the
  word-recovery lemmas of the helper section.
* **walkers** -- `decodeElem_sound_static`/`_dynamic` pin one
  component's head slot to the encoding and its frontier slice to the
  tail; the element-list and tuple walkers thread them through a run of
  parts; the prefix form `decode_sound` assembles the atoms and
  walkers. -/

/-- `decodeElem` of a static type reads in place and keeps the
frontier. -/
theorem decodeElem_static (t : Ty) (head tails : List UInt8) (E : Nat)
    (h : t.IsStatic = true) :
    (decodeElem t).run head tails E = (match decode t head with
      | some (v, rest) => some (v, rest, tails, E)
      | none => none) := by
  simp [decodeElem, h]

/-- `decodeElem` of a dynamic type checks the offset word against
the frontier. -/
theorem decodeElem_dynamic (t : Ty) (head tails : List UInt8) (E : Nat)
    (h : t.IsStatic = false) :
    (decodeElem t).run head tails E = (match natAt head 0 with
      | none => none
      | some o => if o = E then
          match decode t tails with
          | some (v, rest) => some (v, head.drop 32, rest, E + (tails.length - rest.length))
          | none => none
        else none) := by
  simp [decodeElem, h]

/- ### word atoms -/

/-- `decode` at `uint` reads a canonical `uint` word. -/
theorem decode_uint_sound (m : Nat) (v : Ty.Val (.uint m)) (buf rest : List UInt8)
    (h : decode (.uint m) buf = some (v, rest)) :
    encode (.uint m) v ++ rest = buf := by
  obtain ⟨n, hn⟩ := v
  simp only [decode] at h
  cases hdu : decodeUint buf with
  | none => simp only [hdu] at h; contradiction
  | some x =>
      simp only [hdu] at h
      by_cases hx : x < 2 ^ m
      · rw [dif_pos hx] at h
        have hpair := Option.some.inj h
        have hxn : x = n := congrArg (fun p => p.1.val) hpair
        have hrest : buf.drop 32 = rest := congrArg (fun p => p.2) hpair
        subst hxn
        simp only [encode, put, toList_putUint]
        rw [← hrest, ← buf_take_32_eq_encodeUint_of_decodeUint buf x hdu,
          List.take_append_drop 32 buf]
      · rw [dif_neg hx] at h; contradiction

/-- `decode` at `int` reads a canonical `int` word. -/
theorem decode_int_sound (m : Nat) (v : Ty.Val (.int m)) (buf rest : List UInt8)
    (h : decode (.int m) buf = some (v, rest)) :
    encode (.int m) v ++ rest = buf := by
  obtain ⟨i, hi⟩ := v
  simp only [decode] at h
  cases hdi : decodeInt buf with
  | none => simp only [hdi] at h; contradiction
  | some x =>
      simp only [hdi] at h
      by_cases hx : -((2 ^ (m - 1) : Nat) : Int) ≤ x ∧ x < ((2 ^ (m - 1) : Nat) : Int)
      · rw [dif_pos hx] at h
        have hpair := Option.some.inj h
        have hxi : x = i := congrArg (fun p => p.1.val) hpair
        have hrest : buf.drop 32 = rest := congrArg (fun p => p.2) hpair
        subst hxi
        have hword : ∃ w, decodeUint buf = some w ∧ encodeInt x = encodeUint w := by
          cases hdw : decodeUint buf with
          | none => simp only [decodeInt, hdw] at hdi; contradiction
          | some w => exact ⟨w, rfl, encodeInt_eq_encodeUint_of_decodeInt hdi hdw⟩
        obtain ⟨w, hdw, henc⟩ := hword
        simp only [encode, put, toList_putInt]
        rw [henc, ← hrest, ← buf_take_32_eq_encodeUint_of_decodeUint buf w hdw,
          List.take_append_drop 32 buf]
      · rw [dif_neg hx] at h; contradiction

/-- `decode` at `bool` reads a canonical `bool` word. -/
theorem decode_bool_sound (v : Ty.Val .bool) (buf rest : List UInt8)
    (h : decode .bool buf = some (v, rest)) : encode .bool v ++ rest = buf := by
  simp only [decode] at h
  cases hdb : decodeBool buf with
  | none => simp only [hdb] at h; contradiction
  | some b =>
      simp only [hdb] at h
      have hpair := Option.some.inj h
      have hvb : b = v := congrArg Prod.fst hpair
      have hrest : buf.drop 32 = rest := congrArg Prod.snd hpair
      subst hvb
      have hdu : decodeUint buf = some (if b then 1 else 0) :=
        (decodeBool_eq_some_iff buf b).mp hdb
      have htake := buf_take_32_eq_encodeUint_of_decodeUint buf (if b then 1 else 0) hdu
      simp only [encode, put, toList_putBool, encodeBool]
      rw [← hrest, ← htake, List.take_append_drop 32 buf]

/-- `decode` at `address` reads a canonical `address` word. -/
theorem decode_address_sound (v : Ty.Val .address) (buf rest : List UInt8)
    (h : decode .address buf = some (v, rest)) : encode .address v ++ rest = buf := by
  obtain ⟨n, hn⟩ := v
  simp only [decode] at h
  cases hda : decodeAddress buf with
  | none => simp only [hda] at h; contradiction
  | some x =>
      simp only [hda] at h
      by_cases hx : x < 2 ^ 160
      · rw [dif_pos hx] at h
        have hpair := Option.some.inj h
        have hxn : x = n := congrArg (fun p => p.1.val) hpair
        have hrest : buf.drop 32 = rest := congrArg (fun p => p.2) hpair
        subst hxn
        simp only [encode, put, toList_putAddress, encodeAddress]
        rw [← hrest, ← buf_take_32_eq_encodeUint_of_decodeUint buf x hda,
          List.take_append_drop 32 buf]
      · rw [dif_neg hx] at h; contradiction

/-- `decode` at `bytesN` reads a canonical `bytesN` word. -/
theorem decode_bytesN_sound (m : Nat) (v : Ty.Val (.bytesN m)) (buf rest : List UInt8)
    (h : decode (.bytesN m) buf = some (v, rest)) :
    encode (.bytesN m) v ++ rest = buf := by
  obtain ⟨bs, hbs⟩ := v
  simp only [decode] at h
  cases hdb : decodeBytesN m buf with
  | none => simp only [hdb] at h; contradiction
  | some xs =>
      simp only [hdb] at h
      by_cases hx : xs.length = m
      · rw [dif_pos hx] at h
        have hpair := Option.some.inj h
        have hxs : xs = bs := congrArg (fun p => p.1.val) hpair
        have hrest : buf.drop 32 = rest := congrArg (fun p => p.2) hpair
        subst hxs
        have htake := buf_take_32_eq_encodeBytesN_of_decodeBytesN hdb
        simp only [encode, put, toList_putBytesN]
        rw [← hrest, ← htake, List.take_append_drop 32 buf]
      · rw [dif_neg hx] at h; contradiction

/-- `decode` at `bytes` reads a canonical `bytes` payload. -/
theorem decode_bytes_sound (v : Ty.Val .bytes) (buf rest : List UInt8)
    (h : decode .bytes buf = some (v, rest)) : encode .bytes v ++ rest = buf := by
  obtain ⟨bs, hlb⟩ := v
  simp only [decode] at h
  split at h
  · next xs n hp =>
      injection (Option.some.inj h) with hxs' hrest
      injection hxs' with hxs
      subst hxs
      have htake := (take_eq_encodeBytes_of_decodeBytesPrefix buf xs n hp).1
      simp only [encode, put, toList_putBytes]
      rw [← hrest, ← htake, List.take_append_drop n buf]
  · contradiction

/-- `decode` at `string` reads a canonical `string` payload. -/
theorem decode_string_sound (v : Ty.Val .string) (buf rest : List UInt8)
    (h : decode .string buf = some (v, rest)) : encode .string v ++ rest = buf := by
  obtain ⟨s, hlb⟩ := v
  simp only [decode] at h
  split at h
  · next xs n hp =>
      split at h
      · next t hus =>
          injection (Option.some.inj h) with ht' hrest
          injection ht' with ht
          subst ht
          have htake := (take_eq_encodeBytes_of_decodeBytesPrefix buf xs n hp).1
          have hxs : xs = t.toUTF8.data.toList := by
            have hutf : t.toUTF8 = xs.toByteArray := toUTF8_of_fromUTF8? hus
            rw [hutf, List.data_toByteArray]
          simp only [encode, put, toList_putString, encodeString]
          rw [← hrest, ← hxs, ← htake, List.take_append_drop n buf]
      · contradiction
  · contradiction

/- ### the walkers -/

mutual
/-- **Soundness, per-component, static**: a canonical static component
reads back inline, leaving the frontier untouched. -/
theorem decodeElem_sound_static (t : Ty) (hv : t.Valid) (v : t.Val)
    (head tails : List UInt8) (E : Nat) (hs : t.IsStatic = true)
    (h : (decodeElem t).run head tails E = some (v, head', tails', E')) :
    head = encode t v ++ head' ∧ tails' = tails ∧ E' = E := by
  rw [decodeElem_static t head tails E hs] at h
  cases ht : decode t head with
  | none => simp only [ht] at h; contradiction
  | some p =>
      obtain ⟨v', rest'⟩ := p
      simp only [ht] at h
      have hpair := Option.some.inj h
      have hv' : v' = v := congrArg (fun p => p.1) hpair
      have hhd : rest' = head' := congrArg (fun p => p.2.1) hpair
      have htl : tails = tails' := congrArg (fun p => p.2.2.1) hpair
      have hE' : E = E' := congrArg (fun p => p.2.2.2) hpair
      subst hv'
      rw [← hhd, ← htl, ← hE']
      constructor
      · exact (decode_sound t hv v' head rest' ht).symm
      · constructor <;> rfl
termination_by 8 * sizeOf t + 1

/-- **Soundness, per-component, dynamic**: a canonical dynamic component's
head slot holds the offset word `E`, its frontier slice its tail, and the
frontier advances by the tail size. -/
theorem decodeElem_sound_dynamic (t : Ty) (hv : t.Valid) (v : t.Val)
    (head tails : List UInt8) (E : Nat) (hs : t.IsStatic = false)
    (h : (decodeElem t).run head tails E = some (v, head', tails', E')) :
    head = encodeUint E ++ head' ∧ tails = encode t v ++ tails' ∧
      E' = E + (partOf t v).tailSize := by
  rw [decodeElem_dynamic t head tails E hs] at h
  cases hn : natAt head 0 with
  | none => simp only [hn] at h; contradiction
  | some o =>
      simp only [hn] at h
      by_cases ho : o = E
      · rw [if_pos ho] at h
        cases ht : decode t tails with
        | none => simp only [ht] at h; contradiction
        | some p =>
            obtain ⟨v', rest'⟩ := p
            simp only [ht] at h
            have hpair := Option.some.inj h
            have hv' : v' = v := congrArg (fun p => p.1) hpair
            have hhd : head.drop 32 = head' := congrArg (fun p => p.2.1) hpair
            have hrt : rest' = tails' := congrArg (fun p => p.2.2.1) hpair
            have hE' : E + (tails.length - rest'.length) = E' :=
              congrArg (fun p => p.2.2.2) hpair
            have hword : head.take 32 = encodeUint E :=
              take_32_eq_encodeUint_of_natAt head 0 E (by simpa [ho] using hn)
            have hhead : head = encodeUint E ++ head' := by
              rw [← hword, ← hhd, List.take_append_drop 32 head]
            have htail : tails = encode t v ++ tails' := by
              have hsnd := decode_sound t hv v' tails rest' ht
              rw [hv', hrt] at hsnd
              exact hsnd.symm
            have hE'' : E' = E + (partOf t v).tailSize := by
              rw [← hE', hrt]
              rw [htail, List.length_append, Nat.add_sub_cancel]
              rw [tailSize_partOf_dynamic t v hs]
            exact ⟨hhead, htail, hE''⟩
      · rw [if_neg ho] at h; contradiction
termination_by 8 * sizeOf t + 1

/-- **Soundness, element lists**: a run of canonical elements that reads
back has consumed exactly its head and tail encodings. -/
theorem decodeElems_sound (t : Ty) (hv : t.Valid) (vs : List t.Val) (k : Nat)
    (hk : vs.length = k) (E : Nat) (head tails : List UInt8)
    (h : (decodeElems t k).run head tails E = some (⟨vs, hk⟩, head', tails', E')) :
    head = encodeHeads E (vs.map (partOf t)) ++ head' ∧
    tails = encodeTails (vs.map (partOf t)) ++ tails' ∧
    E' = E + tailSizes (vs.map (partOf t)) := by
  induction vs generalizing k E head tails with
  | nil =>
      subst hk
      change (decodeElems t 0).run head tails E = some (⟨[], rfl⟩, head', tails', E') at h
      simp only [decodeElems, Get2.pure_run] at h
      have hhd : head = head' := congrArg (fun p => p.2.1) (Option.some.inj h)
      have htl : tails = tails' := congrArg (fun p => p.2.2.1) (Option.some.inj h)
      have hE' : E = E' := congrArg (fun p => p.2.2.2) (Option.some.inj h)
      rw [hhd, htl, ← hE']
      simp [encodeHeads, encodeTails, putHeads, putTails, tailSizes, Builder.toList_empty]
  | cons w ws ih =>
      have hk' : k = ws.length + 1 := by rw [← hk, List.length_cons]
      subst hk'
      simp only [List.map_cons, decodeElems, Get2.bind_run, Get2.pure_run] at h ⊢
      cases he : (decodeElem t).run head tails E with
      | none => simp only [he] at h; contradiction
      | some p =>
          obtain ⟨v, head0, tails0, E0⟩ := p
          simp only [he] at h
          cases hi : (decodeElems t ws.length).run head0 tails0 E0 with
          | none => simp only [hi] at h; contradiction
          | some q =>
              obtain ⟨⟨ws', hws'⟩, head1, tails1, E1⟩ := q
              simp only [hi] at h
              have hpair := Option.some.inj h
              have hvs' : v :: ws' = w :: ws := congrArg (fun p => p.1.val) hpair
              have hhd1 : head1 = head' := congrArg (fun p => p.2.1) hpair
              have htl1 : tails1 = tails' := congrArg (fun p => p.2.2.1) hpair
              injection hvs' with hv hws''
              subst hv
              subst hws''
              have hE1 : E1 = E' := congrArg (fun p => p.2.2.2) hpair
              rw [hhd1, htl1, hE1] at hi
              have hih : head0 = encodeHeads E0 (ws'.map (partOf t)) ++ head' ∧
                  tails0 = encodeTails (ws'.map (partOf t)) ++ tails' ∧
                  E' = E0 + tailSizes (ws'.map (partOf t)) :=
                ih ws'.length hws' E0 head0 tails0 hi
              cases hs0 : t.IsStatic
              · have hsf : t.IsStatic = false := hs0
                obtain ⟨hhead, htail, hE0'⟩ :=
                  decodeElem_sound_dynamic t hv v head tails E hsf he
                refine ⟨?_, ?_, ?_⟩
                · rw [hhead, hih.1, hE0']
                  rw [partOf_dynamic t v hsf, encodeHeads_cons_dynamic]
                  simp [Part.tailSize]
                · rw [htail, hih.2.1]
                  rw [partOf_dynamic t v hsf, encodeTails_cons_dynamic, List.append_assoc]
                  rfl
                · rw [hih.2.2, hE0']
                  simp [tailSizes, Nat.add_assoc]
              · have hst : t.IsStatic = true := hs0
                obtain ⟨hhead, htl0, hE0⟩ :=
                  decodeElem_sound_static t hv v head tails E hst he
                refine ⟨?_, ?_, ?_⟩
                · rw [hhead, hih.1, hE0]
                  rw [partOf_static t v hst, encodeHeads_cons_static, List.append_assoc]
                  rfl
                · rw [← htl0, hih.2.1]
                  rw [partOf_static t v hst, encodeTails_cons_static]
                · rw [hih.2.2, hE0]
                  simp [tailSizes, tailSize_partOf_static t v hst]
termination_by 8 * sizeOf t + 2

/-- **Soundness, tuples**: a canonical tuple that reads back has consumed
exactly its head and tail encodings. -/
theorem decodeTuple_sound : (ts : List Ty) → AllValid ts → (vs : TupleVal ts) →
    (E : Nat) → (head tails : List UInt8) →
    (decodeTuple ts).run head tails E = some (vs, head', tails', E') →
    head = encodeHeads E (partsOfTuple ts vs) ++ head' ∧
    tails = encodeTails (partsOfTuple ts vs) ++ tails' ∧
    E' = E + tailSizes (partsOfTuple ts vs)
  | [], hv, vs, E, head, tails, h => by
      simp only [decodeTuple, Get2.pure_run] at h
      have hhd : head = head' := congrArg (fun p => p.2.1) (Option.some.inj h)
      have htl : tails = tails' := congrArg (fun p => p.2.2.1) (Option.some.inj h)
      have hE' : E = E' := congrArg (fun p => p.2.2.2) (Option.some.inj h)
      rw [hhd, htl, ← hE']
      simp [partsOfTuple, encodeHeads, encodeTails, putHeads, putTails, tailSizes,
        Builder.toList_empty]
  | t :: ts, hv, (v, vs), E, head, tails, h => by
      obtain ⟨hvt, hvs⟩ := hv
      simp only [partsOfTuple, decodeTuple, Get2.bind_run, Get2.pure_run] at h ⊢
      cases he : (decodeElem t).run head tails E with
      | none => simp only [he] at h; contradiction
      | some p =>
          obtain ⟨v', head0, tails0, E0⟩ := p
          simp only [he] at h
          cases hi : (decodeTuple ts).run head0 tails0 E0 with
          | none => simp only [hi] at h; contradiction
          | some q =>
              obtain ⟨vs', head1, tails1, E1⟩ := q
              simp only [hi] at h
              have hpair := Option.some.inj h
              have hv' : v' = v := congrArg (fun p => p.1.1) hpair
              have hvs' : vs' = vs := congrArg (fun p => p.1.2) hpair
              have hhd1 : head1 = head' := congrArg (fun p => p.2.1) hpair
              have htl1 : tails1 = tails' := congrArg (fun p => p.2.2.1) hpair
              subst hv'
              subst hvs'
              have hE1 : E1 = E' := congrArg (fun p => p.2.2.2) hpair
              have hih : head0 = encodeHeads E0 (partsOfTuple ts vs') ++ head1 ∧
                  tails0 = encodeTails (partsOfTuple ts vs') ++ tails1 ∧
                  E1 = E0 + tailSizes (partsOfTuple ts vs') :=
                decodeTuple_sound ts hvs vs' E0 head0 tails0 hi
              cases hs0 : t.IsStatic
              · have hsf : t.IsStatic = false := hs0
                obtain ⟨hhead, htail, hE0'⟩ :=
                  decodeElem_sound_dynamic t hvt v' head tails E hsf he
                refine ⟨?_, ?_, ?_⟩
                · rw [hhead, hih.1, hE0', hhd1]
                  rw [partOf_dynamic t v' hsf, encodeHeads_cons_dynamic]
                  simp [Part.tailSize]
                · rw [htail, hih.2.1, htl1]
                  rw [partOf_dynamic t v' hsf, encodeTails_cons_dynamic, List.append_assoc]
                  rfl
                · rw [← hE1, hih.2.2, hE0']
                  simp [tailSizes, Nat.add_assoc]
              · have hst : t.IsStatic = true := hs0
                obtain ⟨hhead, htl0, hE0⟩ :=
                  decodeElem_sound_static t hvt v' head tails E hst he
                refine ⟨?_, ?_, ?_⟩
                · rw [hhead, hih.1, hE0, hhd1]
                  rw [partOf_static t v' hst, encodeHeads_cons_static, List.append_assoc]
                  rfl
                · rw [← htl0, hih.2.1, htl1]
                  rw [partOf_static t v' hst, encodeTails_cons_static]
                · rw [← hE1, hih.2.2, hE0]
                  simp [tailSizes, tailSize_partOf_static t v' hst]
termination_by ts => 8 * sizeOf ts + 3

/-- **Soundness, prefix form**: whenever the linear decoder succeeds, the
buffer is the encoding of the decoded value plus the remainder. -/
theorem decode_sound (t : Ty) (hv : t.Valid) (v : t.Val) (buf rest : List UInt8)
    (h : decode t buf = some (v, rest)) : encode t v ++ rest = buf := by
  cases t with
  | uint m => exact decode_uint_sound m v buf rest h
  | int m => exact decode_int_sound m v buf rest h
  | bool => exact decode_bool_sound v buf rest h
  | address => exact decode_address_sound v buf rest h
  | bytesN m => exact decode_bytesN_sound m v buf rest h
  | bytes => exact decode_bytes_sound v buf rest h
  | string => exact decode_string_sound v buf rest h
  | array t =>
      obtain ⟨vs, hlk⟩ := v
      have hvt : t.Valid := hv
      simp only [decode] at h
      split at h
      · contradiction
      · next k hk =>
          cases he : (decodeElems t k).run (buf.drop 32) (buf.drop (32 + k * t.headSize))
            (k * t.headSize) with
          | none => simp only [he] at h; contradiction
          | some q =>
              obtain ⟨⟨vs', hvs'⟩, head0, tails0, E0⟩ := q
              simp only [he] at h
              have hpair := Option.some.inj h
              have hvs'eq : vs' = vs := congrArg (fun p => p.1.val) hpair
              have hrt : tails0 = rest := congrArg (fun p => p.2) hpair
              have hsnd := decodeElems_sound t hvt vs' k hvs' (k * t.headSize)
                (buf.drop 32) (buf.drop (32 + k * t.headSize)) he
              have hlenH : headSizes (vs'.map (partOf t)) = vs'.length * t.headSize :=
                headSizes_map_partOf_any t hvt vs'
              have htake : buf.take 32 = encodeUint k :=
                buf_take_32_eq_encodeUint_of_decodeUint buf k hk
              have hhead0 : head0 = encodeTails (vs'.map (partOf t)) ++ tails0 := by
                have hlen : (encodeHeads (k * t.headSize) (vs'.map (partOf t))).length =
                    k * t.headSize := by
                  rw [length_encodeHeads, hlenH, hvs']
                have hd := congrArg (fun x => x.drop (k * t.headSize)) hsnd.1
                rw [drop_append_of_length hlen] at hd
                rw [List.drop_drop] at hd
                rw [← hd, hsnd.2.1]
              have hinner : encodeHeads (k * t.headSize) (vs'.map (partOf t)) ++
                  (encodeTails (vs'.map (partOf t)) ++ rest) = buf.drop 32 := by
                rw [hsnd.1, hhead0, hrt]
              simp only [encode, put, toList_putUint, toList_append]
              rw [← hvs'eq, hvs', ← htake, ← encodeParts, encodeParts_unfold, hlenH, hvs',
                List.append_assoc, List.append_assoc, hinner, List.take_append_drop 32 buf]
  | fixedArray t n =>
      obtain ⟨vs, hvs⟩ := v
      have hvt : t.Valid := hv
      simp only [decode] at h
      cases he : (decodeElems t n).run buf (buf.drop (n * t.headSize)) (n * t.headSize) with
      | none => simp only [he] at h; contradiction
      | some q =>
          obtain ⟨⟨vs', hvs'⟩, head0, tails0, E0⟩ := q
          simp only [he] at h
          have hpair := Option.some.inj h
          have hvs'eq : vs' = vs := congrArg (fun p => p.1.val) hpair
          have hrt : tails0 = rest := congrArg (fun p => p.2) hpair
          have hsnd := decodeElems_sound t hvt vs' n hvs' (n * t.headSize) buf
            (buf.drop (n * t.headSize)) he
          have hlenH : headSizes (vs'.map (partOf t)) = n * t.headSize := by
            rw [headSizes_map_partOf_any t hvt vs', hvs']
          have hhead0 : head0 = encodeTails (vs'.map (partOf t)) ++ tails0 := by
            have hlen : (encodeHeads (n * t.headSize) (vs'.map (partOf t))).length =
                n * t.headSize := by
              rw [length_encodeHeads, hlenH]
            have hd := congrArg (fun x => x.drop (n * t.headSize)) hsnd.1
            rw [drop_append_of_length hlen] at hd
            rw [← hd, hsnd.2.1]
          simp only [encode, put]
          rw [← hvs'eq, ← encodeParts, encodeParts_unfold, hlenH, hsnd.1, hhead0, hrt,
            List.append_assoc]
  | tuple ts =>
      have hvts : AllValid ts := hv
      simp only [decode] at h
      cases he : (decodeTuple ts).run buf (buf.drop (headSizeSum ts)) (headSizeSum ts) with
      | none => simp only [he] at h; contradiction
      | some q =>
          obtain ⟨vs', head0, tails0, E0⟩ := q
          simp only [he] at h
          have hpair := Option.some.inj h
          have hvs' : vs' = v := congrArg (fun p => p.1) hpair
          have hrt : tails0 = rest := congrArg (fun p => p.2) hpair
          subst hvs'
          have hsnd := decodeTuple_sound ts hvts vs' (headSizeSum ts) buf
            (buf.drop (headSizeSum ts)) he
          have hlenH : headSizes (partsOfTuple ts vs') = headSizeSum ts :=
            headSizes_partsOfTuple_any ts hvts vs'
          have hhead0 : head0 = encodeTails (partsOfTuple ts vs') ++ tails0 := by
            have hlen : (encodeHeads (headSizeSum ts) (partsOfTuple ts vs')).length =
                headSizeSum ts := by
              rw [length_encodeHeads, hlenH]
            have hd := congrArg (fun x => x.drop (headSizeSum ts)) hsnd.1
            rw [drop_append_of_length hlen] at hd
            rw [← hd, hsnd.2.1]
          simp only [encode, put]
          rw [← encodeParts, encodeParts_unfold, hlenH, hsnd.1, hhead0, hrt, List.append_assoc]
termination_by 8 * sizeOf t
end

/-! ## the strictness API -/

/-- Strict decoder: canonical layout and exact length, via the linear
canonical reader `decode`.  For call data (selector ++ arguments),
decode the argument tuple on `buf.drop 4` and compare against `buf.length - 4`. -/
def decodeStrict (t : Ty) (buf : List UInt8) : Option t.Val :=
  match decode t buf with
  | some (v, rest) => if rest = [] then some v else none
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
      obtain ⟨v', rest⟩ := p
      simp only [hg] at h
      by_cases hrest : rest = []
      · rw [if_pos hrest] at h
        have hv' : v' = v := Option.some.inj h
        subst hv'
        have hsnd := decode_sound t hv v' buf rest hg
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
