import EvmAbi.Ty
import EvmAbi.Static
import EvmAbi.Dynamic
import EvmAbi.Align
import EvmAbi.Word
import EvmAbi.Parts

/-!
# EvmAbi.Spec

The **spec codec** — the list-based surface every theorem is stated over.
All definitions in this file live in `namespace EvmAbi.Spec`:
`Spec.put` / `Spec.encode` / `Spec.encodeByteArray`, the linear decoder
`Spec.decode` with its `Get2` walkers, the bound-free static delegation,
and the helper packages.  The user-facing runtime codec is
`EvmAbi.Codec`.
-/

namespace EvmAbi
namespace Spec

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
  match t.isStatic with
  | true => ⟨put t v, ∅, false⟩
  | false => ⟨∅, put t v, true⟩
termination_by (sizeOf t, 1)

/-- A tuple value seen as a list of parts. -/
def partsOfTuple : (ts : List Ty) → TupleVal ts → List Part
  | [], _ => []
  | t :: ts, (v, vs) => partOf t v :: partsOfTuple ts vs
termination_by ts => (sizeOf ts, 2)
end

/-- ABI encoder (type-indexed): the materialization of `put`.  This is the
*specification* — `List UInt8` is the type the proofs are stated over —
and it is not what you run; see `encodeByteArray`. -/
def encode (t : Ty) (v : t.Val) : List UInt8 := (put t v).toList

/-- **Executable ABI encoder**: run the same `put` into a contiguous
`ByteArray`, sized exactly from the builder's cached size and filled in one
linear pass.  Nothing about the layout is duplicated — this is `encode`'s
builder, materialized the other way. -/
def encodeByteArray (t : Ty) (v : t.Val) : ByteArray := (put t v).run

/-- `encodeByteArray` produces exactly the bytes `encode` specifies, so
every `List UInt8` theorem transports to it by rewriting. -/
@[simp] theorem data_toList_encodeByteArray (t : Ty) (v : t.Val) :
    (encodeByteArray t v).data.toList = encode t v :=
  Builder.data_toList_run (put t v)

/-- …equivalently, it is the specification encoding packed into a `ByteArray`. -/
theorem encodeByteArray_eq (t : Ty) (v : t.Val) :
    encodeByteArray t v = (encode t v).toByteArray :=
  Builder.run_eq_toByteArray (put t v)

@[simp] theorem size_encodeByteArray (t : Ty) (v : t.Val) :
    (encodeByteArray t v).size = (encode t v).length := by
  rw [encodeByteArray, Builder.size_run, Builder.size_eq_length_toList]
  rfl

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
theorem partOf_static (t : Ty) (v : t.Val) (h : t.isStatic = true) :
    partOf t v = ⟨put t v, ∅, false⟩ := by
  simp [partOf, h]

/-- `partOf` of a dynamic value is the offset-word head plus tail part. -/
theorem partOf_dynamic (t : Ty) (v : t.Val) (h : t.isStatic = false) :
    partOf t v = ⟨∅, put t v, true⟩ := by
  simp [partOf, h]

/-- A component contributes its part's tail to the tail section: nothing for
a static component (whose part has an empty tail), its encoding for a
dynamic one. -/
theorem encodeTails_cons_partOf (t : Ty) (v : t.Val) (ps : List Part) :
    encodeTails (partOf t v :: ps) = (partOf t v).tail.toList ++ encodeTails ps := by
  cases hs : t.isStatic
  · rw [partOf_dynamic t v hs, encodeTails_cons_dynamic]
  · rw [partOf_static t v hs, encodeTails_cons_static]; simp [Builder.toList_empty]

/-- Dynamic types occupy exactly one offset word in the head. -/
theorem headSize_of_dynamic (t : Ty) (h : t.isStatic = false) : t.headSize = 32 := by
  cases t
  case fixedArray t n =>
      have h' : t.isStatic = false := by simpa [isStatic] using h
      simp [headSize, h']
  case tuple ts =>
      have h' : allStatic ts = false := by simpa [isStatic] using h
      simp [headSize, h']
  all_goals simp [headSize]

/-! ## Package A: head sizes and static encoding lengths -/

/- The head size of a static type is always a multiple of 32, and a static
encoding occupies exactly its head size.  The list siblings use the
`+1`-offset measure so the default decreasing tactic closes every goal. -/
mutual
/-- The head size of a static type is 32-byte aligned. -/
theorem dvd_headSize_static : (t : Ty) → t.isStatic = true → 32 ∣ t.headSize
  | uint _, _ | int _, _ | Ty.bool, _ | address, _ | bytesN _, _ => ⟨1, by simp [headSize]⟩
  | bytes, hs | string, hs | array _, hs => by simp [isStatic] at hs
  | fixedArray t n, hs => by
      have hst : t.isStatic = true := by simp only [isStatic] at hs; exact hs
      obtain ⟨k, hk⟩ := dvd_headSize_static t hst
      exact ⟨n * k, by simp only [headSize]; rw [if_pos hst, hk]; ac_rfl⟩
  | tuple ts, hs => by
      have hss : allStatic ts = true := by simp only [isStatic] at hs; exact hs
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
  cases hs : t.isStatic
  · rw [headSize_of_dynamic t hs]; exact ⟨1, rfl⟩
  · exact dvd_headSize_static t hs

mutual
/-- Static encodings occupy exactly their head size. -/
theorem encode_length_static : (t : Ty) → t.isStatic = true → t.Valid → (v : t.Val) →
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
  | bytes, hs, _, _ | string, hs, _, _ | array _, hs, _, _ => by simp [isStatic] at hs
  | fixedArray t n, hs, hv, ⟨vs, hvs⟩ => by
      have hst : t.isStatic = true := by simp only [isStatic] at hs; exact hs
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
            · simp only [headSizes, Part.headSize, List.length_cons,
                Builder.size_eq_length_toList]
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
      have hss : allStatic ts = true := by simp only [isStatic] at hs; exact hs
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
      simp only [headSizes, tailSizes, Part.headSize, Part.tailSize, headSizeSum,
        Builder.size_eq_length_toList]
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
  cases hs : t.isStatic
  · rw [partOf_dynamic t v hs]
    exact (headSize_of_dynamic t hs).symm
  · rw [partOf_static t v hs, Part.headSize, Builder.size_eq_length_toList]
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
  by_cases hs : t.isStatic
  · rw [encode_length_static t hs hv v]
    exact dvd_headSize_static t hs
  · have hsf : t.isStatic = false := by simp at hs; exact hs
    cases t with
    | uint m => simp [isStatic] at hsf
    | int m => simp [isStatic] at hsf
    | bool => simp [isStatic] at hsf
    | address => simp [isStatic] at hsf
    | bytesN m => simp [isStatic] at hsf
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
        have hvt : t.Valid := (valid_array.mp hv).1
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
      · by_cases hs : t.isStatic
        · rw [partOf_static t w hs]
          constructor
          · change 32 ∣ (encode t w).length
            rw [encode_length_static t hs hv w]; exact dvd_headSize_static t hs
          · exact ⟨0, rfl⟩
        · have hsf : t.isStatic = false := by simp at hs; exact hs
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
      · by_cases hs : t.isStatic
        · rw [partOf_static t v hs]
          constructor
          · change 32 ∣ (encode t v).length
            rw [encode_length_static t hs hvt v]; exact dvd_headSize_static t hs
          · exact ⟨0, rfl⟩
        · have hsf : t.isStatic = false := by simp at hs; exact hs
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
theorem drop_head_partOf_static (t : Ty) (hs : t.isStatic = true) (v : t.Val)
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
theorem tailOffset_partOf_dynamic_le (t : Ty) (v : t.Val) (h : t.isStatic = false)
    (xs ys : List Part) :
    tailOffset (xs ++ (partOf t v :: ys)) xs.length ≤
      (encodeParts (xs ++ (partOf t v :: ys))).length := by
  rw [partOf_dynamic t v h, length_encodeParts, tailOffset, take_append_of_length rfl,
    tailSizes_append]
  simp [tailSizes, Part.tailSize]

/-- Dropping to a dynamic part's tail offset lands exactly on its tail, even
with a trailing suffix after the whole layout. -/
theorem drop_tail_partOf_dynamic (t : Ty) (v : t.Val) (h : t.isStatic = false)
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
theorem natAt_offset_partOf_dynamic (t : Ty) (v : t.Val) (h : t.isStatic = false)
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
      by_cases hc : len < 2 ^ 64 ∧ ((buf.drop 32).take len).length = len ∧
          ((buf.drop 32).drop len).take ((32 - len % 32) % 32) =
            List.replicate ((32 - len % 32) % 32) 0
      · rw [if_pos hc] at h
        have h2 := Option.some.inj h
        have hbs : (buf.drop 32).take len = bs := congrArg Prod.fst h2
        have hm : 32 + len + (32 - len % 32) % 32 = m := congrArg Prod.snd h2
        have htake32 := take_32_eq_encodeUint_of_natAt buf 0 len hlen
        simp only [Nat.mul_zero, List.drop_zero] at htake32
        have hblen : bs.length = len := by rw [← hbs]; exact hc.2.1
        subst hm
        constructor
        · have hsplit : buf.take (32 + len + (32 - len % 32) % 32) =
              buf.take 32 ++ (buf.drop 32).take (len + (32 - len % 32) % 32) := by
            rw [← List.take_add]
            congr 1
            omega
          rw [hsplit, htake32, List.take_add, hbs, hc.2.2]
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
`t` from the front of the buffer, returning it together with the number of
bytes it consumed and the untouched remainder.

The consumed count is computed *structurally* — a constant for the word
types, the count already reported by `decodeBytesPrefix` for the payload
types, and the walker's final frontier for the compound types (the
frontier starts at the head size and advances by each tail, so it ends at
exactly the size of the layout).  It is never measured off the buffers:
`decodeElem` advances the frontier by it in `O(1)`, which is what keeps
the whole walk linear.

The `array` case rejects element types with no head up front: nothing
would advance either cursor, so the element walk would not be bounded by
the buffer.  `Ty.Valid` rules those types out (`0 < t.headSize`), so no
theorem loses ground. -/
def decode : (t : Ty) → List UInt8 → Option (t.Val × Nat × List UInt8)
  | .uint m, buf => match decodeUint buf with
      | some n => if h : n < 2 ^ m then some (⟨n, h⟩, 32, buf.drop 32) else none
      | none => none
  | .int m, buf => match decodeInt buf with
      | some i => if h : -((2 ^ (m - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m - 1) : Nat) : Int) then
          some (⟨i, h⟩, 32, buf.drop 32)
        else none
      | none => none
  | .bool, buf => match decodeBool buf with
      | some b => some (b, 32, buf.drop 32)
      | none => none
  | .address, buf => match decodeAddress buf with
      | some n => if h : n < 2 ^ 160 then some (⟨n, h⟩, 32, buf.drop 32) else none
      | none => none
  | .bytesN m, buf => match decodeBytesN m buf with
      | some bs => if h : bs.length = m then some (⟨bs, h⟩, 32, buf.drop 32) else none
      | none => none
  | .bytes, buf => match hp : decodeBytesPrefix buf with
      | some (bs, n) => some (⟨bs, length_lt_of_decodeBytesPrefix hp⟩, n, buf.drop n)
      | none => none
  | .string, buf => match hp : decodeBytesPrefix buf with
      | some (bs, n) => match hs : String.fromUTF8? bs.toByteArray with
          | some s => some (⟨s, size_toUTF8_lt_of_decodeBytesPrefix hp hs⟩, n, buf.drop n)
          | none => none
      | none => none
  | .array t, buf => if t.headSize = 0 then none else
      match natAt buf 0 with
      | none => none
      | some k => if hb : k < 2 ^ 64 then
          match (decodeElems t k).run (buf.drop 32) (buf.drop (32 + k * t.headSize)) (k * t.headSize) with
          | some ⟨vs, _, rest, E⟩ => some (⟨vs.val, by rw [vs.property]; exact hb⟩, 32 + E, rest)
          | none => none
        else none
  | .fixedArray t n, buf => match (decodeElems t n).run buf (buf.drop (n * t.headSize)) (n * t.headSize) with
      | some ⟨vs, _, rest, E⟩ => some (vs, E, rest)
      | none => none
  | .tuple ts, buf => match (decodeTuple ts).run buf (buf.drop (headSizeSum ts)) (headSizeSum ts) with
      | some ⟨vs, _, rest, E⟩ => some (vs, E, rest)
      | none => none
termination_by t => (sizeOf t, 0)

/-- Read one component at its head slot, as a `Get2` program: static
components decode in place from the head cursor; dynamic components must
have their offset word equal to the frontier `E` and decode from the tail
cursor, advancing the frontier by the bytes that component consumed. -/
def decodeElem (t : Ty) : Get2 t.Val := ⟨fun head tails E =>
  match t.isStatic with
  | true => match decode t head with
      | some (v, _, rest) => some ⟨v, rest, tails, E⟩
      | none => none
  | false => match natAt head 0 with
      | none => none
      | some o => if o = E then
          match decode t tails with
          | some (v, n, rest) => some ⟨v, head.drop 32, rest, E + n⟩
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
theorem encodeTails_map_partOf_static (t : Ty) (hs : t.isStatic = true) (vs : List t.Val) :
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
theorem decodeElem_static_append (t : Ty) (hs : t.isStatic = true) (hv : t.Valid)
    (v : t.Val) (head tails : List UInt8) (E : Nat) :
    (decodeElem t).run (encode t v ++ head) tails E = some ⟨v, head, tails, E⟩ := by
  simp only [decodeElem, hs]
  rw [decode_static_append t hs hv v head]
termination_by 8 * sizeOf t + 1

/-- A run of static elements reads back from its flattened encodings,
leaving the suffix and the tail cursor untouched. -/
theorem decodeElems_static_append (t : Ty) (hs : t.isStatic = true) (hv : t.Valid)
    (vs : List t.Val) (k : Nat) (hk : vs.length = k) (E : Nat) (head tails : List UInt8) :
    (decodeElems t k).run (encodeHeads E (vs.map (partOf t)) ++ head) tails E =
      some ⟨⟨vs, hk⟩, head, tails, E⟩ := by
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
      some ⟨vs, head, tails, E⟩
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
front of its own encoding followed by an arbitrary suffix, consuming
exactly its head size — bound-free, since static types have no offset
words. -/
theorem decode_static_append (t : Ty) (hs : t.isStatic = true) (hv : t.Valid)
    (v : t.Val) (rest : List UInt8) :
    decode t (encode t v ++ rest) = some (v, t.headSize, rest) := by
  cases t with
  | uint m =>
      obtain ⟨n, hn⟩ := v
      have hdec : decodeUint (encodeUint n ++ rest) = some n :=
        decodeUint_append n rest
          (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (n := 2) (by decide) hv.2.1))
      simp only [encode, put, decode, toList_putUint, headSize]
      rw [hdec]
      exact dif_pos hn
  | int m =>
      obtain ⟨i, hi⟩ := v
      have h0 : 0 < m := by have h8 := hv.1; omega
      have hdec : decodeInt (encodeInt i ++ rest) = some i :=
        decodeInt_append h0 hv.2.1 hi.1 hi.2 rest
      simp only [encode, put, decode, toList_putInt, headSize]
      rw [hdec]
      exact dif_pos hi
  | bool =>
      simp only [encode, put, decode, toList_putBool, headSize]
      rw [decodeBool_append v rest]
      rfl
  | address =>
      obtain ⟨n, hn⟩ := v
      have hdec : decodeAddress (encodeAddress n ++ rest) = some n :=
        decodeAddress_append n rest hn
      simp only [encode, put, decode, toList_putAddress, headSize]
      rw [hdec]
      exact dif_pos hn
  | bytesN m =>
      obtain ⟨bs, hbs⟩ := v
      have hdec : decodeBytesN m (encodeBytesN bs ++ rest) = some bs :=
        decodeBytesN_append hv.2 hbs rest
      have hlen : (encodeBytesN bs).length = 32 :=
        length_encodeBytesN (by rw [hbs]; exact hv.2)
      simp only [encode, put, decode, toList_putBytesN, headSize]
      rw [hdec]
      dsimp only []
      rw [dif_pos hbs]
      rw [show (encodeBytesN bs ++ rest).drop 32 = rest from drop_append_of_length hlen]
  | bytes => simp [isStatic] at hs
  | string => simp [isStatic] at hs
  | array t => simp [isStatic] at hs
  | fixedArray t n =>
      obtain ⟨vs, hvs⟩ := v
      have hst : t.isStatic = true := by simpa [isStatic] using hs
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
      simp only [encode, put, decode, headSize, hst, if_true]
      rw [← encodeParts, hbuf, hdr,
        decodeElems_static_append t hst hvt vs n hvs (n * t.headSize) rest rest]
  | tuple ts =>
      have hss : allStatic ts = true := by simpa [isStatic] using hs
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
      simp only [encode, put, decode, headSize, hss, if_true]
      rw [← encodeParts, hbuf, hdr,
        decodeTuple_static_append ts hss hvts v (headSizeSum ts) rest rest]
termination_by 8 * sizeOf t
end

/-- The tail size of a static component's part is zero. -/
theorem tailSize_partOf_static (t : Ty) (v : t.Val) (h : t.isStatic = true) :
    (partOf t v).tailSize = 0 := by
  rw [partOf_static t v h]
  rfl

/-- The tail size of a dynamic component's part is its encoding length. -/
theorem tailSize_partOf_dynamic (t : Ty) (v : t.Val) (h : t.isStatic = false) :
    (partOf t v).tailSize = (encode t v).length := by
  rw [partOf_dynamic t v h, Part.tailSize]
  exact (put t v).size_eq

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

end Spec
