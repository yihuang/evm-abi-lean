import EvmAbi.Ty
import EvmAbi.Bytes
import EvmAbi.Spec
import Binary.UInt256

/-!
# EvmAbi.Packed

Packed ABI encoding (`abi.encodePacked`), following Solidity's non-standard
packed mode:

1. types shorter than 32 bytes are concatenated without padding;
2. dynamic types (`bytes`, `string`, `T[]`) are encoded in place, without
   a length word;
3. array *elements* are padded to their standard 32-byte-word width, but
   still encoded in place;
4. structs and nested arrays are not supported by Solidity —
   `PackedSupported` marks the conformant fragment.  This library's
   `.tuple` arm is the flat *argument list* of a multi-argument
   `abi.encodePacked(a, b, …)` call; applied to nested tuples it is a
   total-function extension with no Solidity counterpart.

Packed encoding is ambiguous in general (no lengths, no offsets), so only
the static fragment is decodable: `decodePacked` reads scalars at their
tight widths and array elements at their padded widths, and rejects
dynamic types.  The codec mirrors the standard one — a `Builder` encoder
(`putPacked` materialized once by `toList`) and `Get2` walkers
(`decodePackedElem` / `decodePackedTuple`; array elements are read by the
standard `decodeElems`) — so packed decoding is a single linear pass.
-/

namespace EvmAbi

open Ty
open Binary
open Builder
open EvmAbi.Spec

/-! ## The Solidity-conformant fragment -/

/-- Scalar (non-composite) static types — the only element types Solidity
accepts inside packed arrays. -/
def PackedScalar : Ty → Bool
  | .uint _ | .int _ | .bool | .address | .bytesN _ => true
  | _ => false

/-- The types Solidity's `abi.encodePacked` accepts as a single argument:
scalars, `bytes`/`string`, and arrays of scalar elements.  Structs
(tuples) and nested arrays are compile errors in Solidity; on those this
library's total encoder is a documented extension, not a conformance
claim. -/
def PackedSupported : Ty → Bool
  | .bytes | .string => true
  | .array t => PackedScalar t
  | .fixedArray t _ _ => PackedScalar t
  | t => PackedScalar t

/-! ## Primitive packed encoders -/

def encodeUintPacked (m : Nat) (n : Nat) : List UInt8 := encodeBEU (m / 8) n

def encodeIntPacked (m : Nat) (i : Int) : List UInt8 :=
  encodeUintPacked m (if 0 ≤ i then i.toNat else 2 ^ m - (-i).toNat)

def encodeBoolPacked (b : Bool) : List UInt8 := [if b then 1 else 0]

def encodeAddressPacked (a : List UInt8) : List UInt8 := a

def encodeBytesNPacked (bs : List UInt8) : List UInt8 := bs

/-! ## Primitive packed decoders -/

/-- Read a packed `uintM` from the front of the buffer.  Widths that are
not byte-aligned are rejected: `encodeBEU (m / 8)` truncates them, so
accepting them would let a lossy encode "roundtrip" (e.g. `uint12` of
`4095` through one byte).  The sufficiency check is *counted*, not
measured: `(buf.take (m / 8)).length = m / 8` walks only the component's
own width, so a packed walk never re-measures the remaining buffer
(`List.length` on the whole cursor would be `O(remaining)` per step). -/
def decodeUintPacked (m : Nat) (buf : List UInt8) : Option Nat :=
  if 0 < m ∧ m % 8 = 0 ∧ (buf.take (m / 8)).length = m / 8 then some (decodeBEU (buf.take (m / 8))) else none

def decodeIntPacked (m : Nat) (buf : List UInt8) : Option Int :=
  (decodeUintPacked m buf).map fun n =>
    if n < 2 ^ (m - 1) then (n : Int) else (n : Int) - ((2 ^ m : Nat) : Int)

def decodeBoolPacked (buf : List UInt8) : Option Bool :=
  match buf with | 0 :: _ => some false | 1 :: _ => some true | _ => none

def decodeAddressPacked (buf : List UInt8) : Option (List UInt8) :=
  if (buf.take 20).length = 20 then some (buf.take 20) else none

def decodeBytesNPacked (n : Nat) (buf : List UInt8) : Option (List UInt8) :=
  if (buf.take n).length = n then some (buf.take n) else none

/-! ## Helpers -/

private theorem pow_eq_256 (m : Nat) (h8 : 8 ∣ m) : 2 ^ m = 256 ^ (m / 8) := by
  have : 8 * (m / 8) = m := Nat.mul_div_cancel' h8
  calc
    2 ^ m = 2 ^ (8 * (m / 8)) := by rw [this]
    _ = (2 ^ 8) ^ (m / 8) := by rw [Nat.pow_mul]
    _ = 256 ^ (m / 8) := by rw [show (2 : Nat) ^ 8 = 256 by decide]

/-- In the negative case of `encodeIntPacked`, the wrapped two's-complement
magnitude `2 ^ m - (-i).toNat` fits its width and has its high bit set, so
`decodeIntPacked` reads it back as the negative value. -/
private theorem twoComp_neg_range {m : Nat} (hm : 0 < m) (i : Int) (hi : ¬ 0 ≤ i)
    (habs : (-i).toNat ≤ 2 ^ (m - 1)) :
    2 ^ m - (-i).toNat < 2 ^ m ∧ ¬ (2 ^ m - (-i).toNat : Nat) < 2 ^ (m - 1) := by
  have hpos_abs : 0 < (-i).toNat := by
    apply Nat.pos_of_ne_zero; intro hz
    have hle0 : -i ≤ 0 := Int.toNat_eq_zero.mp hz; omega
  have hpos_pow : 0 < 2 ^ m := by
    have h := Nat.one_le_pow m 2 (by decide); omega
  constructor
  · apply Nat.sub_lt <;> assumption
  · have h_pow_eq : 2 ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
      calc
        2 ^ m = 2 ^ ((m - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
        _ = 2 ^ (m - 1) * 2 := by rw [Nat.pow_succ]
        _ = 2 ^ (m - 1) + 2 ^ (m - 1) := by omega
    have hle' : (-i).toNat ≤ 2 ^ m :=
      Nat.le_trans habs (Nat.pow_le_pow_right (by decide) (by omega))
    intro hlt
    have hsum : 2 ^ m < 2 ^ (m - 1) + (-i).toNat := by
      have htemp := Nat.add_lt_add_right hlt ((-i).toNat)
      rw [Nat.sub_add_cancel hle'] at htemp
      exact htemp
    have hsum_le : 2 ^ (m - 1) + (-i).toNat ≤ 2 ^ m := by
      rw [h_pow_eq]; exact Nat.add_le_add_left habs _
    exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hsum hsum_le)

/- The exact-buffer primitive roundtrips are derived from the prefix-
tolerant `_append` forms below with `rest := []`, so each read-back fact
is proved exactly once. -/

/-! ## Type-indexed packed codec -/

/- The packed encoder lives in builder form, mirroring the standard codec:
`putPacked` assembles the value with `O(1)` sequencing, and the list form
`encodePacked` is the single materialization (`Builder.toList`).  Scalars
pack at their tight widths, dynamic payloads in place without length words,
array elements at their standard padded widths (`put`, 32-byte words),
tuples as flat concatenation. -/

/-- Element-list packed encoder: each element is standard-encoded (padded
to its 32-byte-word slot) and the encodings concatenate in place. -/
def putPackedElems (t : Ty) : List t.Val → Builder
  | [] => ∅
  | v :: vs => put t v ++ putPackedElems t vs

@[simp] theorem toList_putPackedElems (t : Ty) (vs : List t.Val) :
    (putPackedElems t vs).toList = (vs.map (Spec.encode t)).flatten := by
  induction vs with
  | nil => simp [putPackedElems, Builder.toList_empty]
  | cons v vs ih => simp [putPackedElems, ih, Spec.encode]

mutual
/-- Packed encoder (`abi.encodePacked`), builder form.  Total; the
Solidity-conformant fragment is `PackedSupported`. -/
def putPacked : (t : Ty) → t.Val → Builder
  | .uint m, ⟨n, _⟩   => ofList (encodeUintPacked m.bits n)
  | .int m,  ⟨i, _⟩   => ofList (encodeIntPacked m.bits i)
  | .bool,   b         => ofList (encodeBoolPacked b)
  | .address, ⟨bs, _⟩  => ofList (encodeAddressPacked bs)
  | .bytesN _, ⟨bs, _⟩ => ofList (encodeBytesNPacked bs)
  | .bytes,   bs       => ofList bs
  | .string,  s        => ofList s.val.toUTF8.data.toList
  | .array t, vs       => putPackedElems t vs.val
  | .fixedArray t _ _, ⟨vs, _⟩ => putPackedElems t vs
  | .tuple head tail, (v, vs) => putPacked head v ++ putPackedTuple tail vs

/-- Packed encoder for the flat argument list of a multi-argument
`abi.encodePacked(a, b, …)` call, builder form. -/
def putPackedTuple : (ts : List Ty) → TupleVal ts → Builder
  | [], _ => ∅
  | t :: ts, (v, vs) => putPacked t v ++ putPackedTuple ts vs
end

/-- Packed encoder (type-indexed): the materialization of `putPacked`. -/
def encodePacked (t : Ty) (v : t.Val) : List UInt8 := (putPacked t v).toList

/-- Packed encoder for the flat argument list of a multi-argument
`abi.encodePacked(a, b, …)` call. -/
def encodePackedTuple (ts : List Ty) (vs : TupleVal ts) : List UInt8 :=
  (putPackedTuple ts vs).toList

/- The packed decoder reads with the same `Get2` walkers as the standard
codec, on a purely linear layout: no offset words, no tails — each clause
reads its type's packed extent from the front of the head cursor and
advances it, and dynamic types are rejected (without length words their
extent is ambiguous).  Array elements keep their standard padded widths,
so the element walker *is* the standard codec's `decodeElems` (bound-free
for static element types).  The walkers are structurally recursive (each
call is on a strict subterm), so they stay kernel-reducible and `by
decide` can evaluate packed decodes directly. -/
mutual
/-- Read one packed component as a `Get2` program: static types decode in
place from the head cursor and advance it by the packed size; dynamic
types are rejected.  The tail cursor and frontier are inert in packed
layouts. -/
def decodePackedElem (t : Ty) : Get2 t.Val := ⟨fun head tails E =>
  match t with
  | .uint m => match decodeUintPacked m.bits head with
      | some n => if h : n < 2 ^ m.bits then some ⟨⟨n, h⟩, head.drop (m.bits / 8), tails, E⟩ else none
      | none => none
  | .int m => match decodeIntPacked m.bits head with
      | some i => if h : -((2 ^ (m.bits - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m.bits - 1) : Nat) : Int) then
          some ⟨⟨i, h⟩, head.drop (m.bits / 8), tails, E⟩
        else none
      | none => none
  | .bool => match decodeBoolPacked head with
      | some b => some ⟨b, head.drop 1, tails, E⟩
      | none => none
  | .address => match decodeAddressPacked head with
      | some bs => if h : bs.length = 20 then some ⟨⟨bs, h⟩, head.drop 20, tails, E⟩ else none
      | none => none
  | .bytesN m => match decodeBytesNPacked m.bytes head with
      | some bs => if h : bs.length = m.bytes then some ⟨⟨bs, h⟩, head.drop m.bytes, tails, E⟩ else none
      | none => none
  | .fixedArray t n _ => match t.isStatic with
      | true => match (decodeElems t n).run head (head.drop (n * t.headSize)) (n * t.headSize) with
          | some r => some ⟨r.val, head.drop (n * t.headSize), tails, E⟩
          | none => none
      | false => none
  | .tuple h0 tail =>
      let hsz := h0.packedSize + packedSizeSum tail
      match (decodePackedElem h0).run head (head.drop hsz) hsz with
      | none => none
      | some ⟨v, head', tails', E'⟩ =>
          match (decodePackedTuple tail).run head' tails' E' with
          | none => none
          | some ⟨vs, _, _, _⟩ => some ⟨(v, vs), head.drop hsz, tails, E⟩
  | .bytes | .string | .array _ => none⟩

/-- Read a packed tuple as a `Get2` program, consuming components
sequentially by their packed sizes. -/
def decodePackedTuple : (ts : List Ty) → Get2 (TupleVal ts)
  | [] => pure ()
  | t :: ts => do
      let v ← decodePackedElem t
      let vs ← decodePackedTuple ts
      pure (v, vs)
end

/-- Packed decoder for static types (prefix-tolerant): reads one packed
value from the front of the buffer via the `Get2` walker, discarding the
advanced cursor.  Dynamic types are rejected. -/
def decodePacked (t : Ty) (buf : List UInt8) : Option t.Val :=
  match t.isStatic with
  | true => match (decodePackedElem t).run buf (buf.drop t.packedSize) t.packedSize with
      | some r => some r.val
      | none => none
  | false => none

/-! ## Length lemmas -/

/-- The standard encodings of a static element list occupy `vs.length`
padded (32-byte-word) slots. -/
theorem length_map_encode_static (t : Ty) (hs : t.isStatic = true) :
    (vs : List t.Val) → ((vs.map (Spec.encode t)).map List.length).sum = vs.length * t.headSize
  | [] => by simp
  | v :: vs => by
      simp only [List.map_cons, List.length_cons, List.sum_cons]
      rw [encode_length_static t hs v, length_map_encode_static t hs vs]
      rw [Nat.succ_mul]
      exact Nat.add_comm _ _

mutual
/-- The packed encoding of a static type occupies exactly `packedSize t` bytes. -/
theorem length_encodePacked : (t : Ty) → t.isStatic = true → (v : t.Val) →
    (encodePacked t v).length = t.packedSize
  | .uint m, hs, ⟨n, _⟩ => by
      simp [encodePacked, putPacked, encodeUintPacked, length_encodeBEU, packedSize]
  | .int m, hs, ⟨i, _⟩ => by
      simp only [encodePacked, putPacked, encodeIntPacked, encodeUintPacked, toList_ofList]
      rw [length_encodeBEU]
      simp [packedSize]
  | .bool, hs, b => by simp [encodePacked, putPacked, encodeBoolPacked, packedSize]
  | .address, hs, ⟨bs, hbs⟩ => by
      simp [encodePacked, putPacked, encodeAddressPacked, packedSize, hbs]
  | .bytesN m, hs, ⟨bs, hbs⟩ => by
      simp [encodePacked, putPacked, encodeBytesNPacked, packedSize, hbs]
  | .bytes, hs, v | .string, hs, v | .array _, hs, v => by simp [isStatic] at hs
  | .fixedArray t n _, hs, ⟨vs, hvs⟩ => by
      have hst : t.isStatic = true := by simp only [isStatic] at hs; exact hs
      simp only [encodePacked, putPacked, toList_putPackedElems, List.length_flatten]
      rw [length_map_encode_static t hst vs, hvs, packedSize]
      simp [hst]
  | .tuple head tail, hs, (v, vs) => by
      have hst : head.isStatic = true ∧ allStatic tail = true := by
        simp only [isStatic] at hs
        rw [Bool.and_eq_true] at hs
        exact hs
      have hss : (head.isStatic && allStatic tail) = true := by
        rw [Bool.and_eq_true]
        exact hst
      simp only [encodePacked, putPacked, packedSize, Builder.toList_append, List.length_append]
      rw [if_pos hss]
      change (encodePacked head v).length + (encodePackedTuple tail vs).length =
        head.packedSize + packedSizeSum tail
      rw [length_encodePacked head hst.1 v, length_encodePackedTuple tail hst.2 vs]
termination_by t => 2 * sizeOf t

/-- Length of a packed tuple encoding. -/
theorem length_encodePackedTuple : (ts : List Ty) → allStatic ts = true →
    (vs : TupleVal ts) → (encodePackedTuple ts vs).length = packedSizeSum ts
  | [], _, _ => by simp [encodePackedTuple, putPackedTuple, Builder.toList_empty, packedSizeSum]
  | t :: ts, hs, (v, vs) => by
      simp only [allStatic] at hs
      rw [Bool.and_eq_true] at hs
      obtain ⟨hst, hss⟩ := hs
      simp [encodePackedTuple, putPackedTuple, Builder.toList_append, packedSizeSum]
      change (encodePacked t v).length + (encodePackedTuple ts vs).length =
        t.packedSize + packedSizeSum ts
      rw [length_encodePacked t hst v, length_encodePackedTuple ts hss vs]
termination_by ts => 2 * sizeOf ts + 1
end

/-! ## Prefix-tolerant primitive roundtrips -/

/-- `uintM` packed read-back over an appended suffix. -/
theorem decodeUintPacked_append (m : Nat) (n : Nat) (hm : 0 < m) (h8 : 8 ∣ m) (hn : n < 2 ^ m)
    (rest : List UInt8) :
    decodeUintPacked m (encodeUintPacked m n ++ rest) = some n := by
  unfold decodeUintPacked encodeUintPacked
  have hlen : (encodeBEU (m / 8) n).length = m / 8 := length_encodeBEU _ _
  have htk : (encodeBEU (m / 8) n ++ rest).take (m / 8) = encodeBEU (m / 8) n :=
    take_append_of_length hlen
  rw [if_pos ⟨hm, by omega, by rw [htk, hlen]⟩, htk]
  have hpow := pow_eq_256 m h8
  have hn' : n < 256 ^ (m / 8) := by rw [← hpow]; exact hn
  have := decodeBEU_encodeBEU hn'
  rw [this]

/-- `intM` packed read-back over an appended suffix. -/
theorem decodeIntPacked_append (m : Nat) (hm : 0 < m) (h8 : 8 ∣ m)
    (hl : -((2 ^ (m - 1) : Nat) : Int) ≤ i) (hu : i < ((2 ^ (m - 1) : Nat) : Int))
    (rest : List UInt8) :
    decodeIntPacked m (encodeIntPacked m i ++ rest) = some i := by
  by_cases hi : 0 ≤ i
  · have hn : i.toNat < 2 ^ m := by
      have hlt_nat : i.toNat < 2 ^ (m - 1) := by omega
      exact Nat.lt_of_lt_of_le hlt_nat (Nat.pow_le_pow_right (by decide) (by omega))
    have h_enc : encodeIntPacked m i = encodeUintPacked m i.toNat := by
      rw [encodeIntPacked, if_pos hi]
    rw [h_enc, decodeIntPacked]
    have hdec := decodeUintPacked_append m i.toNat hm h8 hn rest
    rw [hdec]
    dsimp
    apply Option.some.inj
    have hlt_int : (i.toNat : Int) < (2 ^ (m - 1) : Int) := by
      have hp : ((2 ^ (m - 1) : Nat) : Int) = (2 : Int) ^ (m - 1) := by
        simp [Int.natCast_pow]
      omega
    by_cases hcond : (i.toNat : Int) < (2 ^ (m - 1) : Int)
    · rw [if_pos hcond, Int.toNat_of_nonneg hi]
    · exfalso; exact hcond hlt_int
  · have hpos_neg : 0 ≤ -i := by omega
    have heq_toNat : ((-i).toNat : Int) = -i := Int.toNat_of_nonneg hpos_neg
    have h_abs : (-i).toNat ≤ 2 ^ (m - 1) := by omega
    have hrng := twoComp_neg_range (m := m) hm i hi h_abs
    have h_enc : encodeIntPacked m i = encodeUintPacked m (2 ^ m - (-i).toNat) := by
      rw [encodeIntPacked, if_neg hi]
    rw [h_enc, decodeIntPacked]
    have hdec := decodeUintPacked_append m (2 ^ m - (-i).toNat) hm h8 hrng.1 rest
    rw [hdec]
    dsimp
    apply Option.some.inj
    have h_not_lt_int : ¬ (↑(2 ^ m - (-i).toNat) < (2 ^ (m - 1) : Int)) := by
      have hp : ((2 ^ (m - 1) : Nat) : Int) = (2 : Int) ^ (m - 1) := by
        simp [Int.natCast_pow]
      omega
    rw [if_neg h_not_lt_int]
    have hle : (-i).toNat ≤ 2 ^ m :=
      Nat.le_trans h_abs (Nat.pow_le_pow_right (by decide) (by omega))
    have hgoal : (↑(2 ^ m - (-i).toNat) : Int) - ((2 ^ m : Nat) : Int) = i := by
      omega
    simpa using hgoal

/-- `bool` packed read-back over an appended suffix. -/
theorem decodeBoolPacked_append (b : Bool) (rest : List UInt8) :
    decodeBoolPacked (encodeBoolPacked b ++ rest) = some b := by
  cases b <;> simp [encodeBoolPacked, decodeBoolPacked]

/-- `address` packed read-back over an appended suffix. -/
theorem decodeAddressPacked_append (a : List UInt8) (h : a.length = 20) (rest : List UInt8) :
    decodeAddressPacked (encodeAddressPacked a ++ rest) = some a := by
  unfold decodeAddressPacked encodeAddressPacked
  rw [if_pos (by rw [take_append_of_length h, h]), take_append_of_length h]

/-- `bytesN` packed read-back over an appended suffix. -/
theorem decodeBytesNPacked_append (bs : List UInt8) (h : bs.length = n) (rest : List UInt8) :
    decodeBytesNPacked n (encodeBytesNPacked bs ++ rest) = some bs := by
  unfold decodeBytesNPacked encodeBytesNPacked
  rw [if_pos (by rw [take_append_of_length h, h]), take_append_of_length h]

/-! ## Static packed roundtrip -/

/-- For a static element type the head section of its part list is exactly
the flattened standard encodings — the packed array layout. -/
theorem encodeHeads_map_partOf_static (t : Ty) (hs : t.isStatic = true) (vs : List t.Val) :
    encodeHeads E (vs.map (partOf t)) = (vs.map (Spec.encode t)).flatten := by
  induction vs with
  | nil => simp [encodeHeads, putHeads, Builder.toList_empty]
  | cons v vs ih =>
      rw [List.map_cons, partOf_static t v hs, encodeHeads_cons_static, ih]
      rfl

mutual
/-- A static packed component reads back from the front of its own packed
encoding, advancing the head cursor by its packed size; the tail cursor
and frontier pass through untouched. -/
theorem decodePackedElem_append : (t : Ty) → t.isStatic = true →
    (v : t.Val) → (head tails : List UInt8) → (E : Nat) →
    (decodePackedElem t).run (encodePacked t v ++ head) tails E =
      some ⟨v, head, tails, E⟩
  | .uint m, hs, ⟨n, hn⟩, head, tails, E => by
      have hm : 0 < m.bits := by unfold Width.bits; omega
      have h8 : 8 ∣ m.bits := by
        unfold Width.bits
        exact ⟨m.idx.val + 1, by omega⟩
      have hdec := decodeUintPacked_append m.bits n hm h8 hn head
      have hdrop : (encodeUintPacked m.bits n ++ head).drop (m.bits / 8) = head := by
        rw [drop_append_of_length (by rw [encodeUintPacked, length_encodeBEU])]
      simp only [decodePackedElem, encodePacked, putPacked, toList_ofList, hdec]
      rw [hdrop]
      exact dif_pos hn
  | .int m, hs, ⟨i, hi⟩, head, tails, E => by
      have h0 : 0 < m.bits := by unfold Width.bits; omega
      have h8 : 8 ∣ m.bits := by
        unfold Width.bits
        exact ⟨m.idx.val + 1, by omega⟩
      have hdec := decodeIntPacked_append m.bits h0 h8 hi.1 hi.2 head
      have hlen : (encodeIntPacked m.bits i).length = m.bits / 8 := by
        rw [encodeIntPacked, encodeUintPacked, length_encodeBEU]
      have hdrop : (encodeIntPacked m.bits i ++ head).drop (m.bits / 8) = head :=
        drop_append_of_length hlen
      simp only [decodePackedElem, encodePacked, putPacked, toList_ofList, hdec]
      rw [hdrop]
      exact dif_pos hi
  | .bool, hs, b, head, tails, E => by
      have hdrop : (encodeBoolPacked b ++ head).drop 1 = head := by
        rw [drop_append_of_length (by simp [encodeBoolPacked])]
      simp only [decodePackedElem, encodePacked, putPacked, toList_ofList]
      rw [decodeBoolPacked_append b head, hdrop]
  | .address, hs, ⟨bs, hbs⟩, head, tails, E => by
      have hdec := decodeAddressPacked_append bs hbs head
      have hdrop : (encodeAddressPacked bs ++ head).drop 20 = head := by
        rw [drop_append_of_length (by simp [encodeAddressPacked, hbs])]
      simp only [decodePackedElem, encodePacked, putPacked, toList_ofList, hdec]
      rw [hdrop]
      exact dif_pos hbs
  | .bytesN m, hs, ⟨bs, hbs⟩, head, tails, E => by
      have hdec := decodeBytesNPacked_append bs hbs head
      have hdrop : (encodeBytesNPacked bs ++ head).drop m.bytes = head := by
        rw [drop_append_of_length (by simp [encodeBytesNPacked, hbs])]
      simp only [decodePackedElem, encodePacked, putPacked, toList_ofList, hdec]
      rw [hdrop]
      exact dif_pos hbs
  | .bytes, hs, _, _, _, _ | .string, hs, _, _, _, _ | .array _, hs, _, _, _, _ => by
      simp [isStatic] at hs
  | .fixedArray t n _, hs, ⟨vs, hvs⟩, head, tails, E => by
      have hst : t.isStatic = true := by simp only [isStatic] at hs; exact hs
      have hbuf : (vs.map (Spec.encode t)).flatten ++ head =
          encodeHeads (n * t.headSize) (vs.map (partOf t)) ++ head := by
        rw [encodeHeads_map_partOf_static t hst vs]
      have hlen_heads : (encodeHeads (n * t.headSize) (vs.map (partOf t))).length =
          n * t.headSize := by
        rw [length_encodeHeads, headSizes_map_partOf_any t vs, hvs]
      simp only [decodePackedElem, encodePacked, putPacked, toList_putPackedElems, hst]
      rw [hbuf, drop_append_of_length hlen_heads]
      have h := decodeElems_static_append t hst vs n hvs (n * t.headSize) head head
      rw [h]
  | .tuple h0 tail, hs, (vh, vtail), head, tails, E => by
      have hst : h0.isStatic = true ∧ allStatic tail = true := by
        simp only [isStatic] at hs
        rw [Bool.and_eq_true] at hs
        exact hs
      have hbuf : encodePacked (tuple h0 tail) (vh, vtail) ++ head =
          encodePacked h0 vh ++ (encodePackedTuple tail vtail ++ head) := by
        simp [encodePacked, putPacked, encodePackedTuple, List.append_assoc]
      have hlen : (encodePacked h0 vh ++ encodePackedTuple tail vtail).length =
          h0.packedSize + packedSizeSum tail := by
        rw [List.length_append, length_encodePacked h0 hst.1 vh,
          length_encodePackedTuple tail hst.2 vtail]
      have hdrop : (encodePacked h0 vh ++ (encodePackedTuple tail vtail ++ head)).drop
          (h0.packedSize + packedSizeSum tail) = head := by
        rw [← List.append_assoc, drop_append_of_length hlen]
      rw [hbuf]
      rw [decodePackedElem]
      simp only []
      rw [hdrop]
      rw [decodePackedElem_append h0 hst.1 vh (encodePackedTuple tail vtail ++ head) head
        (h0.packedSize + packedSizeSum tail)]
      simp
      rw [decodePackedTuple_append tail hst.2 vtail (h0.packedSize + packedSizeSum tail) head head]
termination_by t => 4 * sizeOf t

/-- A packed tuple reads back from its flattened packed encodings,
advancing the head cursor by the tuple's packed size. -/
theorem decodePackedTuple_append : (ts : List Ty) → allStatic ts = true →
    (vs : TupleVal ts) → (E : Nat) → (head tails : List UInt8) →
    (decodePackedTuple ts).run (encodePackedTuple ts vs ++ head) tails E =
      some ⟨vs, head, tails, E⟩
  | [], _, _, E, head, tails => by
      simp [decodePackedTuple, Get2.pure_run, encodePackedTuple, putPackedTuple, Builder.toList_empty]
  | t :: ts, hs, (v, vs), E, head, tails => by
      simp only [allStatic] at hs
      rw [Bool.and_eq_true] at hs
      obtain ⟨hst, hss⟩ := hs
      simp only [decodePackedTuple, Get2.bind_run, Get2.pure_run]
      have hbuf : encodePackedTuple (t :: ts) (v, vs) ++ head =
          encodePacked t v ++ (encodePackedTuple ts vs ++ head) := by
        rw [encodePackedTuple, putPackedTuple, Builder.toList_append, ← encodePacked,
          ← encodePackedTuple, List.append_assoc]
      rw [hbuf, decodePackedElem_append t hst v (encodePackedTuple ts vs ++ head) tails E]
      dsimp only []
      rw [decodePackedTuple_append ts hss vs E head tails]
termination_by ts => 4 * sizeOf ts + 1
end

/-- **Static packed roundtrip, prefix form**: a static value decodes from the front
of its own packed encoding followed by an arbitrary suffix. -/
theorem decodePacked_encodePacked_append (t : Ty) (hs : t.isStatic = true) (v : t.Val) (rest : List UInt8) : decodePacked t (encodePacked t v ++ rest) = some v := by
  simp only [decodePacked, hs]
  rw [drop_append_of_length (length_encodePacked t hs v)]
  rw [decodePackedElem_append t hs v rest rest (packedSize t)]

/-- **Static packed roundtrip**: every static type decodes its own packed encoding
without any side condition. -/
theorem roundtrip_packed_static (t : Ty) (hs : t.isStatic = true) (v : t.Val) :
    decodePacked t (encodePacked t v) = some v := by
  have h := decodePacked_encodePacked_append t hs v []
  rwa [List.append_nil] at h

end EvmAbi
