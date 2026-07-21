import EvmAbi.Ty
import EvmAbi.Bytes
import EvmAbi.Static
import EvmAbi.Codec
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
dynamic types.
-/

namespace EvmAbi

open Ty
open Binary

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
  | .fixedArray t _ => PackedScalar t
  | t => PackedScalar t

/-! `Nat.cast` lemmas for `Nat → Int` that are essential for mixed `Nat`/`Int` reasoning. -/

namespace NatCast

@[simp] theorem add (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  induction a with
  | zero => simp
  | succ a ih => simp [Nat.succ_add, ih]; omega

@[simp] theorem one : ((1 : Nat) : Int) = (1 : Int) := rfl

@[simp] theorem succ (a : Nat) : ((Nat.succ a : Nat) : Int) = (a : Int) + (1 : Int) := by
  rw [Nat.succ_eq_add_one, add, one]

@[simp] theorem mul (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, add, ih, succ a]
    calc
      (a : Int) * (b : Int) + (b : Int) = (b : Int) * (a : Int) + (b : Int) := by rw [Int.mul_comm]
      _ = (b : Int) * (a : Int) + (b : Int) * 1 := by simp
      _ = (b : Int) * ((a : Int) + 1) := by rw [Int.mul_add]
      _ = ((a : Int) + 1) * (b : Int) := by rw [Int.mul_comm]

/-- `Nat.cast` distributes over subtraction when `b ≤ a`. -/
theorem sub {a b : Nat} (h : b ≤ a) : ((a - b : Nat) : Int) = (a : Int) - (b : Int) := by
  have hsub := Nat.sub_add_cancel h
  have hcast : (((a - b) + b : Nat) : Int) = (a : Int) :=
    congrArg (fun (x : Nat) => (x : Int)) hsub
  rw [add (a - b) b] at hcast
  omega

@[simp] theorem pow (a n : Nat) : ((a ^ n : Nat) : Int) = ((a : Int) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.pow_succ, Int.pow_succ, mul, ih]

/-! ## `Nat.cast` of order relations -/

@[simp] theorem lt_iff {a b : Nat} : (a : Int) < (b : Int) ↔ a < b := by
  constructor <;> intro h <;> omega

@[simp] theorem le_iff {a b : Nat} : (a : Int) ≤ (b : Int) ↔ a ≤ b := by
  constructor <;> intro h <;> omega

end NatCast


/-! ## Primitive packed encoders -/

def encodeUintPacked (m : Nat) (n : Nat) : List UInt8 := encodeBEU (m / 8) n

def encodeIntPacked (m : Nat) (i : Int) : List UInt8 :=
  encodeUintPacked m (if 0 ≤ i then i.toNat else 2 ^ m - (-i).toNat)

def encodeBoolPacked (b : Bool) : List UInt8 := [if b then 1 else 0]

def encodeAddressPacked (a : Nat) : List UInt8 := encodeUintPacked 160 a

def encodeBytesNPacked (bs : List UInt8) : List UInt8 := bs

/-! ## Primitive packed decoders -/

def decodeUintPacked (m : Nat) (buf : List UInt8) : Option Nat :=
  if buf.length ≥ m / 8 then some (decodeBEU (buf.take (m / 8))) else none

def decodeIntPacked (m : Nat) (buf : List UInt8) : Option Int :=
  (decodeUintPacked m buf).map fun n =>
    if n < 2 ^ (m - 1) then (n : Int) else (n : Int) - ((2 ^ m : Nat) : Int)

def decodeBoolPacked (buf : List UInt8) : Option Bool :=
  match buf with | 0 :: _ => some false | 1 :: _ => some true | _ => none

def decodeAddressPacked (buf : List UInt8) : Option Nat := decodeUintPacked 160 buf

def decodeBytesNPacked (n : Nat) (buf : List UInt8) : Option (List UInt8) :=
  if buf.length ≥ n then some (buf.take n) else none

/-! ## Helpers -/

private theorem pow_eq_256 (m : Nat) (h8 : 8 ∣ m) : 2 ^ m = 256 ^ (m / 8) := by
  have : 8 * (m / 8) = m := Nat.mul_div_cancel' h8
  calc
    2 ^ m = 2 ^ (8 * (m / 8)) := by rw [this]
    _ = (2 ^ 8) ^ (m / 8) := by rw [Nat.pow_mul]
    _ = 256 ^ (m / 8) := by rw [show (2 : Nat) ^ 8 = 256 by decide]

/- The exact-buffer primitive roundtrips are derived from the prefix-
tolerant `_append` forms below with `rest := []`, so each read-back fact
is proved exactly once. -/

/-! ## Type-indexed packed codec -/

/- The packed encoder: scalars at their tight widths, dynamic payloads in
place without length words, array elements at their standard padded
widths (`encode`, 32-byte words), tuples as flat concatenation. -/
mutual
/-- Packed encoder (`abi.encodePacked`).  Total; the Solidity-conformant
fragment is `PackedSupported`. -/
def encodePacked : (t : Ty) → t.Val → List UInt8
  | .uint m, ⟨n, _⟩ => encodeUintPacked m n
  | .int m, ⟨i, _⟩ => encodeIntPacked m i
  | .bool, b => encodeBoolPacked b
  | .address, ⟨n, _⟩ => encodeAddressPacked n
  | .bytesN _, ⟨bs, _⟩ => encodeBytesNPacked bs
  | .bytes, bs => bs
  | .string, s => s.toUTF8.data.toList
  | .array t, vs => (vs.map (encode t)).flatten
  | .fixedArray t _, ⟨vs, _⟩ => (vs.map (encode t)).flatten
  | .tuple ts, vs => encodePackedTuple ts vs
termination_by t => (sizeOf t, 0)

/-- Packed encoder for the flat argument list of a multi-argument
`abi.encodePacked(a, b, …)` call. -/
def encodePackedTuple : (ts : List Ty) → TupleVal ts → List UInt8
  | [], _ => []
  | t :: ts, (v, vs) => encodePacked t v ++ encodePackedTuple ts vs
termination_by ts => (sizeOf ts, 1)
end

/-- Read `n` consecutive packed array elements of type `t` from the front
of the buffer.  Packed array elements carry their standard padded layout,
so each is read by the standard `decode` and occupies `t.headSize` bytes. -/
def decodePackedElems (t : Ty) : (n : Nat) → List UInt8 →
    Option { vs : List t.Val // vs.length = n }
  | 0, _ => some ⟨[], rfl⟩
  | n + 1, buf => match decode t buf with
    | none => none
    | some v => match decodePackedElems t n (buf.drop t.headSize) with
      | none => none
      | some ⟨vs, h⟩ => some ⟨v :: vs, by simp [List.length_cons, h]⟩

/- The packed decoder: each clause reads its type's packed extent from the
front of the buffer and ignores the rest.  Dynamic types are rejected —
without length words their extent is ambiguous. -/
mutual
/-- Packed decoder for static types (prefix-tolerant). -/
def decodePacked : (t : Ty) → List UInt8 → Option t.Val
  | .uint m, buf => match decodeUintPacked m buf with
    | some n => if h : n < 2 ^ m then some ⟨n, h⟩ else none
    | none => none
  | .int m, buf => match decodeIntPacked m buf with
    | some i => if h : -((2 ^ (m - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m - 1) : Nat) : Int) then
        some ⟨i, h⟩
      else none
    | none => none
  | .bool, buf => decodeBoolPacked buf
  | .address, buf => match decodeAddressPacked buf with
    | some n => if h : n < 2 ^ 160 then some ⟨n, h⟩ else none
    | none => none
  | .bytesN m, buf => match decodeBytesNPacked m buf with
    | some bs => if h : bs.length = m then some ⟨bs, h⟩ else none
    | none => none
  | .fixedArray t n, buf => match t.IsStatic with
    | true => decodePackedElems t n buf
    | false => none
  | .tuple ts, buf => decodePackedTuple ts buf
  | _, _ => none
termination_by t => (sizeOf t, 0)

/-- Read a tuple from the front of the buffer, consuming components
sequentially by their packed sizes. -/
def decodePackedTuple : (ts : List Ty) → List UInt8 → Option (TupleVal ts)
  | [], _ => some ()
  | t :: ts, buf => match decodePacked t buf with
    | none => none
    | some v => (decodePackedTuple ts (buf.drop t.packedSize)).map (v, ·)
termination_by ts => (sizeOf ts, 1)
end

/-! ## Length lemmas -/

mutual
/-- The packed encoding of a static type occupies exactly `packedSize t` bytes. -/
theorem length_encodePacked : (t : Ty) → t.IsStatic = true → t.Valid → (v : t.Val) →
    (encodePacked t v).length = t.packedSize
  | .uint m, hs, hv, ⟨n, _⟩ => by simp [encodePacked, encodeUintPacked, length_encodeBEU, packedSize]
  | .int m, hs, hv, ⟨i, _⟩ => by
      simp only [encodePacked, encodeIntPacked, encodeUintPacked]
      rw [length_encodeBEU]
      simp [packedSize]
  | .bool, hs, hv, b => by simp [encodePacked, encodeBoolPacked, packedSize]
  | .address, hs, hv, ⟨n, _⟩ => by
      simp only [encodePacked, encodeAddressPacked, encodeUintPacked]
      rw [length_encodeBEU]
      simp [packedSize]
  | .bytesN m, hs, hv, ⟨bs, hbs⟩ => by simp [encodePacked, encodeBytesNPacked, packedSize, hbs]
  | .bytes, hs, hv, v | .string, hs, hv, v | .array _, hs, hv, v => by simp [IsStatic] at hs
  | .fixedArray t n, hs, hv, ⟨vs, hvs⟩ => by
      have hst : t.IsStatic = true := by simp only [IsStatic] at hs; exact hs
      have hvt : t.Valid := hv
      simp only [encodePacked, List.length_flatten]
      have hmap : ∀ (vs : List t.Val),
          ((vs.map (encode t)).map List.length).sum = vs.length * t.headSize := by
        intro vs
        induction vs with
        | nil => simp
        | cons v vs ih =>
          simp only [List.map_cons, List.length_cons, List.sum_cons]
          rw [encode_length_static t hst hvt v, ih]
          rw [Nat.succ_mul]
          exact Nat.add_comm _ _
      rw [hmap, hvs, packedSize]
  | .tuple ts, hs, hv, vs => by
      have hss : allStatic ts = true := by simp only [IsStatic] at hs; exact hs
      have hvts : AllValid ts := hv
      simp only [encodePacked, packedSize]
      exact length_encodePackedTuple ts hss hvts vs
termination_by t => 2 * sizeOf t

/-- Length of a packed tuple encoding. -/
theorem length_encodePackedTuple : (ts : List Ty) → allStatic ts = true → AllValid ts →
    (vs : TupleVal ts) → (encodePackedTuple ts vs).length = packedSizeSum ts
  | [], _, _, _ => by simp [encodePackedTuple, packedSizeSum]
  | t :: ts, hs, hv, (v, vs) => by
      simp only [allStatic] at hs
      rw [Bool.and_eq_true] at hs
      obtain ⟨hst, hss⟩ := hs
      obtain ⟨hvt, hvs⟩ := hv
      simp only [encodePackedTuple, List.length_append, packedSizeSum]
      rw [length_encodePacked t hst hvt v, length_encodePackedTuple ts hss hvs vs]
termination_by ts => 2 * sizeOf ts + 1
end

/-! ## Prefix-tolerant primitive roundtrips -/

/-- `uintM` packed read-back over an appended suffix. -/
theorem decodeUintPacked_append (m : Nat) (n : Nat) (h8 : 8 ∣ m) (hn : n < 2 ^ m)
    (rest : List UInt8) :
    decodeUintPacked m (encodeUintPacked m n ++ rest) = some n := by
  unfold decodeUintPacked encodeUintPacked
  have hlen : (encodeBEU (m / 8) n).length = m / 8 := length_encodeBEU _ _
  have hge : (encodeBEU (m / 8) n ++ rest).length ≥ m / 8 := by
    rw [List.length_append, hlen]; omega
  have htk : (encodeBEU (m / 8) n ++ rest).take (m / 8) = encodeBEU (m / 8) n :=
    take_append_of_length hlen
  rw [if_pos hge, htk]
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
      have hlt_nat : i.toNat < 2 ^ (m - 1) := by
        have hpos : (i.toNat : Int) = i := Int.toNat_of_nonneg hi
        have hlt_int : (i.toNat : Int) < ((2 ^ (m - 1) : Nat) : Int) := by rwa [hpos]
        exact NatCast.lt_iff.mp hlt_int
      exact Nat.lt_of_lt_of_le hlt_nat (Nat.pow_le_pow_right (by decide) (by omega))
    have h_enc : encodeIntPacked m i = encodeUintPacked m i.toNat := by
      rw [encodeIntPacked, if_pos hi]
    rw [h_enc, decodeIntPacked]
    have hdec := decodeUintPacked_append m i.toNat h8 hn rest
    rw [hdec]
    dsimp
    apply Option.some.inj
    have hlt_int : (i.toNat : Int) < (2 ^ (m - 1) : Int) := by
      have hpos : (i.toNat : Int) = i := Int.toNat_of_nonneg hi
      have hlt_int' : (i.toNat : Int) < ((2 ^ (m - 1) : Nat) : Int) := by rwa [hpos]
      simpa using hlt_int'
    by_cases hcond : (i.toNat : Int) < (2 ^ (m - 1) : Int)
    · rw [if_pos hcond, Int.toNat_of_nonneg hi]
    · exfalso; exact hcond hlt_int
  · have hpos_neg : 0 ≤ -i := by omega
    have heq_toNat : ((-i).toNat : Int) = -i := Int.toNat_of_nonneg hpos_neg
    have h_abs : (-i).toNat ≤ 2 ^ (m - 1) := by
      have hle_int : -i ≤ ((2 ^ (m - 1) : Nat) : Int) := by omega
      rw [← heq_toNat] at hle_int
      exact NatCast.le_iff.mp hle_int
    have hpos_abs : 0 < (-i).toNat := by
      apply Nat.pos_of_ne_zero; intro hz
      have hle0 : -i ≤ 0 := Int.toNat_eq_zero.mp hz; omega
    have hpos_pow : 0 < 2 ^ m := by
      have h := Nat.one_le_pow m 2 (by decide); omega
    have hn : 2 ^ m - (-i).toNat < 2 ^ m := by
      apply Nat.sub_lt <;> assumption
    have h_enc : encodeIntPacked m i = encodeUintPacked m (2 ^ m - (-i).toNat) := by
      rw [encodeIntPacked, if_neg hi]
    rw [h_enc, decodeIntPacked]
    have hdec := decodeUintPacked_append m (2 ^ m - (-i).toNat) h8 hn rest
    rw [hdec]
    dsimp
    apply Option.some.inj
    have h_not_lt : ¬ (2 ^ m - (-i).toNat : Nat) < 2 ^ (m - 1) := by
      have h_pow_eq : 2 ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
        calc
          2 ^ m = 2 ^ ((m - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
          _ = 2 ^ (m - 1) * 2 := by rw [Nat.pow_succ]
          _ = 2 ^ (m - 1) + 2 ^ (m - 1) := by omega
      intro hlt
      have hsum : 2 ^ m < 2 ^ (m - 1) + (-i).toNat := by
        have htemp := Nat.add_lt_add_right hlt ((-i).toNat)
        have hle' : (-i).toNat ≤ 2 ^ m :=
          Nat.le_trans h_abs (Nat.pow_le_pow_right (by decide) (by omega))
        rw [Nat.sub_add_cancel hle'] at htemp; exact htemp
      have hsum_le : 2 ^ (m - 1) + (-i).toNat ≤ 2 ^ m := by
        rw [h_pow_eq]; exact Nat.add_le_add_left h_abs _
      exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hsum hsum_le)
    have h_not_lt_int' : ¬ (↑(2 ^ m - (-i).toNat) < (2 ^ (m - 1) : Int)) := by
      simpa using mt NatCast.lt_iff.mp h_not_lt
    rw [if_neg h_not_lt_int']
    have hle : (-i).toNat ≤ 2 ^ m :=
      Nat.le_trans h_abs (Nat.pow_le_pow_right (by decide) (by omega))
    have hcast := NatCast.sub hle
    have hgoal : (↑(2 ^ m - (-i).toNat) : Int) - ((2 ^ m : Nat) : Int) = i := by
      rw [hcast, heq_toNat]; omega
    simpa using hgoal

/-- `bool` packed read-back over an appended suffix. -/
theorem decodeBoolPacked_append (b : Bool) (rest : List UInt8) :
    decodeBoolPacked (encodeBoolPacked b ++ rest) = some b := by
  cases b <;> simp [encodeBoolPacked, decodeBoolPacked]

/-- `address` packed read-back over an appended suffix. -/
theorem decodeAddressPacked_append (a : Nat) (h : a < 2 ^ 160) (rest : List UInt8) :
    decodeAddressPacked (encodeAddressPacked a ++ rest) = some a :=
  decodeUintPacked_append 160 a ⟨20, by decide⟩ h rest

/-- `bytesN` packed read-back over an appended suffix. -/
theorem decodeBytesNPacked_append (bs : List UInt8) (h : bs.length = n) (rest : List UInt8) :
    decodeBytesNPacked n (encodeBytesNPacked bs ++ rest) = some bs := by
  unfold decodeBytesNPacked encodeBytesNPacked
  rw [if_pos (by rw [List.length_append]; omega), take_append_of_length h]

/-! ## Exact-buffer primitive roundtrips (corollaries) -/

theorem decodeUintPacked_encodeUintPacked (m : Nat) (n : Nat) (h8 : 8 ∣ m) (hn : n < 2 ^ m) :
    decodeUintPacked m (encodeUintPacked m n) = some n := by
  simpa using decodeUintPacked_append m n h8 hn []

theorem decodeIntPacked_encodeIntPacked (m : Nat) (hm : 0 < m) (h8 : 8 ∣ m)
    (hl : -((2 ^ (m - 1) : Nat) : Int) ≤ i) (hu : i < ((2 ^ (m - 1) : Nat) : Int)) :
    decodeIntPacked m (encodeIntPacked m i) = some i := by
  simpa using decodeIntPacked_append m hm h8 hl hu []

theorem decodeBoolPacked_encodeBoolPacked (b : Bool) :
    decodeBoolPacked (encodeBoolPacked b) = some b := by
  simpa using decodeBoolPacked_append b []

theorem decodeAddressPacked_encodeAddressPacked (a : Nat) (h : a < 2 ^ 160) :
    decodeAddressPacked (encodeAddressPacked a) = some a := by
  simpa using decodeAddressPacked_append a h []

theorem decodeBytesNPacked_encodeBytesNPacked (bs : List UInt8) (h : bs.length = n) :
    decodeBytesNPacked n (encodeBytesNPacked bs) = some bs := by
  simpa using decodeBytesNPacked_append bs h []

/-! ## Static packed roundtrip -/

/-- Element lists decode from their own padded-element encoding followed by
a suffix — a direct consequence of the standard codec's static prefix
roundtrip, since packed array elements *are* standard-encoded. -/
theorem decodePackedElems_append (t : Ty) (hs : t.IsStatic = true) (hv : t.Valid)
    (vs : List t.Val) (n : Nat) (hn : vs.length = n) (rest : List UInt8) :
    decodePackedElems t n ((vs.map (encode t)).flatten ++ rest) = some ⟨vs, hn⟩ := by
  induction vs generalizing n with
  | nil =>
      subst hn
      simp [List.map_nil, List.flatten_nil, decodePackedElems]
  | cons v vs ih =>
      have hn' : n = vs.length + 1 := by rw [← hn, List.length_cons]
      subst hn'
      simp only [List.map_cons, List.flatten_cons, List.append_assoc, decodePackedElems]
      rw [decode_encode_append_static t hs hv v _]
      rw [drop_append_of_length (encode_length_static t hs hv v)]
      rw [ih _ rfl]

mutual
/-- **Static packed roundtrip, prefix form**: a static value decodes from the front
of its own packed encoding followed by an arbitrary suffix. -/
theorem decodePacked_encodePacked_append : (t : Ty) → t.IsStatic = true → t.Valid →
    (v : t.Val) → (rest : List UInt8) → decodePacked t (encodePacked t v ++ rest) = some v
  | .uint m, hs, hv, ⟨n, hn⟩, rest => by
      have h8 : 8 ∣ m := Nat.dvd_of_mod_eq_zero hv.2.2
      have hdec := decodeUintPacked_append m n h8 hn rest
      simp only [encodePacked, decodePacked]
      rw [hdec]
      exact dif_pos hn
  | .int m, hs, hv, ⟨i, hi⟩, rest => by
      have h0 : 0 < m := by have h8 := hv.1; omega
      have h8 : 8 ∣ m := Nat.dvd_of_mod_eq_zero hv.2.2
      have hdec := decodeIntPacked_append m h0 h8 hi.1 hi.2 rest
      simp only [encodePacked, decodePacked]
      rw [hdec]
      exact dif_pos hi
  | .bool, hs, hv, b, rest => by
      simp only [encodePacked, decodePacked]
      exact decodeBoolPacked_append b rest
  | .address, hs, hv, ⟨n, hn⟩, rest => by
      have hdec := decodeAddressPacked_append n hn rest
      simp only [encodePacked, decodePacked]
      rw [hdec]
      exact dif_pos hn
  | .bytesN m, hs, hv, ⟨bs, hbs⟩, rest => by
      have hdec := decodeBytesNPacked_append bs hbs rest
      simp only [encodePacked, decodePacked]
      rw [hdec]
      exact dif_pos hbs
  | .bytes, hs, _, _, _ | .string, hs, _, _, _ | .array _, hs, _, _, _ => by
      simp [IsStatic] at hs
  | .fixedArray t n, hs, hv, ⟨vs, hvs⟩, rest => by
      have hst : t.IsStatic = true := by simp only [IsStatic] at hs; exact hs
      have hvt : t.Valid := hv
      simp only [encodePacked, decodePacked, hst]
      have h := decodePackedElems_append t hst hvt vs n hvs rest
      simpa using h
  | .tuple ts, hs, hv, vs, rest => by
      have hss : allStatic ts = true := by simp only [IsStatic] at hs; exact hs
      have hvts : AllValid ts := hv
      simp only [encodePacked, decodePacked]
      have h := decodePackedTuple_append ts hss hvts vs rest
      simpa using h
termination_by t => 4 * sizeOf t

/-- Tuples decode from their own packed encoding followed by a suffix. -/
theorem decodePackedTuple_append : (ts : List Ty) → allStatic ts = true → AllValid ts →
    (vs : TupleVal ts) → (rest : List UInt8) →
    decodePackedTuple ts (encodePackedTuple ts vs ++ rest) = some vs
  | [], _, _, _, _ => by simp [encodePackedTuple, decodePackedTuple]
  | t :: ts, hs, hv, (v, vs), rest => by
      simp only [allStatic] at hs
      rw [Bool.and_eq_true] at hs
      obtain ⟨hst, hss⟩ := hs
      obtain ⟨hvt, hvs⟩ := hv
      simp only [encodePackedTuple, decodePackedTuple]
      rw [List.append_assoc]
      rw [decodePacked_encodePacked_append t hst hvt v _]
      have hlen := length_encodePacked t hst hvt v
      rw [drop_append_of_length hlen]
      rw [decodePackedTuple_append ts hss hvs vs rest]
      rfl
termination_by ts => 4 * sizeOf ts + 2
end

/-- **Static packed roundtrip**: every static type decodes its own packed encoding
without any side condition. -/
theorem roundtrip_packed_static (t : Ty) (hs : t.IsStatic = true) (hv : t.Valid) (v : t.Val) :
    decodePacked t (encodePacked t v) = some v := by
  have h := decodePacked_encodePacked_append t hs hv v []
  rwa [List.append_nil] at h

end EvmAbi
