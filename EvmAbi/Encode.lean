import EvmAbi.Builder
import EvmAbi.Codec
import EvmAbi.Canonical

/-!
# EvmAbi.Encode

The **executable ABI encoder** (roadmap node 14): a `Builder`-valued mirror of
`EvmAbi.Codec`'s `encode`, run into a contiguous `ByteArray` in one pass.

`encode : (t : Ty) → t.Val → List UInt8` is the specification.  It concatenates
with `++` at every level, so a value nested `d` deep has its bytes re-copied
`d` times, on a representation that spends a cons cell and a boxed `UInt8` per
byte.  This module keeps that definition as the spec and adds a fast one
beside it: `encodeB` / `partOfB` / `partsOfTupleB` mirror `encode` / `partOf` /
`partsOfTuple` clause for clause, and `PartB` / `encodePartsB` mirror the
`EvmAbi.Parts` head/tail layer, with `PartB.toPart` as their denotation.
Every `++` becomes an `O(1)` node, string payloads stay `ByteArray` chunks,
and padding is a `zeros` node rather than a materialised `List.replicate`.

One theorem ties the two together:

```
toList_encodeB : (encodeB t v).toList = encode t v
```

That is the whole point.  Once the encoders agree at the denotation level,
*every* theorem already proved about `encode` — roundtrip, injectivity,
canonical validation — transports to `encodeByteArray t v = (encodeB t v).run`
by rewriting, with no new proof; the transported statements are collected at
the end of this module.

Note where `Builder`'s cached size earns its keep: `encodeHeadsB` asks every
dynamic part for its tail's length in order to write the offset word, and
`Builder.size` answers in `O(1)`.  Measuring the tree instead would restore
the very cost this module removes.
-/
namespace EvmAbi

open Ty
open Binary

/-! ## the head/tail combinator over builders

`PartB` is `Part` with `Builder` fields; `PartB.toPart` is its denotation,
and each `*B` function below denotes the corresponding function of
`EvmAbi.Parts`. -/

/-- A `Part` whose head and tail are builders. -/
structure PartB where
  /-- Bytes contributed to the head section. -/
  head : Builder
  /-- Bytes contributed to the tail section (empty for static parts). -/
  tail : Builder
  /-- Whether this part is dynamic (head is an offset word, tail is the data). -/
  isDyn : Bool

namespace PartB

/-- The `Part` a `PartB` denotes. -/
def toPart (p : PartB) : Part := ⟨p.head.toList, p.tail.toList, p.isDyn⟩

/-- Bytes this part occupies in the head section (no list is built). -/
def headSize : PartB → Nat
  | ⟨head, _, false⟩ => head.size
  | ⟨_, _, true⟩ => 32

@[simp] theorem headSize_toPart (p : PartB) : p.toPart.headSize = p.headSize := by
  obtain ⟨head, tail, isDyn⟩ := p
  cases isDyn <;> simp [toPart, Part.headSize, headSize]

end PartB

/-- Total size of the head section.  There is no `tailSizesB`: `encodeHeadsB`
reads each tail's length straight off its `Builder`. -/
def headSizesB : List PartB → Nat
  | [] => 0
  | p :: ps => p.headSize + headSizesB ps

@[simp] theorem headSizesB_eq (ps : List PartB) :
    headSizesB ps = headSizes (ps.map PartB.toPart) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [headSizesB, headSizes, ih]

/-- Encode the head section; `acc` is the byte offset of the current part's
tail (cf. `encodeHeads`). -/
def encodeHeadsB (acc : Nat) : List PartB → Builder
  | [] => .empty
  | ⟨head, _, false⟩ :: ps => head ++ encodeHeadsB acc ps
  | ⟨_, tail, true⟩ :: ps => .bytes (encodeUint acc) ++ encodeHeadsB (acc + tail.size) ps

/-- Encode the tail section: the dynamic tails, in order (cf. `encodeTails`). -/
def encodeTailsB : List PartB → Builder
  | [] => .empty
  | ⟨_, _, false⟩ :: ps => encodeTailsB ps
  | ⟨_, tail, true⟩ :: ps => tail ++ encodeTailsB ps

/-- Full tuple encoding as a builder (cf. `encodeParts`). -/
def encodePartsB (ps : List PartB) : Builder :=
  encodeHeadsB (headSizesB ps) ps ++ encodeTailsB ps

@[simp] theorem toList_encodeHeadsB (acc : Nat) (ps : List PartB) :
    (encodeHeadsB acc ps).toList = encodeHeads acc (ps.map PartB.toPart) := by
  induction ps generalizing acc with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨head, tail, isDyn⟩ := p
      cases isDyn <;> simp [encodeHeadsB, encodeHeads, PartB.toPart, ih]

@[simp] theorem toList_encodeTailsB (ps : List PartB) :
    (encodeTailsB ps).toList = encodeTails (ps.map PartB.toPart) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨head, tail, isDyn⟩ := p
      cases isDyn <;> simp [encodeTailsB, encodeTails, PartB.toPart, ih]

@[simp] theorem toList_encodePartsB (ps : List PartB) :
    (encodePartsB ps).toList = encodeParts (ps.map PartB.toPart) := by
  simp [encodePartsB, encodeParts]

/-! ## the builder-valued encoder

A clause-for-clause mirror of the `encode` family of `EvmAbi.Codec`, with
the same termination measures. -/

mutual
/-- ABI encoder into a `Builder` — the executable counterpart of `encode`. -/
def encodeB : (t : Ty) → t.Val → Builder
  | .uint _, ⟨n, _⟩    => .bytes (encodeUint n)
  | .int _, ⟨i, _⟩     => .bytes (encodeInt i)
  | .bool, b           => .bytes (encodeBool b)
  | .address, ⟨n, _⟩   => .bytes (encodeAddress n)
  | .bytesN _, ⟨bs, _⟩ => .bytes bs ++ .zeros (32 - bs.length)
  | .bytes, ⟨bs, _⟩    =>
      .bytes (encodeUint bs.length) ++ (.bytes bs ++ .zeros ((32 - bs.length % 32) % 32))
  | .string, ⟨s, _⟩    =>
      .bytes (encodeUint s.toUTF8.size) ++
        (.chunk s.toUTF8 ++ .zeros ((32 - s.toUTF8.size % 32) % 32))
  | .array t, ⟨vs, _⟩  => .bytes (encodeUint vs.length) ++ encodePartsB (vs.map (partOfB t))
  | .fixedArray t _, ⟨vs, _⟩ => encodePartsB (vs.map (partOfB t))
  | .tuple ts, vs      => encodePartsB (partsOfTupleB ts vs)
termination_by t => (sizeOf t, 0)

/-- A value seen as a builder-valued head/tail part (cf. `partOf`). -/
def partOfB (t : Ty) (v : t.Val) : PartB :=
  match t.IsStatic with
  | true => ⟨encodeB t v, .empty, false⟩
  | false => ⟨.empty, encodeB t v, true⟩
termination_by (sizeOf t, 1)

/-- A tuple value seen as a list of builder-valued parts (cf. `partsOfTuple`). -/
def partsOfTupleB : (ts : List Ty) → TupleVal ts → List PartB
  | [], _ => []
  | t :: ts, (v, vs) => partOfB t v :: partsOfTupleB ts vs
termination_by ts => (sizeOf ts, 2)
end

/-- `partOfB` of a static value is the inline head part. -/
theorem partOfB_static (t : Ty) (v : t.Val) (h : t.IsStatic = true) :
    partOfB t v = ⟨encodeB t v, .empty, false⟩ := by
  simp [partOfB, h]

/-- `partOfB` of a dynamic value is the offset-word head plus tail part. -/
theorem partOfB_dynamic (t : Ty) (v : t.Val) (h : t.IsStatic = false) :
    partOfB t v = ⟨.empty, encodeB t v, true⟩ := by
  simp [partOfB, h]

/-! ## the bridge

The builder encoder denotes the specification encoder.  Everything else in
this module is a corollary. -/

mutual
/-- **The bridge**: the builder-valued encoder denotes `encode`. -/
theorem toList_encodeB : (t : Ty) → (v : t.Val) → (encodeB t v).toList = encode t v
  | .uint _, ⟨n, _⟩ => by simp [encodeB, encode]
  | .int _, ⟨i, _⟩ => by simp only [encodeB, encode, Builder.toList_bytes]
  | .bool, b => by simp [encodeB, encode]
  | .address, ⟨n, _⟩ => by simp [encodeB, encode]
  | .bytesN _, ⟨bs, _⟩ => by simp [encodeB, encode, encodeBytesN]
  | .bytes, ⟨bs, _⟩ => by
      simp [encodeB, encode, encodeBytes, pad32]
  | .string, ⟨s, _⟩ => by
      simp [encodeB, encode, encodeString, encodeBytes, pad32]
  | .array t, ⟨vs, _⟩ => by
      simp only [encodeB, encode, Builder.toList_append, Builder.toList_bytes,
        toList_encodePartsB, map_toPart_map_partOfB t vs]
  | .fixedArray t _, ⟨vs, _⟩ => by
      simp only [encodeB, encode, toList_encodePartsB, map_toPart_map_partOfB t vs]
  | .tuple ts, vs => by
      simp only [encodeB, encode, toList_encodePartsB, map_toPart_partsOfTupleB ts vs]
termination_by t => 4 * sizeOf t

/-- `partOfB` denotes `partOf`. -/
theorem toPart_partOfB : (t : Ty) → (v : t.Val) → (partOfB t v).toPart = partOf t v := by
  intro t v
  cases hs : t.IsStatic
  · rw [partOfB_dynamic t v hs, partOf_dynamic t v hs]
    simp [PartB.toPart, toList_encodeB t v]
  · rw [partOfB_static t v hs, partOf_static t v hs]
    simp [PartB.toPart, toList_encodeB t v]
termination_by t => 4 * sizeOf t + 1

/-- Element lists denote element lists. -/
theorem map_toPart_map_partOfB : (t : Ty) → (vs : List t.Val) →
    (vs.map (partOfB t)).map PartB.toPart = vs.map (partOf t) := by
  intro t vs
  induction vs with
  | nil => rfl
  | cons w ws ih => rw [List.map_cons, List.map_cons, List.map_cons, ih, toPart_partOfB t w]
termination_by t => 4 * sizeOf t + 2

/-- Tuple part lists denote tuple part lists. -/
theorem map_toPart_partsOfTupleB : (ts : List Ty) → (vs : TupleVal ts) →
    (partsOfTupleB ts vs).map PartB.toPart = partsOfTuple ts vs
  | [], _ => by rw [partsOfTupleB, partsOfTuple, List.map_nil]
  | t :: ts, (v, vs) => by
      rw [partsOfTupleB, List.map_cons, toPart_partOfB t v, partsOfTuple,
        map_toPart_partsOfTupleB ts vs]
termination_by ts => 4 * sizeOf ts + 3
end

/-! ## the executable entry points -/

/-- **Executable ABI encoder**: encode a value straight into a contiguous
`ByteArray`, sized exactly and filled in one linear pass. -/
def encodeByteArray (t : Ty) (v : t.Val) : ByteArray := (encodeB t v).run

/-- `encodeByteArray` produces exactly the bytes `encode` specifies. -/
@[simp] theorem data_toList_encodeByteArray (t : Ty) (v : t.Val) :
    (encodeByteArray t v).data.toList = encode t v := by
  rw [encodeByteArray, Builder.data_toList_run, toList_encodeB t v]

/-- …equivalently, it is the specification encoding packed into a `ByteArray`. -/
theorem encodeByteArray_eq (t : Ty) (v : t.Val) :
    encodeByteArray t v = (encode t v).toByteArray := by
  rw [encodeByteArray, Builder.run_eq_toByteArray, toList_encodeB t v]

@[simp] theorem size_encodeByteArray (t : Ty) (v : t.Val) :
    (encodeByteArray t v).size = (encode t v).length := by
  rw [encodeByteArray, Builder.size_run, Builder.size_eq_length_toList, toList_encodeB]

/-! ## transported theorems

Nothing below is reproved: each is its `EvmAbi.Codec` / `EvmAbi.Canonical`
counterpart with `data_toList_encodeByteArray` rewritten in. -/

/-- **Roundtrip for the executable encoder**, inherited from `roundtrip`. -/
theorem decode_encodeByteArray (t : Ty) (hv : t.Valid) (v : t.Val)
    (hb : (encodeByteArray t v).size < 2 ^ 256) :
    decode t (encodeByteArray t v).data.toList = some v := by
  rw [size_encodeByteArray] at hb
  rw [data_toList_encodeByteArray]
  exact roundtrip t hv v hb

/-- **Static roundtrip for the executable encoder** — no size hypothesis. -/
theorem decode_encodeByteArray_static (t : Ty) (hs : t.IsStatic = true) (hv : t.Valid)
    (v : t.Val) : decode t (encodeByteArray t v).data.toList = some v := by
  rw [data_toList_encodeByteArray]
  exact roundtrip_static t hs hv v

/-- The executable encoder's output is canonical. -/
theorem isCanonical_encodeByteArray (t : Ty) (hv : t.Valid) (v : t.Val)
    (hb : (encodeByteArray t v).size < 2 ^ 256) :
    IsCanonical t (encodeByteArray t v).data.toList := by
  rw [size_encodeByteArray] at hb
  rw [data_toList_encodeByteArray]
  exact isCanonical_encode t hv v hb

/-- **Strict roundtrip for the executable encoder**, inherited from
`decodeCanonical_encode`. -/
theorem decodeCanonical_encodeByteArray (t : Ty) (hv : t.Valid) (v : t.Val)
    (hb : (encodeByteArray t v).size < 2 ^ 256) :
    decodeCanonical t (encodeByteArray t v).data.toList = some v := by
  rw [size_encodeByteArray] at hb
  rw [data_toList_encodeByteArray]
  exact decodeCanonical_encode t hv v hb

end EvmAbi
