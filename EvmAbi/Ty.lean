import Binary.UInt256

/-!
# EvmAbi.Ty

The ABI type universe (roadmap design decision 1, node 8): an inductive
universe `Ty` together with its type-indexed value family `Ty.Val`, so the
roundtrip statement is simply `decode t (encode t v) = some v` — no separate
well-formedness predicate on values, because `Val` is already refined.

The universe covers the full ABI type grammar:

```
uintM | intM | bool | address | bytesM | bytes | string
T[]   | T[k]  | (T₁, ..., Tₙ)
```

Two technical points shape this module:

* **Mutual list helpers.**  A clause like `∀ t ∈ ts, P t` inside a
  definition by pattern matching falls into well-founded recursion
  (`Acc.rec`), which is opaque both to the kernel and to the elaborator.
  All list-quantifying companions therefore come as structurally-recursive
  mutual siblings: `Val/TupleVal`, `isStatic/allStatic`, `headSize/headSizeSum`.

* **`Val` is `@[reducible]`** so the dependent matches in `encode`/`decode`
  see through the type index.  The dynamic-payload length bounds are part
  of `Val` itself: `bytes`/`string`/`array` values are subtypes carrying
  their own `< 2^64` bound, and containers inherit their components'
  bounds through the recursion — no separate well-formedness predicate
  exists.
-/

namespace EvmAbi

/-! ## Widths

ABI scalar width parameters share one `Width` type: a `Fin 32` index plus
one.  The literal `n` means the byte length `n` (`1..32`).  For `uintM` /
`intM` the bit width is `8 * n` (`8..256`); for `bytesN` the byte length is
`n`.  This gives a single shared representation with a single `OfNat`
conversion, and invalid widths such as `0` or `33` are unrepresentable. -/

/-- A legal ABI scalar width: `idx.val + 1` is the byte length (`1..32`). -/
structure Width where
  idx : Fin 32
  deriving Repr, DecidableEq

namespace Width

/-- The byte length denoted by a width parameter (`1..32`). -/
def bytes (w : Width) : Nat := w.idx.val + 1

/-- The bit length denoted by a `uint`/`int` width parameter (`8..256`). -/
def bits (w : Width) : Nat := (w.idx.val + 1) * 8

/-- Construct a width from a bit length `8..256` divisible by 8. -/
def ofBits? (m : Nat) : Option Width :=
  if h : 0 < m ∧ m ≤ 256 ∧ m % 8 = 0 then some ⟨⟨m / 8 - 1, by omega⟩⟩ else none

/-- Construct a width from a byte length `1..32`. -/
def ofBytes? (n : Nat) : Option Width :=
  if h : 0 < n ∧ n ≤ 32 then some ⟨⟨n - 1, by omega⟩⟩ else none

instance : OfNat Width 1 where ofNat := ⟨0⟩
instance : OfNat Width 2 where ofNat := ⟨1⟩
instance : OfNat Width 3 where ofNat := ⟨2⟩
instance : OfNat Width 4 where ofNat := ⟨3⟩
instance : OfNat Width 5 where ofNat := ⟨4⟩
instance : OfNat Width 6 where ofNat := ⟨5⟩
instance : OfNat Width 7 where ofNat := ⟨6⟩
instance : OfNat Width 8 where ofNat := ⟨7⟩
instance : OfNat Width 9 where ofNat := ⟨8⟩
instance : OfNat Width 10 where ofNat := ⟨9⟩
instance : OfNat Width 11 where ofNat := ⟨10⟩
instance : OfNat Width 12 where ofNat := ⟨11⟩
instance : OfNat Width 13 where ofNat := ⟨12⟩
instance : OfNat Width 14 where ofNat := ⟨13⟩
instance : OfNat Width 15 where ofNat := ⟨14⟩
instance : OfNat Width 16 where ofNat := ⟨15⟩
instance : OfNat Width 17 where ofNat := ⟨16⟩
instance : OfNat Width 18 where ofNat := ⟨17⟩
instance : OfNat Width 19 where ofNat := ⟨18⟩
instance : OfNat Width 20 where ofNat := ⟨19⟩
instance : OfNat Width 21 where ofNat := ⟨20⟩
instance : OfNat Width 22 where ofNat := ⟨21⟩
instance : OfNat Width 23 where ofNat := ⟨22⟩
instance : OfNat Width 24 where ofNat := ⟨23⟩
instance : OfNat Width 25 where ofNat := ⟨24⟩
instance : OfNat Width 26 where ofNat := ⟨25⟩
instance : OfNat Width 27 where ofNat := ⟨26⟩
instance : OfNat Width 28 where ofNat := ⟨27⟩
instance : OfNat Width 29 where ofNat := ⟨28⟩
instance : OfNat Width 30 where ofNat := ⟨29⟩
instance : OfNat Width 31 where ofNat := ⟨30⟩
instance : OfNat Width 32 where ofNat := ⟨31⟩

end Width

/-- ABI types: the full grammar of the specification. -/
inductive Ty where
  /-- `uintM`: unsigned integer of `M` bits; the spec requires `8 ∣ M`, `8 ≤ M ≤ 256`.
  The constructor's `Width` is the byte length (`1..32`). -/
  | uint (m : Width)
  /-- `intM`: two's-complement signed integer of `M` bits, same size rule.
  The constructor's `Width` is the byte length (`1..32`). -/
  | int (m : Width)
  /-- `bool`: encoded as the word `0` (`false`) or `1` (`true`). -/
  | bool
  /-- `address`: 20 raw bytes (ABI-encoded exactly like `uint160`). -/
  | address
  /-- `bytesM`: exactly `M` raw bytes (`1 ≤ M ≤ 32`), left-aligned in one word. -/
  | bytesN (m : Width)
  /-- `bytes`: dynamically sized raw bytes. -/
  | bytes
  /-- `string`: dynamically sized UTF-8 text (encoded exactly like `bytes`). -/
  | string
  /-- `T[]`: dynamically sized array of `T`. -/
  | array (t : Ty)
  /-- `T[k]`: fixed-size array of `k` elements of `T`, with `k > 0`. -/
  | fixedArray (t : Ty) (n : Nat) (h : 0 < n)
  /-- `(T₁, ..., Tₙ)`: non-empty tuple of types. -/
  | tuple (head : Ty) (tail : List Ty)
  deriving Repr

namespace Ty

/-! ## Staticness and head sizes -/

/- A type is *static* when its encoding has a fixed size determined by the
type alone, embedded inline in any head it appears in.  `allStatic` is the
structural list sibling. -/
mutual
/-- Staticness predicate. -/
def isStatic : Ty → Bool
  | uint _ | int _ | bool | address | bytesN _ => true
  | bytes | string | array _ => false
  | fixedArray t _ _ => t.isStatic
  | tuple head tail => head.isStatic && allStatic tail

/-- Every type in the list is static. -/
def allStatic : List Ty → Bool
  | [] => true
  | t :: ts => t.isStatic && allStatic ts
end

/- The number of bytes a type occupies in the head section: for static
types the full encoding size, for dynamic types the 32 bytes of the offset
word.  `headSizeSum` is the structural list sibling. -/
mutual
/-- Head size of a type. -/
def headSize : Ty → Nat
  | fixedArray t n _ => if t.isStatic then n * t.headSize else 32
  | tuple head tail => if head.isStatic && allStatic tail then head.headSize + headSizeSum tail else 32
  | _ => 32

/-- Sum of the head sizes of a list of types. -/
def headSizeSum : List Ty → Nat
  | [] => 0
  | t :: ts => t.headSize + headSizeSum ts
end

/-! ## Packed sizes -/

/- The packed encoding size of a static type (the number of bytes its
encoding occupies in `abi.encodePacked`).  For dynamic types the size is
not statically known and the function returns 0.  `packedSizeSum` is the
structural list sibling.  Note the fixed-array case: Solidity pads packed
array *elements* to their standard (32-byte-word) width, so a fixed array
occupies `n` standard element slots, not `n` tight ones. -/
mutual
/-- Packed size of a type. -/
def packedSize : Ty → Nat
  | uint m | int m => m.bits / 8
  | bool => 1
  | address => 20
  | bytesN m => m.bytes
  | bytes | string | array _ => 0
  | fixedArray t n _ => n * t.headSize
  | tuple head tail => head.packedSize + packedSizeSum tail

/-- Sum of the packed sizes of a list of types. -/
def packedSizeSum : List Ty → Nat
  | [] => 0
  | t :: ts => t.packedSize + packedSizeSum ts
end

/- For an all-static type, the packed size is the total bytes the encoding
occupies.  Dynamic types (`bytes`, `string`, `T[]`) have no statically
known packed size — their encodings are data-dependent and `decodePacked`
rejects them — so `packedSize` returns 0 for them. -/
/-! ## The value family -/

/- Values indexed by their ABI type, refined so that every inhabitant is
encodable *and decodable*: the roundtrip holds for every `v : t.Val` of a
valid `t`, with no side condition on the value.  Dynamic payloads carry
their length bound in the subtype: it must fit a 64-bit word.  Soundness
alone would only need `< 2^256`, the width of the length word past which
it wraps; `2^64` is deliberately tighter, and a length word above it is
rejected rather than believed.  Nothing is lost — a payload that long
cannot be held in memory, let alone in a transaction — and every derived
length stays inside a machine word.  Containers inherit their components'
bounds through the recursion, so no separate well-formedness predicate is
needed.  (The roundtrip still assumes the
*total* encoding length is below `2^256`, so the offset words do not wrap
either — an aggregate property no per-value refinement can express.)
Tuples are right-nested products (`TupleVal`).  Marked `@[reducible]` so
the dependent match in `encode`/`decode` can see through the type index
(roadmap design decision 1). -/
mutual
/-- The type of values of ABI type `t`. -/
@[reducible]
def Val : Ty → Type
  | uint m => { n : Nat // n < 2 ^ m.bits }
  | int m => { i : Int // -((2 ^ (m.bits - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m.bits - 1) : Nat) : Int) }
  | bool => Bool
  | address => { bs : List UInt8 // bs.length = 20 }
  | bytesN m => { bs : List UInt8 // bs.length = m.bytes }
  | bytes => { bs : List UInt8 // bs.length < 2 ^ 64 }
  | string => { s : String // s.toUTF8.size < 2 ^ 64 }
  | array t => { vs : List t.Val // vs.length < 2 ^ 64 }
  | fixedArray t n _ => { vs : List t.Val // vs.length = n }
  | tuple head tail => head.Val × TupleVal tail

/-- Tuple values: right-nested products. -/
@[reducible]
def TupleVal : List Ty → Type
  | [] => Unit
  | t :: ts => t.Val × TupleVal ts
end

end Ty

end EvmAbi
