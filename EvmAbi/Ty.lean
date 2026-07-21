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
  (`Acc.rec`), which is opaque both to the kernel and to the elaborator —
  `Valid (uint 8)` would no longer be a `Prop` one can inhabit by
  `⟨by decide, by decide⟩`.  All list-quantifying companions therefore come
  as structurally-recursive mutual siblings: `Valid/AllValid`,
  `Val/TupleVal`, `IsStatic/allStatic`, `headSize/headSizeSum`,
  `LenBound/AllLenBound/TupleLenBounds`.

* **`Val` is `@[reducible]`** so the dependent matches in `encode`/`decode`
  see through the type index.  `LenBound` has a dependent index (`t.Val`)
  and is necessarily compiled by well-founded recursion; it stays opaque
  and is only ever rewritten through its equation lemmas (`simp [LenBound]`).
-/

namespace EvmAbi

/-- ABI types: the full grammar of the specification. -/
inductive Ty where
  /-- `uintM`: unsigned integer of `M` bits; the spec requires `8 ∣ M`, `8 ≤ M ≤ 256`. -/
  | uint (m : Nat)
  /-- `intM`: two's-complement signed integer of `M` bits, same size rule. -/
  | int (m : Nat)
  /-- `bool`: encoded as the word `0` (`false`) or `1` (`true`). -/
  | bool
  /-- `address`: a 160-bit unsigned integer (encoded exactly like `uint160`). -/
  | address
  /-- `bytesM`: exactly `M` raw bytes (`1 ≤ M ≤ 32`), left-aligned in one word. -/
  | bytesN (m : Nat)
  /-- `bytes`: dynamically sized raw bytes. -/
  | bytes
  /-- `string`: dynamically sized UTF-8 text (encoded exactly like `bytes`). -/
  | string
  /-- `T[]`: dynamically sized array of `T`. -/
  | array (t : Ty)
  /-- `T[k]`: fixed-size array of `k` elements of `T`. -/
  | fixedArray (t : Ty) (n : Nat)
  /-- `(T₁, ..., Tₙ)`: tuple of types. -/
  | tuple (ts : List Ty)
  deriving Repr

namespace Ty

/-! ## Validity -/

/- Spec-level validity of a type: size parameters in range, and every
sub-type valid.  Codec theorems assume it; invalid types still encode, but
nothing is promised.  `AllValid` is the structural list sibling (see the
module doc). -/
mutual
/-- Validity of a single type. -/
def Valid : Ty → Prop
  | uint m | int m => 8 ≤ m ∧ m ≤ 256 ∧ m % 8 = 0
  | bytesN m => 1 ≤ m ∧ m ≤ 32
  | array t => t.Valid
  | fixedArray t _ => t.Valid
  | tuple ts => AllValid ts
  | _ => True

/-- Validity of every type in a list. -/
def AllValid : List Ty → Prop
  | [] => True
  | t :: ts => t.Valid ∧ AllValid ts
end

/-- `AllValid` unwrapped to a pointwise statement. -/
theorem AllValid.forall_mem {ts : List Ty} (h : AllValid ts) : ∀ t ∈ ts, t.Valid := by
  induction ts with
  | nil => intro t ht; cases ht
  | cons u us ih =>
      intro t ht
      simp only [AllValid] at h
      cases List.mem_cons.mp ht with
      | inl he => rw [he]; exact h.1
      | inr hm => exact ih h.2 t hm

/- Decidability of validity, by mutual recursion on the type and the list. -/
mutual
/-- Decision procedure for `Valid`. -/
def decValid : (t : Ty) → Decidable t.Valid
  | uint m | int m => inferInstanceAs (Decidable (8 ≤ m ∧ m ≤ 256 ∧ m % 8 = 0))
  | bytesN m => inferInstanceAs (Decidable (1 ≤ m ∧ m ≤ 32))
  | bool | address | bytes | string => inferInstanceAs (Decidable True)
  | array t => decValid t
  | fixedArray t _ => decValid t
  | tuple ts => decAllValid ts

/-- Decision procedure for `AllValid`. -/
def decAllValid : (ts : List Ty) → Decidable (AllValid ts)
  | [] => isTrue trivial
  | t :: ts =>
      match decValid t, decAllValid ts with
      | isTrue ht, isTrue hts => isTrue ⟨ht, hts⟩
      | isFalse hf, _ => isFalse fun h => hf h.1
      | _, isFalse hf => isFalse fun h => hf h.2
end

instance (t : Ty) : Decidable t.Valid := decValid t
instance (ts : List Ty) : Decidable (AllValid ts) := decAllValid ts

/-! ## Staticness and head sizes -/

/- A type is *static* when its encoding has a fixed size determined by the
type alone, embedded inline in any head it appears in.  `allStatic` is the
structural list sibling. -/
mutual
/-- Staticness predicate. -/
def IsStatic : Ty → Bool
  | uint _ | int _ | bool | address | bytesN _ => true
  | bytes | string | array _ => false
  | fixedArray t _ => t.IsStatic
  | tuple ts => allStatic ts

/-- Every type in the list is static. -/
def allStatic : List Ty → Bool
  | [] => true
  | t :: ts => t.IsStatic && allStatic ts
end

/- The number of bytes a type occupies in the head section: for static
types the full encoding size, for dynamic types the 32 bytes of the offset
word.  `headSizeSum` is the structural list sibling. -/
mutual
/-- Head size of a type. -/
def headSize : Ty → Nat
  | fixedArray t n => if t.IsStatic then n * t.headSize else 32
  | tuple ts => if allStatic ts then headSizeSum ts else 32
  | _ => 32

/-- Sum of the head sizes of a list of types. -/
def headSizeSum : List Ty → Nat
  | [] => 0
  | t :: ts => t.headSize + headSizeSum ts
end

/-- `headSizeSum` is the sum of the mapped `headSize`s. -/
theorem headSizeSum_eq_sum_map (ts : List Ty) :
    headSizeSum ts = (ts.map headSize).sum := by
  induction ts with
  | nil => simp only [headSizeSum, List.map_nil, List.sum_nil]
  | cons t ts ih => simp only [headSizeSum, List.map_cons, List.sum_cons, ← ih]

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
  | uint m | int m => m / 8
  | bool => 1
  | address => 20
  | bytesN m => m
  | bytes | string | array _ => 0
  | fixedArray t n => n * t.headSize
  | tuple ts => packedSizeSum ts

/-- Sum of the packed sizes of a list of types. -/
def packedSizeSum : List Ty → Nat
  | [] => 0
  | t :: ts => t.packedSize + packedSizeSum ts
end

/-- `packedSizeSum` is the sum of the mapped `packedSize`s. -/
theorem packedSizeSum_eq_sum_map (ts : List Ty) :
    packedSizeSum ts = (ts.map packedSize).sum := by
  induction ts with
  | nil => simp only [packedSizeSum, List.map_nil, List.sum_nil]
  | cons t ts ih => simp only [packedSizeSum, List.map_cons, List.sum_cons, ← ih]

/- For an all-static type, the packed size is the total bytes the encoding
occupies.  Dynamic types (`bytes`, `string`, `T[]`) have no statically
known packed size — their encodings are data-dependent and `decodePacked`
rejects them — so `packedSize` returns 0 for them. -/
/-! ## The value family -/

/- Values indexed by their ABI type, refined so that every inhabitant is
encodable: the roundtrip holds for *every* `v : t.Val` of a valid `t`
(plus the length bound of `LenBound` for dynamic payloads).  Tuples are
right-nested products (`TupleVal`).  Marked `@[reducible]` so the dependent
match in `encode`/`decode` can see through the type index (roadmap design
decision 1). -/
mutual
/-- The type of values of ABI type `t`. -/
@[reducible]
def Val : Ty → Type
  | uint m => { n : Nat // n < 2 ^ m }
  | int m => { i : Int // -((2 ^ (m - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m - 1) : Nat) : Int) }
  | bool => Bool
  | address => { n : Nat // n < 2 ^ 160 }
  | bytesN m => { bs : List UInt8 // bs.length = m }
  | bytes => List UInt8
  | string => String
  | array t => List t.Val
  | fixedArray t n => { vs : List t.Val // vs.length = n }
  | tuple ts => TupleVal ts

/-- Tuple values: right-nested products. -/
@[reducible]
def TupleVal : List Ty → Type
  | [] => Unit
  | t :: ts => t.Val × TupleVal ts
end

/-! ## Length bounds -/

/- The condition under which an encoded value is decodable: every dynamic
payload must fit the single length word that prefixes it.  Without it the
length word wraps modulo `2^256` and decoding reads a wrong length — the
unconditional statement would be false, not merely unproven.  (The
roundtrip additionally assumes the *total* encoding length is below
`2^256`, so the offset words do not wrap either.)

`LenBound` matches on `t.Val` and is therefore compiled by well-founded
recursion; it stays opaque and is used only through its equation lemmas. -/
mutual
/-- The length bound for values of type `t`. -/
def LenBound : (t : Ty) → t.Val → Prop
  | bytes, bs => bs.length < 2 ^ 256
  | string, s => s.toUTF8.size < 2 ^ 256
  | array t, vs => vs.length < 2 ^ 256 ∧ AllLenBound t vs
  | fixedArray t _, ⟨vs, _⟩ => AllLenBound t vs
  | tuple ts, vs => TupleLenBounds ts vs
  | _, _ => True

/-- The length bound, pointwise over a list of values of the same type. -/
def AllLenBound : (t : Ty) → List t.Val → Prop
  | _, [] => True
  | t, v :: vs => LenBound t v ∧ AllLenBound t vs

/-- The length bound, pointwise over the components of a tuple. -/
def TupleLenBounds : (ts : List Ty) → TupleVal ts → Prop
  | [], _ => True
  | t :: ts, (v, vs) => LenBound t v ∧ TupleLenBounds ts vs
end

end Ty

end EvmAbi
