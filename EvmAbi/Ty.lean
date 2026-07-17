import Binary.UInt256

/-!
# EvmAbi.Ty

The ABI type universe (roadmap design decision 1): an inductive universe
`Ty` together with its type-indexed value family `Ty.Val`, so the roundtrip
statement is simply `decode t (encode t v) = some v` — no separate
well-formedness predicate on values, because `Val` is already refined.

S2 covers the base types only: static `uintM / intM / bool / address / bytesM`
and dynamic `bytes` / `string`. Compound types (tuples, fixed and dynamic
arrays) arrive with the head/tail combinator of S3/S4.
-/

namespace EvmAbi

/-- ABI types (base fragment; compound constructors are added in S3/S4). -/
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
  deriving Repr, DecidableEq

namespace Ty

/-- Spec-level validity of a type: size parameters in range.
Codec theorems assume it; invalid types still encode, but nothing is promised. -/
def Valid : Ty → Prop
  | uint m | int m => 8 ≤ m ∧ m ≤ 256 ∧ m % 8 = 0
  | bytesN m => 1 ≤ m ∧ m ≤ 32
  | _ => True

instance (t : Ty) : Decidable t.Valid := by
  cases t <;> unfold Valid <;> infer_instance

/-- A type is *static* when its encoding is one fixed-size word, embedded
inline in any head it appears in. All base types except `bytes`/`string`
are static. -/
def IsStatic : Ty → Bool
  | uint _ | int _ | bool | address | bytesN _ => true
  | bytes | string => false

/-- Values indexed by their ABI type, refined so that every inhabitant is
encodable: the roundtrip holds for *every* `v : t.Val` of a valid `t`
(plus the length bound of `LenBound` for dynamic payloads).

Marked `@[reducible]` so the dependent match in `encode`/`decode`
can see through the type index (roadmap design decision 1). -/
@[reducible]
def Val : Ty → Type
  | uint m => { n : Nat // n < 2 ^ m }
  | int m => { i : Int // -((2 ^ (m - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m - 1) : Nat) : Int) }
  | bool => Bool
  | address => { n : Nat // n < 2 ^ 160 }
  | bytesN m => { bs : List UInt8 // bs.length = m }
  | bytes => List UInt8
  | string => String

/-- The condition under which an encoded value is decodable: dynamic payloads
must fit the single length word that prefixes them. Without it the length
word wraps modulo `2^256` and decoding reads a wrong length — the
unconditional statement would be false, not merely unproven.

Marked `@[reducible]` together with `Val`. -/
@[reducible]
def LenBound : (t : Ty) → t.Val → Prop
  | bytes, bs => bs.length < 2 ^ 256
  | string, s => s.toUTF8.size < 2 ^ 256
  | _, _ => True

end Ty

end EvmAbi
