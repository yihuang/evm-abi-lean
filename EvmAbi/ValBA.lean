import EvmAbi.Ty

/-!
# EvmAbi.ValBA

The **runtime value family**: the same type-indexed values as `Ty.Val`,
but with packed payloads.  `Val .bytes` is `{bs : List UInt8 // …}` — the
right *specification* type (the `take`/`drop` algebra proofs live on it)
and the wrong *runtime* one: a cons cell and a boxed byte per payload
byte, so decoding a 256-byte `bytes` value costs ~2 µs and ~500
allocations.  `ValBA .bytes` is `{bs : ByteArray // …}` — one packed
buffer per payload, so the same decode is one `extract` (a memcpy).

`ValBA` is the layer `Codec.ByteArray` and `Codec` write their runtime
walkers against.  Nothing here is a second spec: `ValBA.toList` maps every
packed value to its `Ty.Val` denotation, and every `ValBA` theorem is
stated through it, so the `List UInt8` statements transport exactly as
`Builder`'s `data_toList_run` transports the encoder.  The two value
families are one value family materialized two ways, like `encode` and
`encodeByteArray`.

`string` is identical in both families (`String` is already a packed byte
buffer at runtime), and the numeric ones are identical too — only the
payload-carrying clauses differ.

`@[reducible]` for the same reason as `Val`: the dependent match in the
decoder must see through the type index.
-/

namespace EvmAbi

open Ty

mutual
/-- The type of values of ABI type `t`, with packed payloads. -/
@[reducible]
def ValBA : Ty → Type
  | uint m => { n : Nat // n < 2 ^ m }
  | int m => { i : Int // -((2 ^ (m - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m - 1) : Nat) : Int) }
  | .bool => Bool
  | address => { n : Nat // n < 2 ^ 160 }
  | bytesN m => { bs : ByteArray // bs.size = m }
  | bytes => { bs : ByteArray // bs.size < 2 ^ 256 }
  | string => { s : String // s.toUTF8.size < 2 ^ 256 }
  | array t => { vs : List (ValBA t) // vs.length < 2 ^ 256 }
  | fixedArray t n => { vs : List (ValBA t) // vs.length = n }
  | tuple ts => TupleValBA ts

/-- Tuple values: right-nested products. -/
@[reducible]
def TupleValBA : List Ty → Type
  | [] => Unit
  | t :: ts => ValBA t × TupleValBA ts
end

mutual
/-- The denotation: every packed value denotes the `Ty.Val` with the same
structure, payloads converted by `ByteArray.data.toList`. -/
def ValBA.toList : (t : Ty) → ValBA t → t.Val
  | uint _, ⟨n, h⟩ => ⟨n, h⟩
  | int _, ⟨i, h⟩ => ⟨i, h⟩
  | .bool, b => b
  | address, ⟨n, h⟩ => ⟨n, h⟩
  | bytesN _, ⟨bs, h⟩ => ⟨bs.data.toList, by
      rw [← Binary.ByteArray.size_eq_toList_length]
      exact h⟩
  | bytes, ⟨bs, h⟩ => ⟨bs.data.toList, by
      rw [← Binary.ByteArray.size_eq_toList_length]
      exact h⟩
  | string, s => s
  | array t, ⟨vs, h⟩ => ⟨vs.map (ValBA.toList t), by simpa using h⟩
  | fixedArray t n, ⟨vs, h⟩ => ⟨vs.map (ValBA.toList t), by simpa using h⟩
  | tuple ts, vs => TupleValBA.toList ts vs
termination_by t => (sizeOf t, 0)

/-- Tuple values denote componentwise. -/
def TupleValBA.toList : (ts : List Ty) → TupleValBA ts → TupleVal ts
  | [], _ => ()
  | t :: ts, (v, vs) => (ValBA.toList t v, TupleValBA.toList ts vs)
termination_by ts => (sizeOf ts, 1)
end

/-- `TupleValBA.toList` on a cons tuple is componentwise. -/
@[simp] theorem TupleValBA.toList_cons (t : Ty) (ts : List Ty)
    (v : ValBA t) (vs : TupleValBA ts) :
    TupleValBA.toList (t :: ts) (v, vs) = (ValBA.toList t v, TupleValBA.toList ts vs) := by
  rw [TupleValBA.toList.eq_2]

end EvmAbi
