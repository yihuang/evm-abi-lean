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
  | uint m => { w : Binary.UInt256 // w.toNat < 2 ^ m }
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
  | uint _, ⟨w, h⟩ => ⟨w.toNat, h⟩
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

/-! ## injectivity

The two families carry the same information: the clauses differ only in the
payloads, and there only by `ByteArray.data.toList`.

This is the direction the agreement lemmas cannot supply.  They push a runtime
answer *down* to its denotation; injectivity brings a conclusion back up, which
is what lets the capstones in `EvmAbi.Codec.Runtime` be stated at all. -/

/-- `List.map f` is injective when `f` is. -/
private theorem map_inj {α β : Type} {f : α → β} (hf : ∀ {a b : α}, f a = f b → a = b) :
    ∀ {as bs : List α}, as.map f = bs.map f → as = bs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
      rw [List.map_cons, List.map_cons, List.cons.injEq] at h
      rw [hf h.1, map_inj hf h.2]

/-- A `ByteArray` is determined by the bytes it denotes. -/
private theorem ba_inj {a b : ByteArray} (h : a.data.toList = b.data.toList) : a = b := by
  apply Binary.ByteArray.data_inj
  rwa [← Array.toList_inj]

mutual
/-- **`ValBA.toList` is injective**: a packed value is determined by its
denotation. -/
theorem ValBA.toList_injective (t : Ty) {v w : ValBA t}
    (h : ValBA.toList t v = ValBA.toList t w) : v = w := by
  cases t with
  | uint m =>
      obtain ⟨n, hn⟩ := v; obtain ⟨n', hn'⟩ := w
      simp only [ValBA.toList, Subtype.mk.injEq] at h
      exact Subtype.ext (Binary.UInt256.toNat_inj.mp h)
  | int m =>
      obtain ⟨i, hi⟩ := v; obtain ⟨i', hi'⟩ := w
      simp only [ValBA.toList, Subtype.mk.injEq] at h
      exact Subtype.ext h
  | bool => simpa only [ValBA.toList] using h
  | address =>
      obtain ⟨n, hn⟩ := v; obtain ⟨n', hn'⟩ := w
      simp only [ValBA.toList, Subtype.mk.injEq] at h
      exact Subtype.ext h
  | bytesN m =>
      obtain ⟨a, ha⟩ := v; obtain ⟨b, hb⟩ := w
      simp only [ValBA.toList, Subtype.mk.injEq] at h
      exact Subtype.ext (ba_inj h)
  | bytes =>
      obtain ⟨a, ha⟩ := v; obtain ⟨b, hb⟩ := w
      simp only [ValBA.toList, Subtype.mk.injEq] at h
      exact Subtype.ext (ba_inj h)
  | string => simpa only [ValBA.toList] using h
  | array t =>
      obtain ⟨vs, hv⟩ := v; obtain ⟨ws, hw⟩ := w
      simp only [ValBA.toList, Subtype.mk.injEq] at h
      exact Subtype.ext (map_inj (fun {_ _} hab => ValBA.toList_injective t hab) h)
  | fixedArray t n =>
      obtain ⟨vs, hv⟩ := v; obtain ⟨ws, hw⟩ := w
      simp only [ValBA.toList, Subtype.mk.injEq] at h
      exact Subtype.ext (map_inj (fun {_ _} hab => ValBA.toList_injective t hab) h)
  | tuple ts => exact TupleValBA.toList_injective ts (by simpa only [ValBA.toList] using h)
termination_by (sizeOf t, 0)

/-- **`TupleValBA.toList` is injective**, componentwise. -/
theorem TupleValBA.toList_injective (ts : List Ty) {vs ws : TupleValBA ts}
    (h : TupleValBA.toList ts vs = TupleValBA.toList ts ws) : vs = ws := by
  cases ts with
  | nil => rfl
  | cons t ts =>
      obtain ⟨v, vss⟩ := vs; obtain ⟨w, wss⟩ := ws
      rw [TupleValBA.toList_cons, TupleValBA.toList_cons, Prod.mk.injEq] at h
      rw [ValBA.toList_injective t h.1, TupleValBA.toList_injective ts h.2]
termination_by (sizeOf ts, 1)
end

end EvmAbi
