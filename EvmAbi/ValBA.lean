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
  | uint m => { w : Binary.UInt256 // w.toNat < 2 ^ m.bits }
  | int m => { i : Int // -((2 ^ (m.bits - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m.bits - 1) : Nat) : Int) }
  | .bool => Bool
  | address => { bs : ByteArray // bs.size = 20 }
  | bytesN m => { bs : ByteArray // bs.size = m.bytes }
  | bytes => { bs : ByteArray // bs.size < 2 ^ 64 }
  | string => { s : String // s.toUTF8.size < 2 ^ 64 }
  | array t => { vs : List (ValBA t) // vs.length < 2 ^ 64 }
  | fixedArray t n _ => { vs : List (ValBA t) // vs.length = n }
  | tuple head tail => ValBA head × TupleValBA tail

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
  | address, ⟨bs, h⟩ => ⟨bs.data.toList, by
      rw [← Binary.ByteArray.size_eq_toList_length]
      exact h⟩
  | bytesN _, ⟨bs, h⟩ => ⟨bs.data.toList, by
      rw [← Binary.ByteArray.size_eq_toList_length]
      exact h⟩
  | bytes, ⟨bs, h⟩ => ⟨bs.data.toList, by
      rw [← Binary.ByteArray.size_eq_toList_length]
      exact h⟩
  | string, s => s
  | array t, ⟨vs, h⟩ => ⟨vs.map (ValBA.toList t), by simpa using h⟩
  | fixedArray t n _, ⟨vs, h⟩ => ⟨vs.map (ValBA.toList t), by simpa using h⟩
  | tuple head tail, (v, vs) => (ValBA.toList head v, TupleValBA.toList tail vs)
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

mutual
/-- Materialize a specification value with packed payloads: the inverse of
`ValBA.toList` on the nose.  Only the payload-carrying clauses do anything —
the numeric ones are the identity and `string` is already packed — which is
what lets the runtime codec be *defined* as the spec decoder composed with
this, instead of being a second hand-written walk.

This is a proof- and definition-side function, not a runtime path: the
`@[csimp]` swap on `decodeBAVal` means no caller ever walks it. -/
def ValBA.ofList : (t : Ty) → t.Val → ValBA t
  | uint m, ⟨n, h⟩ => ⟨Binary.UInt256.ofNat n, by
      rw [Binary.UInt256.toNat_ofNat, Nat.mod_eq_of_lt]
      · exact h
      · exact Nat.lt_of_lt_of_le h
          (Nat.pow_le_pow_right (by omega) (by simp [Width.bits]; omega))⟩
  | int m, ⟨i, h⟩ => ⟨i, h⟩
  | .bool, b => b
  | address, ⟨bs, h⟩ => ⟨bs.toByteArray, by rw [List.size_toByteArray]; exact h⟩
  | bytesN m, ⟨bs, h⟩ => ⟨bs.toByteArray, by rw [List.size_toByteArray]; exact h⟩
  | bytes, ⟨bs, h⟩ => ⟨bs.toByteArray, by rw [List.size_toByteArray]; exact h⟩
  | string, s => s
  | array t, ⟨vs, h⟩ => ⟨vs.map (ValBA.ofList t), by simpa using h⟩
  | fixedArray t n _, ⟨vs, h⟩ => ⟨vs.map (ValBA.ofList t), by simpa using h⟩
  | tuple head tail, (v, vs) => (ValBA.ofList head v, TupleValBA.ofList tail vs)
termination_by t => (sizeOf t, 0)

/-- Tuple values materialize componentwise. -/
def TupleValBA.ofList : (ts : List Ty) → TupleVal ts → TupleValBA ts
  | [], _ => ()
  | t :: ts, (v, vs) => (ValBA.ofList t v, TupleValBA.ofList ts vs)
termination_by ts => (sizeOf ts, 1)
end

/-- A `List.map` whose function is pointwise the identity is the identity —
the `ofList` roundtrip applied elementwise. -/
private theorem map_eq_self_of {α : Type} {f : α → α} (h : ∀ a, f a = a) :
    ∀ l : List α, l.map f = l
  | [] => rfl
  | a :: l => by simp [h a, map_eq_self_of h l]

mutual
/-- **`ofList` is a section of `toList`**: materializing a spec value and
denoting it back gives the same value.  This is the half of the roundtrip the
`@[csimp]` swap needs — the other half is `toList_injective` below. -/
theorem ValBA.toList_ofList (t : Ty) (v : t.Val) :
    ValBA.toList t (ValBA.ofList t v) = v := by
  cases t with
  | uint m =>
      obtain ⟨n, h⟩ := v
      refine Subtype.ext ?_
      rw [ValBA.ofList.eq_1, ValBA.toList.eq_1]
      show (Binary.UInt256.ofNat n).toNat = n
      rw [Binary.UInt256.toNat_ofNat, Nat.mod_eq_of_lt]
      exact Nat.lt_of_lt_of_le h
        (Nat.pow_le_pow_right (by omega) (by simp [Width.bits]; omega))
  | int m =>
      obtain ⟨i, h⟩ := v
      rw [ValBA.ofList.eq_2, ValBA.toList.eq_2]
  | bool => rw [ValBA.ofList.eq_3, ValBA.toList.eq_3]
  | address =>
      obtain ⟨bs, h⟩ := v
      grind [ValBA.ofList, ValBA.toList, List.data_toByteArray, List.size_toByteArray,
        Binary.ByteArray.size_eq_toList_length]
  | bytesN m =>
      obtain ⟨bs, h⟩ := v
      grind [ValBA.ofList, ValBA.toList, List.data_toByteArray, List.size_toByteArray,
        Binary.ByteArray.size_eq_toList_length]
  | bytes =>
      obtain ⟨bs, h⟩ := v
      grind [ValBA.ofList, ValBA.toList, List.data_toByteArray, List.size_toByteArray,
        Binary.ByteArray.size_eq_toList_length]
  | string => grind [ValBA.ofList, ValBA.toList]
  | array t =>
      obtain ⟨vs, h⟩ := v
      refine Subtype.ext ?_
      simp only [ValBA.ofList.eq_8, ValBA.toList.eq_8, List.map_map]
      exact map_eq_self_of (fun v => ValBA.toList_ofList t v) vs
  | fixedArray t n _ =>
      obtain ⟨vs, h⟩ := v
      refine Subtype.ext ?_
      simp only [ValBA.ofList.eq_9, ValBA.toList.eq_9, List.map_map]
      exact map_eq_self_of (fun v => ValBA.toList_ofList t v) vs
  | tuple head tail =>
      obtain ⟨v', vs⟩ := v
      rw [ValBA.ofList.eq_10, ValBA.toList.eq_10, ValBA.toList_ofList head v',
        TupleValBA.toList_ofList tail vs]
termination_by (sizeOf t, 0)

/-- …and componentwise for tuples. -/
theorem TupleValBA.toList_ofList : (ts : List Ty) → (vs : TupleVal ts) →
    TupleValBA.toList ts (TupleValBA.ofList ts vs) = vs
  | [], vs => by cases vs; rw [TupleValBA.ofList.eq_1, TupleValBA.toList.eq_1]
  | t :: ts, (v, vs) => by
      rw [TupleValBA.ofList.eq_2, TupleValBA.toList_cons, ValBA.toList_ofList t v,
        TupleValBA.toList_ofList ts vs]
termination_by ts => (sizeOf ts, 1)
end

/-! ## injectivity

The two families carry the same information: the clauses differ only in the
payloads, and there only by `ByteArray.data.toList`.

This is the direction the agreement lemmas cannot supply.  They push a runtime
answer *down* to its denotation; injectivity brings a conclusion back up, which
is what lets the capstones in `EvmAbi.Codec` be stated at all. -/

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
  grind [Binary.ByteArray.data_inj, Array.toList_inj]

mutual
/-- **`ValBA.toList` is injective**: a packed value is determined by its
denotation. -/
theorem ValBA.toList_injective (t : Ty) {v w : ValBA t}
    (h : ValBA.toList t v = ValBA.toList t w) : v = w := by
  cases t with
  | uint m =>
      obtain ⟨n, hn⟩ := v; obtain ⟨n', hn'⟩ := w
      grind [ValBA.toList, Binary.UInt256.toNat_inj]
  | int m =>
      obtain ⟨i, hi⟩ := v; obtain ⟨i', hi'⟩ := w
      grind [ValBA.toList]
  | bool => grind [ValBA.toList]
  | address =>
      obtain ⟨a, ha⟩ := v; obtain ⟨b, hb⟩ := w
      grind [ValBA.toList, ba_inj]
  | bytesN m =>
      obtain ⟨a, ha⟩ := v; obtain ⟨b, hb⟩ := w
      grind [ValBA.toList, ba_inj]
  | bytes =>
      obtain ⟨a, ha⟩ := v; obtain ⟨b, hb⟩ := w
      grind [ValBA.toList, ba_inj]
  | string => grind [ValBA.toList]
  | array t =>
      obtain ⟨vs, hv⟩ := v; obtain ⟨ws, hw⟩ := w
      grind [ValBA.toList, map_inj (fun {_ _} hab => ValBA.toList_injective t hab)]
  | fixedArray t n _ =>
      obtain ⟨vs, hv⟩ := v; obtain ⟨ws, hw⟩ := w
      grind [ValBA.toList, map_inj (fun {_ _} hab => ValBA.toList_injective t hab)]
  | tuple head tail =>
      obtain ⟨v, vs⟩ := v; obtain ⟨w, ws⟩ := w
      grind [ValBA.toList, ValBA.toList_injective head, TupleValBA.toList_injective tail]
termination_by (sizeOf t, 0)

/-- **`TupleValBA.toList` is injective**, componentwise. -/
theorem TupleValBA.toList_injective (ts : List Ty) {vs ws : TupleValBA ts}
    (h : TupleValBA.toList ts vs = TupleValBA.toList ts ws) : vs = ws := by
  cases ts with
  | nil => rfl
  | cons t ts =>
      grind [TupleValBA.toList_cons, ValBA.toList_injective t, TupleValBA.toList_injective ts]
termination_by (sizeOf ts, 1)
end

end EvmAbi
