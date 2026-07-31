import EvmAbi.Word

/-!
# EvmAbi.Builder

The builder/reader layer (roadmap node 9): a *write* abstraction
(`Builder`) and its dual *read* abstraction (`Get2`), decoupling the
high-level ABI layout logic from low-level byte-list plumbing.

## Design

`Builder` is a difference list over byte strings (the Hughes /
blaze-builder trick): a builder is a function `List UInt8 → List UInt8`
that prepends its payload to an arbitrary suffix, together with a proof
(`invariant`) that it really is such a prepend.  Sequencing writes is
`O(1)` function composition; the payload is materialized once, at the
boundary, by `toList`.

The proof layer already worked in this shape: every roundtrip theorem in
`EvmAbi.Static` / `EvmAbi.Dynamic` / `EvmAbi.Codec` quantifies over a
trailing `rest : List UInt8`.  `b.apply rest` *is* that trailing-suffix
form, so the existing theorems port with unchanged statements.

`Get2` is the reader dual: it consumes from two cursors — a *head*
cursor over the head section and a *tail* cursor over the tails — and
threads the expected tail frontier.  It is a monad, so the canonical
decoder's walkers compose with `do`-notation while both cursors advance
monotonically (each byte touched at most once).

The layer is deliberately dependency-free (Lean core + `Binary` only).
-/

namespace EvmAbi

open Binary

/-! ## Builder -/

/-- A byte-string builder: a prepend function with the proof that it is
determined by its materialization `apply []`. -/
structure Builder where
  /-- Run the builder onto a suffix. -/
  apply : List UInt8 → List UInt8
  /-- The builder is completely determined by the list `apply []`. -/
  invariant : ∀ rest, apply rest = apply [] ++ rest

namespace Builder

/-- `O(1)` creation (the payload is copied once, at materialization).
Lift a byte string to a builder. -/
def ofList (bs : List UInt8) : Builder := ⟨(bs ++ ·), fun _ => by simp⟩

/-- `O(1)`. The empty write. -/
def empty : Builder := ⟨id, fun _ => rfl⟩

instance : EmptyCollection Builder := ⟨empty⟩

/-- `O(1)`. Sequencing of writes. -/
def append (a b : Builder) : Builder where
  apply rest := a.apply (b.apply rest)
  invariant rest := by
    show a.apply (b.apply rest) = a.apply (b.apply []) ++ rest
    rw [a.invariant, b.invariant, a.invariant (b.apply []), List.append_assoc]

instance : Append Builder := ⟨append⟩

/-- Materialize the payload: `O(size)`.  Specifications are stated about
`toList`; `apply rest` is the continuation form used inside proofs. -/
def toList (b : Builder) : List UInt8 := b.apply []

@[simp] theorem apply_append (a b : Builder) (rest : List UInt8) :
    (a ++ b).apply rest = a.apply (b.apply rest) := rfl

@[simp] theorem apply_ofList (bs rest : List UInt8) :
    (ofList bs).apply rest = bs ++ rest := rfl

@[simp] theorem apply_empty (rest : List UInt8) : (∅ : Builder).apply rest = rest := rfl

@[simp] theorem toList_ofList (bs : List UInt8) : (ofList bs).toList = bs := by
  simp [toList]

theorem toList_empty : (∅ : Builder).toList = [] := rfl

@[simp] theorem toList_append (a b : Builder) :
    (a ++ b).toList = a.toList ++ b.toList := by
  show a.apply (b.apply []) = a.apply [] ++ b.apply []
  exact a.invariant _

@[simp] theorem toList_invariant (a : Builder) (rest : List UInt8) :
    a.toList ++ rest = a.apply rest := by
  rw [toList, ← a.invariant]

@[simp] theorem length_apply (b : Builder) (rest : List UInt8) :
    (b.apply rest).length = b.toList.length + rest.length := by
  rw [b.invariant rest, List.length_append]
  rfl

/-- Extensionality: builders with equal behaviour are equal. -/
@[ext] theorem ext {a b : Builder} (h : ∀ rest, a.apply rest = b.apply rest) : a = b := by
  obtain ⟨fa, ha⟩ := a
  obtain ⟨fb, hb⟩ := b
  have hfb : fa = fb := by
    funext rest
    exact h rest
  subst hfb
  rfl

theorem empty_append (b : Builder) : ∅ ++ b = b := by
  ext rest; rfl

theorem append_empty (b : Builder) : b ++ ∅ = b := by
  ext rest; rfl

theorem append_assoc (a b c : Builder) : (a ++ b) ++ c = a ++ (b ++ c) := rfl

/-! ## word primitive -/

/-- Write one 32-byte EVM word, big-endian. -/
def putWord (w : UInt256) : Builder := ofList (bytesOfWord w)

@[simp] theorem toList_putWord (w : UInt256) : (putWord w).toList = bytesOfWord w := by
  simp [putWord]

theorem apply_putWord (w : UInt256) (rest : List UInt8) :
    (putWord w).apply rest = bytesOfWord w ++ rest := rfl

end Builder

/-! ## Get2: the dual-cursor reader -/

/-- A dual-cursor prefix reader: consumes from a *head cursor* (the head
section of a canonical layout) and a *tail cursor* (the tails), threading
the expected tail frontier `E`.  Each component step advances one or both
cursors monotonically — no re-dropping from the front of the buffer — so
canonical layouts decode in a single pass.  The frontier is the absolute
position the next dynamic tail must occupy; a dynamic component's offset
word must equal it exactly. -/
structure Get2 (α : Type) where
  run : List UInt8 → List UInt8 → Nat → Option (α × List UInt8 × List UInt8 × Nat)

namespace Get2

instance : Monad Get2 where
  pure a := ⟨fun head tails E => some (a, head, tails, E)⟩
  bind x f := ⟨fun head tails E =>
    match x.run head tails E with
    | none => none
    | some (a, head', tails', E') => (f a).run head' tails' E'⟩

/-- Failure, cursors untouched. -/
def fail : Get2 α := ⟨fun _ _ _ => none⟩

@[simp] theorem pure_run (a : α) (head tails : List UInt8) (E : Nat) :
    (pure a : Get2 α).run head tails E = some (a, head, tails, E) := rfl

@[simp] theorem bind_run (x : Get2 α) (f : α → Get2 β) (head tails : List UInt8) (E : Nat) :
    (x >>= f).run head tails E = (match x.run head tails E with
      | none => none
      | some (a, head', tails', E') => (f a).run head' tails' E') := rfl

@[simp] theorem fail_run (head tails : List UInt8) (E : Nat) :
    (fail : Get2 α).run head tails E = none := rfl

end Get2

end EvmAbi
