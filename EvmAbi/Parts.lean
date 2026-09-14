import EvmAbi.Dynamic

/-!
# EvmAbi.Parts

The head/tail combinator (roadmap node 7) — the heart of the ABI layout —
in builder form (roadmap node 9).

A tuple encoding is a list of `Part`s; each part contributes a static
`head` (for dynamic parts: a 32-byte offset word computed by `putParts`)
and, when dynamic, a `tail`.  Heads and tails are `Builder`s
(`EvmAbi.Builder`), so the full encoding

```
putParts ps = putHeads (headSizes ps) ps ++ putTails ps
```

is assembled with `O(1)` composition and materialized once at the
boundary.  The list-level encoders `encodeHeads` / `encodeTails` /
`encodeParts` are those materializations (`Builder.toList`); all
specifications and the offset theorems are stated about them, unchanged
from the list-based formulation:

* `drop_headOffset_static` — a static part's head is found at its head offset;
* `wordAt_offset_append` — a dynamic part's head word *contains* its tail offset;
* `drop_tailOffset_append` — dropping to that offset lands exactly on the tail.
-/

namespace EvmAbi

open Binary

/-- One component of a tuple encoding: a static `head` and a dynamic
`tail`, both as builders.  For static components (`isDyn = false`) the
tail is empty; for dynamic components the head is the 32-byte offset word
computed by `putParts`. -/
structure Part where
  head : Builder
  tail : Builder
  isDyn : Bool

namespace Part

/-- Bytes this part occupies in the head section.  Read off the builder's
cached `size`: the layout asks for this once per part while writing the
offset words, so walking the chunk tree here would reintroduce the
`O(n · depth)` cost the builder exists to remove. -/
def headSize : Part → Nat
  | ⟨head, _, false⟩ => head.size
  | ⟨_, _, true⟩ => 32

/-- Bytes this part occupies in the tail section — the cached size again. -/
def tailSize : Part → Nat
  | ⟨_, _, false⟩ => 0
  | ⟨_, tail, true⟩ => tail.size

/-- Two parts are equivalent when they denote the same bytes and occupy
the same cached sizes. -/
def Equiv (p q : Part) : Prop :=
  p.isDyn = q.isDyn ∧
    p.head.toList = q.head.toList ∧
    p.tail.toList = q.tail.toList ∧
    p.head.size = q.head.size ∧
    p.tail.size = q.tail.size

/-- Equivalent parts have equal head sizes. -/
theorem headSize_eq_of_equiv {p q : Part} (h : Equiv p q) : headSize p = headSize q := by
  rcases h with ⟨hdyn, hhead, htail, hs1, hs2⟩
  obtain ⟨ph, pt, pd⟩ := p; obtain ⟨qh, qt, qd⟩ := q
  cases pd <;> cases qd <;> grind [Equiv, headSize]

/-- Equivalent parts have equal tail sizes. -/
theorem tailSize_eq_of_equiv {p q : Part} (h : Equiv p q) : tailSize p = tailSize q := by
  rcases h with ⟨hdyn, hhead, htail, hs1, hs2⟩
  obtain ⟨ph, pt, pd⟩ := p; obtain ⟨qh, qt, qd⟩ := q
  cases pd <;> cases qd <;> grind [Equiv, tailSize]

end Part

/-- Total size of the head section. -/
def headSizes : List Part → Nat
  | [] => 0
  | p :: ps => p.headSize + headSizes ps

/-- Total size of the tail section. -/
def tailSizes : List Part → Nat
  | [] => 0
  | p :: ps => p.tailSize + tailSizes ps

/-- Byte offset at which part `i`'s tail starts in the full encoding:
the whole head section plus the tails of the preceding dynamic parts. -/
def tailOffset (ps : List Part) (i : Nat) : Nat := headSizes ps + tailSizes (ps.take i)

/-! ## the builder assembly -/

/-- Build the head section; `acc` is the byte offset of the current part's
tail (total head size plus the sizes of the preceding tails). -/
def putHeads (acc : Nat) : List Part → Builder
  | [] => ∅
  | ⟨head, _, false⟩ :: ps => head ++ putHeads acc ps
  | ⟨_, tail, true⟩ :: ps => putUint acc ++ putHeads (acc + tail.size) ps

/-- Build the tail section: the dynamic tails, in order. -/
def putTails : List Part → Builder
  | [] => ∅
  | ⟨_, _, false⟩ :: ps => putTails ps
  | ⟨_, tail, true⟩ :: ps => tail ++ putTails ps

/-- Full tuple builder: the head section followed by the tails. -/
def putParts (ps : List Part) : Builder :=
  putHeads (headSizes ps) ps ++ putTails ps

/-! ## the list-level materialization -/

/-- Materialized head section. -/
def encodeHeads (acc : Nat) (ps : List Part) : List UInt8 := (putHeads acc ps).toList

/-- Materialized tail section. -/
def encodeTails (ps : List Part) : List UInt8 := (putTails ps).toList

/-- Materialized full tuple encoding. -/
def encodeParts (ps : List Part) : List UInt8 := (putParts ps).toList

/-- `encodeParts` in the classical head/tail-append form. -/
theorem encodeParts_unfold (ps : List Part) :
    encodeParts ps = encodeHeads (headSizes ps) ps ++ encodeTails ps := by
  simp [encodeParts, putParts, encodeHeads, encodeTails]

/-- cons equations for the materialized encoders. -/
theorem encodeHeads_cons_static (acc : Nat) (head tail : Builder) (ys : List Part) :
    encodeHeads acc (⟨head, tail, false⟩ :: ys) = head.toList ++ encodeHeads acc ys := by
  simp [encodeHeads, putHeads]

theorem encodeHeads_cons_dynamic (acc : Nat) (head tail : Builder) (ys : List Part) :
    encodeHeads acc (⟨head, tail, true⟩ :: ys) =
      encodeUint acc ++ encodeHeads (acc + tail.toList.length) ys := by
  simp [encodeHeads, putHeads]

theorem encodeTails_cons_static (head tail : Builder) (ys : List Part) :
    encodeTails (⟨head, tail, false⟩ :: ys) = encodeTails ys := by
  simp [encodeTails, putTails]

theorem encodeTails_cons_dynamic (head tail : Builder) (ys : List Part) :
    encodeTails (⟨head, tail, true⟩ :: ys) = tail.toList ++ encodeTails ys := by
  simp [encodeTails, putTails]

/-! ## sizes -/

@[simp] theorem length_putHeads (acc : Nat) (ps : List Part) :
    ((putHeads acc ps).toList).length = headSizes ps := by
  induction ps generalizing acc with
  | nil => grind [putHeads, headSizes, Builder.toList_empty]
  | cons p ps ih =>
      obtain ⟨head, tail, isDyn⟩ := p
      cases isDyn <;>
        grind [putHeads, headSizes, Part.headSize, Builder.toList_append,
          Builder.size_eq_length_toList, length_encodeUint, toList_putUint]

@[simp] theorem length_encodeHeads (acc : Nat) (ps : List Part) :
    (encodeHeads acc ps).length = headSizes ps := length_putHeads acc ps

@[simp] theorem length_putTails (ps : List Part) :
    ((putTails ps).toList).length = tailSizes ps := by
  induction ps with
  | nil => grind [putTails, tailSizes, Builder.toList_empty]
  | cons p ps ih =>
      obtain ⟨head, tail, isDyn⟩ := p
      cases isDyn <;>
        grind [putTails, tailSizes, Part.tailSize, Builder.toList_append,
          Builder.size_eq_length_toList]

@[simp] theorem length_encodeTails (ps : List Part) :
    (encodeTails ps).length = tailSizes ps := length_putTails ps

theorem length_encodeParts (ps : List Part) :
    (encodeParts ps).length = headSizes ps + tailSizes ps := by
  simp [encodeParts, putParts]

theorem headSizes_append (xs ys : List Part) :
    headSizes (xs ++ ys) = headSizes xs + headSizes ys := by
  induction xs with
  | nil => grind [headSizes]
  | cons x xs ih => grind [headSizes]

theorem tailSizes_append (xs ys : List Part) :
    tailSizes (xs ++ ys) = tailSizes xs + tailSizes ys := by
  induction xs with
  | nil => grind [tailSizes]
  | cons x xs ih => grind [tailSizes]

/-! ## append lemmas for the encoders -/

/- `Builder.append` is a `Chunks` constructor, so it is associative only up
to `toList` — `(a ++ b) ++ c` and `a ++ (b ++ c)` are different trees
denoting the same bytes.  The append laws are therefore stated of the
materialization, which is all the codec ever uses. -/

theorem encodeHeads_append (acc : Nat) (xs ys : List Part) :
    encodeHeads acc (xs ++ ys) = encodeHeads acc xs ++ encodeHeads (acc + tailSizes xs) ys := by
  induction xs generalizing acc with
  | nil => grind [encodeHeads, putHeads, tailSizes, Builder.toList_empty]
  | cons x xs ih =>
      obtain ⟨head, tail, isDyn⟩ := x
      cases isDyn <;>
        grind [encodeHeads, encodeHeads_cons_static, encodeHeads_cons_dynamic,
          tailSizes, Part.tailSize, List.append_assoc, Builder.size_eq_length_toList]

theorem encodeTails_append (xs ys : List Part) :
    encodeTails (xs ++ ys) = encodeTails xs ++ encodeTails ys := by
  induction xs with
  | nil => grind [encodeTails, putTails, Builder.toList_empty]
  | cons x xs ih =>
      obtain ⟨head, tail, isDyn⟩ := x
      cases isDyn <;>
        grind [encodeTails, encodeTails_cons_static, encodeTails_cons_dynamic,
          List.append_assoc]

/-! ## well-formedness -/

/-- Well-formed parts: every static head and every tail is 32-byte aligned. -/
def WF (ps : List Part) : Prop :=
  ∀ p ∈ ps, 32 ∣ p.head.toList.length ∧ 32 ∣ p.tail.toList.length

theorem dvd_headSizes (hwf : WF ps) : 32 ∣ headSizes ps := by
  induction ps with
  | nil => grind [headSizes]
  | cons p ps ih =>
      have hp := hwf p List.mem_cons_self
      have hih := ih (fun q hq => hwf q (List.mem_cons_of_mem p hq))
      obtain ⟨head, tail, isDyn⟩ := p
      cases isDyn <;>
        grind [headSizes, Part.headSize, WF, Builder.size_eq_length_toList,
          Builder.toList_append]

theorem dvd_tailSizes (hwf : WF ps) : 32 ∣ tailSizes ps := by
  induction ps with
  | nil => grind [tailSizes]
  | cons p ps ih =>
      have hp := hwf p List.mem_cons_self
      have hih := ih (fun q hq => hwf q (List.mem_cons_of_mem p hq))
      obtain ⟨head, tail, isDyn⟩ := p
      cases isDyn <;>
        grind [tailSizes, Part.tailSize, WF, Builder.size_eq_length_toList]

theorem dvd_length_encodeParts (hwf : WF ps) : 32 ∣ (encodeParts ps).length := by
  rw [length_encodeParts]
  have h1 := dvd_headSizes hwf
  have h2 := dvd_tailSizes hwf
  omega

/-- Well-formedness constructors (handy for concrete part lists). -/
theorem wf_nil : WF [] := fun _q hq => (List.not_mem_nil hq).elim

theorem wf_cons (hp : 32 ∣ p.head.toList.length ∧ 32 ∣ p.tail.toList.length)
    (hps : WF ps) : WF (p :: ps) := fun q hq => by
  simp only [List.mem_cons] at hq
  cases hq with
  | inl h => subst h; exact hp
  | inr h => exact hps q h

/-! ## the fundamental theorems -/

/-- **Fundamental theorem, dynamic case**: dropping to a dynamic part's tail
offset lands exactly on its tail — the offsets written into the head words
are correct. -/
theorem drop_tailOffset_append (xs : List Part) (head tail : Builder) (ys : List Part) :
    (encodeParts (xs ++ ⟨head, tail, true⟩ :: ys)).drop
      (tailOffset (xs ++ ⟨head, tail, true⟩ :: ys) xs.length) =
    tail.toList ++ encodeTails ys := by
  grind [encodeParts_unfold, tailOffset, take_append_of_length, drop_append_of_length,
    encodeTails_append, length_encodeHeads, length_encodeTails, encodeTails_cons_dynamic]

/-- **Fundamental theorem, static case**: a static part's head is found at
its head offset. -/
theorem drop_headOffset_static (xs : List Part) (head tail : Builder) (ys : List Part) :
    (encodeParts (xs ++ ⟨head, tail, false⟩ :: ys)).drop (headSizes xs) =
      head.toList ++ (encodeHeads (headSizes (xs ++ ⟨head, tail, false⟩ :: ys) +
        tailSizes xs) ys ++ encodeTails (xs ++ ⟨head, tail, false⟩ :: ys)) := by
  rw [encodeParts_unfold, encodeHeads_append, encodeHeads_cons_static]
  simp only [List.append_assoc]
  rw [drop_append_of_length (length_encodeHeads _ _)]

/-- **Fundamental theorem, offset words**: the head word of a dynamic part
contains exactly its tail offset. -/
theorem wordAt_offset_append (hwf : WF (xs ++ ⟨head, tail, true⟩ :: ys)) :
    wordAt (encodeParts (xs ++ ⟨head, tail, true⟩ :: ys)) (headSizes xs / 32) =
      some (UInt256.ofNat (tailOffset (xs ++ ⟨head, tail, true⟩ :: ys) xs.length)) := by
  have hwfx : WF xs := fun q hq => hwf q (List.mem_append_left _ hq)
  have hA : (encodeHeads (headSizes (xs ++ ⟨head, tail, true⟩ :: ys)) xs).length =
      32 * (headSizes xs / 32) := by
    rw [length_encodeHeads]
    have hdv := dvd_headSizes hwfx
    omega
  rw [encodeParts_unfold, encodeHeads_append, encodeHeads_cons_dynamic, tailOffset,
    take_append_of_length rfl]
  simp only [List.append_assoc]
  exact wordAt_append _ _ _ _ hA

end EvmAbi
