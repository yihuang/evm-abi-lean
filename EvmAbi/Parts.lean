import EvmAbi.Dynamic

/-!
# EvmAbi.Parts

The head/tail combinator (roadmap node 7) — the heart of the ABI layout.

A tuple encoding is a list of `Part`s; each part contributes a static
`head` (for dynamic parts: a 32-byte offset word computed by `encodeParts`)
and, when dynamic, a `tail`. The full encoding is

```
encodeParts ps = encodeHeads (headSizes ps) ps ++ encodeTails ps
```

The fundamental theorems:

* `drop_headOffset_static` — a static part's head is found at its head offset;
* `wordAt_offset_append` — a dynamic part's head word *contains* its tail offset;
* `drop_tailOffset_append` — dropping to that offset lands exactly on the tail.
-/

namespace EvmAbi

open Binary

/-- One component of a tuple encoding: a static `head` and a dynamic `tail`.
For static components (`isDyn = false`) the tail is empty; for dynamic
components the head is the 32-byte offset word computed by `encodeParts`. -/
structure Part where
  head : List UInt8
  tail : List UInt8
  isDyn : Bool

namespace Part

/-- Bytes this part occupies in the head section. -/
def headSize : Part → Nat
  | ⟨head, _, false⟩ => head.length
  | ⟨_, _, true⟩ => 32

/-- Bytes this part occupies in the tail section. -/
def tailSize : Part → Nat
  | ⟨_, _, false⟩ => 0
  | ⟨_, tail, true⟩ => tail.length

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

/-- Encode the head section; `acc` is the byte offset of the current part's
tail (total head size plus the sizes of the preceding tails). -/
def encodeHeads (acc : Nat) : List Part → List UInt8
  | [] => []
  | ⟨head, _, false⟩ :: ps => head ++ encodeHeads acc ps
  | ⟨_, tail, true⟩ :: ps => encodeUint acc ++ encodeHeads (acc + tail.length) ps

/-- Encode the tail section: the dynamic tails, in order. -/
def encodeTails : List Part → List UInt8
  | [] => []
  | ⟨_, _, false⟩ :: ps => encodeTails ps
  | ⟨_, tail, true⟩ :: ps => tail ++ encodeTails ps

/-- Full tuple encoding: the head section followed by the tails. -/
def encodeParts (ps : List Part) : List UInt8 :=
  encodeHeads (headSizes ps) ps ++ encodeTails ps

/-! ## sizes -/

@[simp] theorem length_encodeHeads (acc : Nat) (ps : List Part) :
    (encodeHeads acc ps).length = headSizes ps := by
  induction ps generalizing acc with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨head, tail, isDyn⟩ := p
      cases isDyn <;>
        simp [encodeHeads, headSizes, Part.headSize, ih, length_encodeUint]

@[simp] theorem length_encodeTails (ps : List Part) :
    (encodeTails ps).length = tailSizes ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨head, tail, isDyn⟩ := p
      cases isDyn <;> simp [encodeTails, tailSizes, Part.tailSize, ih]

theorem length_encodeParts (ps : List Part) :
    (encodeParts ps).length = headSizes ps + tailSizes ps := by
  rw [encodeParts, List.length_append, length_encodeHeads, length_encodeTails]

theorem headSizes_append (xs ys : List Part) :
    headSizes (xs ++ ys) = headSizes xs + headSizes ys := by
  induction xs with
  | nil => simp [headSizes]
  | cons x xs ih => simp [List.cons_append, headSizes, ih, Nat.add_assoc]

theorem tailSizes_append (xs ys : List Part) :
    tailSizes (xs ++ ys) = tailSizes xs + tailSizes ys := by
  induction xs with
  | nil => simp [tailSizes]
  | cons x xs ih => simp [List.cons_append, tailSizes, ih, Nat.add_assoc]

/-! ## append lemmas for the encoders -/

theorem encodeHeads_append (acc : Nat) (xs ys : List Part) :
    encodeHeads acc (xs ++ ys) = encodeHeads acc xs ++ encodeHeads (acc + tailSizes xs) ys := by
  induction xs generalizing acc with
  | nil => simp [encodeHeads, tailSizes]
  | cons x xs ih =>
      obtain ⟨head, tail, isDyn⟩ := x
      cases isDyn <;>
        simp [List.cons_append, encodeHeads, tailSizes, Part.tailSize, ih,
          List.append_assoc, Nat.add_assoc]

theorem encodeTails_append (xs ys : List Part) :
    encodeTails (xs ++ ys) = encodeTails xs ++ encodeTails ys := by
  induction xs with
  | nil => simp [encodeTails]
  | cons x xs ih =>
      obtain ⟨head, tail, isDyn⟩ := x
      cases isDyn <;> simp [List.cons_append, encodeTails, ih, List.append_assoc]

/-! ## well-formedness -/

/-- Well-formed parts: every static head and every tail is 32-byte aligned. -/
def WF (ps : List Part) : Prop := ∀ p ∈ ps, 32 ∣ p.head.length ∧ 32 ∣ p.tail.length

theorem dvd_headSizes (hwf : WF ps) : 32 ∣ headSizes ps := by
  induction ps with
  | nil => exact ⟨0, rfl⟩
  | cons p ps ih =>
      have hp := hwf p List.mem_cons_self
      have hih := ih (fun q hq => hwf q (List.mem_cons_of_mem p hq))
      obtain ⟨head, tail, isDyn⟩ := p
      have hp1 : 32 ∣ head.length := hp.1
      cases isDyn <;> simp [headSizes, Part.headSize] <;> omega

theorem dvd_tailSizes (hwf : WF ps) : 32 ∣ tailSizes ps := by
  induction ps with
  | nil => exact ⟨0, rfl⟩
  | cons p ps ih =>
      have hp := hwf p List.mem_cons_self
      have hih := ih (fun q hq => hwf q (List.mem_cons_of_mem p hq))
      obtain ⟨head, tail, isDyn⟩ := p
      have hp2 : 32 ∣ tail.length := hp.2
      cases isDyn <;> simp [tailSizes, Part.tailSize] <;> omega

theorem dvd_length_encodeParts (hwf : WF ps) : 32 ∣ (encodeParts ps).length := by
  rw [length_encodeParts]
  have h1 := dvd_headSizes hwf
  have h2 := dvd_tailSizes hwf
  omega

/-- Well-formedness constructors (handy for concrete part lists). -/
theorem wf_nil : WF [] := fun _q hq => (List.not_mem_nil hq).elim

theorem wf_cons (hp : 32 ∣ p.head.length ∧ 32 ∣ p.tail.length) (hps : WF ps) :
    WF (p :: ps) := fun q hq => by
  simp only [List.mem_cons] at hq
  cases hq with
  | inl h => subst h; exact hp
  | inr h => exact hps q h

/-! ## the fundamental theorems -/

/-- **Fundamental theorem, dynamic case**: dropping to a dynamic part's tail
offset lands exactly on its tail — the offsets written into the head words
are correct. -/
theorem drop_tailOffset_append (xs : List Part) (head tail : List UInt8) (ys : List Part) :
    (encodeParts (xs ++ ⟨head, tail, true⟩ :: ys)).drop
      (tailOffset (xs ++ ⟨head, tail, true⟩ :: ys) xs.length) =
    tail ++ encodeTails ys := by
  rw [encodeParts, tailOffset, take_append_of_length rfl, ← List.drop_drop,
    drop_append_of_length (length_encodeHeads _ _), encodeTails_append,
    drop_append_of_length (length_encodeTails xs), encodeTails]

/-- **Fundamental theorem, static case**: a static part's head is found at
its head offset. -/
theorem drop_headOffset_static (xs : List Part) (head tail : List UInt8) (ys : List Part) :
    (encodeParts (xs ++ ⟨head, tail, false⟩ :: ys)).drop (headSizes xs) =
      head ++ (encodeHeads (headSizes (xs ++ ⟨head, tail, false⟩ :: ys) + tailSizes xs) ys ++
        encodeTails (xs ++ ⟨head, tail, false⟩ :: ys)) := by
  rw [encodeParts, encodeHeads_append, encodeHeads]
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
  rw [encodeParts, encodeHeads_append, encodeHeads, tailOffset, take_append_of_length rfl]
  simp only [List.append_assoc]
  exact wordAt_append _ _ _ _ hA

end EvmAbi
