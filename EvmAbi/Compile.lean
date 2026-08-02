import EvmAbi.Codec.Runtime

/-!
# EvmAbi.Compile

The **target language of the ABI compiler**: a tiny abstract machine for the
head/tail layout, whose every step is proved once against the generic
encoder `putBA` (`EvmAbi.Codec.Runtime`).

The generic encoder is *interpretive*: `putBA` recurses on the `Ty` while it
walks the value, `partOfBA` asks `t.isStatic` per component (and per array
*element*), `partsOfTupleBA` allocates a `List Part`, and `putParts` then
walks that list three more times (`headSizes`, `putHeads`, `putTails`).  All
of that is determined by the type alone, so for a *fixed* type it can be
decided at compile time.

`EvmAbi.Compile.Meta` does exactly that: it emits, for a given type, straight
code in terms of the machine below, together with a machine-checked proof
that the code denotes the same bytes as `putBA`.  The machine is what makes
those proofs cheap — the emitter never invents a proof, it chains the lemmas
proved here, one per emitted instruction.

The machine state `Acc` is the layout under construction: the head section
so far, the offset the next dynamic tail will occupy (the frontier the
decoder checks), and the tail section so far.  There are two instructions —
`static` (inline the component in the head) and `dyn` (write the frontier as
an offset word, append the component to the tails) — plus `start` and
`finish`.  `Inv` says the state is exactly what `putHeads`/`putTails` would
have built from the parts consumed so far, and every instruction preserves
it, so a compiled encoder is correct by composition of its steps.

One loop (`elems`) runs one instruction per element of an array: an array is
homogeneous, so *which* instruction is chosen once, at compile time, and the
loop that remains is the only recursion left in compiled code.
-/

namespace EvmAbi
namespace Compile

open Ty Binary Builder

/-! ## the contract

`Denotes t f` is what every emitted encoder is proved to satisfy: `f` writes,
for every value, exactly the bytes the generic encoder writes.  Emitted
statements are therefore binder-free — `Denotes ty node3` — and compose, each
clause below turning its sub-encoders' contracts into the contract of the code
emitted for the node above. -/

/-- A compiled encoder for `t` denotes the generic one. -/
def Denotes (t : Ty) (f : ValBA t → Builder) : Prop :=
  ∀ v, (f v).toList = (putBA t v).toList

/-- A static component's part is its encoding, inline in the head. -/
theorem partOfBA_static {t : Ty} (v : ValBA t) (hs : t.isStatic = true) :
    partOfBA t v = ⟨putBA t v, ∅, false⟩ := by simp [partOfBA, hs]

/-- A dynamic component's part is a tail, reached through an offset word. -/
theorem partOfBA_dynamic {t : Ty} (v : ValBA t) (hs : t.isStatic = false) :
    partOfBA t v = ⟨∅, putBA t v, true⟩ := by simp [partOfBA, hs]

/-! ## the machine -/

/-- The state of the layout machine: the head section built so far, the
absolute offset the next dynamic tail will occupy, and the tail section
built so far. -/
structure Acc where
  /-- Head section so far. -/
  head : Builder
  /-- Offset of the next dynamic tail (the decoder's frontier). -/
  off : Nat
  /-- Tail section so far. -/
  tail : Builder

namespace Acc

/-- Start a layout whose head section is `H` bytes: the first tail goes
right after the head. -/
@[inline] def start (H : Nat) : Acc := ⟨∅, H, ∅⟩

/-- Emit a static component: it sits inline in the head, and no tail
moves. -/
@[inline] def static (s : Acc) (b : Builder) : Acc := ⟨s.head ++ b, s.off, s.tail⟩

/-- Emit a dynamic component: the head takes an offset word pointing at the
current frontier, the component goes to the tails, and the frontier advances
by its size (the builder's cached count — never a walk). -/
@[inline] def dyn (s : Acc) (b : Builder) : Acc :=
  ⟨s.head ++ putUint s.off, s.off + b.size, s.tail ++ b⟩

/-- Close the layout: head section, then tails. -/
@[inline] def finish (s : Acc) : Builder := s.head ++ s.tail

/-- Run one instruction per element.  An array is homogeneous, so `step` is
`static` or `dyn` throughout and is chosen once, at compile time;
`@[specialize]` is what turns that choice into a specialised loop. -/
@[specialize] def elems (step : Acc → Builder → Acc) (f : α → Builder) (s : Acc) : List α → Acc
  | [] => s
  | v :: vs => elems step f (step s (f v)) vs

/-! ## the machine invariant -/

/-- The state is exactly what the generic layout would have built from the
parts `ps` consumed so far, inside a layout whose head section is `H`
bytes.  A structure, not a conjunction, so that emitted proofs can chain the
instruction lemmas below with dot notation. -/
structure Inv (H : Nat) (s : Acc) (ps : List Part) : Prop where
  /-- The head section so far is the generic head section of `ps`. -/
  head_eq : s.head.toList = encodeHeads H ps
  /-- The frontier is the head section plus the tails written so far. -/
  off_eq : s.off = H + tailSizes ps
  /-- The tail section so far is the generic tail section of `ps`. -/
  tail_eq : s.tail.toList = encodeTails ps

theorem start_inv (H : Nat) : Inv H (start H) [] :=
  ⟨rfl, rfl, rfl⟩

/-- `static` preserves the invariant: any builder denoting the component's
encoding may be inlined. -/
theorem Inv.static {H : Nat} {s : Acc} {ps : List Part} (h : Inv H s ps)
    {t : Ty} {v : ValBA t} {b : Builder} (hs : t.isStatic = true)
    (hb : b.toList = (putBA t v).toList) :
    Inv H (s.static b) (ps ++ [partOfBA t v]) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hp := partOfBA_static v hs
  refine ⟨?_, ?_, ?_⟩
  · show (s.head ++ b).toList = _
    rw [Builder.toList_append, h1, hp, encodeHeads_append, encodeHeads_cons_static, hb]
    simp [encodeHeads, putHeads]
  · show s.off = _
    rw [h2, hp, tailSizes_append]
    simp [tailSizes, Part.tailSize]
  · show s.tail.toList = _
    rw [h3, hp, encodeTails_append, encodeTails_cons_static]
    simp [encodeTails, putTails]

/-- `dyn` preserves the invariant: the offset word it writes is the frontier,
which is where the tail it appends actually lands. -/
theorem Inv.dyn {H : Nat} {s : Acc} {ps : List Part} (h : Inv H s ps)
    {t : Ty} {v : ValBA t} {b : Builder} (hs : t.isStatic = false)
    (hb : b.toList = (putBA t v).toList) :
    Inv H (s.dyn b) (ps ++ [partOfBA t v]) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hp := partOfBA_dynamic v hs
  have hsz : b.size = (putBA t v).size := by
    rw [Builder.size_eq_length_toList, Builder.size_eq_length_toList, hb]
  refine ⟨?_, ?_, ?_⟩
  · show (s.head ++ putUint s.off).toList = _
    rw [Builder.toList_append, h1, toList_putUint, h2, hp, encodeHeads_append,
      encodeHeads_cons_dynamic]
    simp [encodeHeads, putHeads]
  · show s.off + b.size = _
    rw [hsz, h2, hp, tailSizes_append]
    simp [tailSizes, Part.tailSize, Builder.size_eq_length_toList, Nat.add_assoc]
  · show (s.tail ++ b).toList = _
    rw [Builder.toList_append, h3, hb, hp, encodeTails_append, encodeTails_cons_dynamic]
    simp [encodeTails, putTails]

/-- `finish` closes a complete layout: once the parts consumed are all of
them, the machine's two sections *are* the generic encoding. -/
theorem Inv.finish_toList {H : Nat} {s : Acc} {ps : List Part} (h : Inv H s ps)
    (hH : H = headSizes ps) : s.finish.toList = (putParts ps).toList := by
  obtain ⟨h1, h2, h3⟩ := h
  show (s.head ++ s.tail).toList = _
  rw [Builder.toList_append, h1, h3, hH]
  rfl

end Acc

/-! ## per-component facts

The compiler needs to know, at compile time, what a component contributes to
the head section.  These are the `ValBA` counterparts of the `Spec` lemmas in
`EvmAbi.Codec`, transported by `toList_putBA`. -/

/-- A static component's builder occupies exactly its type's head size. -/
theorem size_putBA_static (t : Ty) (hs : t.isStatic = true) (hv : t.Valid) (v : ValBA t) :
    (putBA t v).size = t.headSize := by
  rw [Builder.size_eq_length_toList, toList_putBA]
  exact Spec.encode_length_static t hs hv _

/-- A component's part occupies exactly its type's head size: its own
encoding when static, one offset word when dynamic. -/
theorem headSize_partOfBA (t : Ty) (hv : t.Valid) (v : ValBA t) :
    (partOfBA t v).headSize = t.headSize := by
  cases hs : t.isStatic
  · rw [partOfBA_dynamic v hs]
    exact (Spec.headSize_of_dynamic t hs).symm
  · rw [partOfBA_static v hs]
    exact size_putBA_static t hs hv v

/-- The head section of a tuple is the sum of its components' head sizes —
a compile-time constant. -/
theorem headSizes_partsOfTupleBA : (ts : List Ty) → AllValid ts → (v : TupleValBA ts) →
    headSizes (partsOfTupleBA ts v) = headSizeSum ts
  | [], _, v => by rw [partsOfTupleBA.eq_1]; rfl
  | t :: ts, hv, (v, vs) => by
      rw [partsOfTupleBA.eq_2]
      simp only [headSizes, headSize_partOfBA t hv.1 v, headSizeSum]
      rw [headSizes_partsOfTupleBA ts hv.2 vs]

/-- The head section of an array is one slot per element. -/
theorem headSizes_map_partOfBA (t : Ty) (hv : t.Valid) :
    (vs : List (ValBA t)) → headSizes (vs.map (partOfBA t)) = vs.length * t.headSize
  | [] => by simp [headSizes]
  | v :: vs => by
      rw [List.map_cons]
      simp only [headSizes, headSize_partOfBA t hv v, List.length_cons]
      rw [headSizes_map_partOfBA t hv vs, Nat.succ_mul]
      omega

/-! ## the element loop

An array runs the same instruction per element.  `Step` is what that
instruction has to do — extend the state by one component's part — so the loop
and the section lemma below are proved once and instantiated twice. -/

namespace Acc

/-- A compiled instruction for components of type `t`: it extends the state by
exactly that component's part. -/
def Step (t : Ty) (step : Acc → Builder → Acc) (f : ValBA t → Builder) : Prop :=
  ∀ (v : ValBA t) {H : Nat} {s : Acc} {ps : List Part}, Inv H s ps →
    Inv H (step s (f v)) (ps ++ [partOfBA t v])

/-- Inlining a static component is such an instruction. -/
theorem Inv.stepStatic {t : Ty} {f : ValBA t → Builder} (hs : t.isStatic = true)
    (hf : Denotes t f) : Step t Acc.static f :=
  fun v {_ _ _} h => h.static hs (hf v)

/-- So is writing a dynamic component's offset word. -/
theorem Inv.stepDyn {t : Ty} {f : ValBA t → Builder} (hs : t.isStatic = false)
    (hf : Denotes t f) : Step t Acc.dyn f :=
  fun v {_ _ _} h => h.dyn hs (hf v)

/-- The loop preserves the invariant, one part per element. -/
theorem Inv.loop {t : Ty} {step : Acc → Builder → Acc} {f : ValBA t → Builder}
    (hstep : Step t step f) :
    ∀ (vs : List (ValBA t)) {H : Nat} {s : Acc} {ps : List Part}, Inv H s ps →
      Inv H (elems step f s vs) (ps ++ vs.map (partOfBA t))
  | [], _, _, _, h => by simpa [elems] using h
  | v :: vs, H, s, ps, h => by
      rw [elems, List.map_cons, ← List.singleton_append, ← List.append_assoc]
      exact Inv.loop hstep vs (hstep v h)

/-- **Compiled array section**: the loop denotes the generic element layout. -/
theorem toList_elems {t : Ty} (hv : t.Valid) {step : Acc → Builder → Acc}
    {f : ValBA t → Builder} (hstep : Step t step f) (vs : List (ValBA t)) :
    ((start (vs.length * t.headSize)).elems step f vs).finish.toList =
      (putParts (vs.map (partOfBA t))).toList := by
  refine Inv.finish_toList (H := vs.length * t.headSize) ?_ ?_
  · simpa using Inv.loop hstep vs (start_inv _)
  · rw [headSizes_map_partOfBA t hv vs]

end Acc

/-! ## the leaves -/

theorem denotes_uint (m : Nat) : Denotes (.uint m) (fun v => putUint v.val) := by
  rintro ⟨n, h⟩; rw [putBA.eq_1]

theorem denotes_int (m : Nat) : Denotes (.int m) (fun v => putInt v.val) := by
  rintro ⟨i, h⟩; rw [putBA.eq_2]

theorem denotes_bool : Denotes .bool (fun v => putBool v) := by
  intro v; rw [putBA.eq_3]

theorem denotes_address : Denotes .address (fun v => putAddress v.val) := by
  rintro ⟨n, h⟩; rw [putBA.eq_4]

theorem denotes_bytesN (m : Nat) : Denotes (.bytesN m) (fun v => putBytesNBA v.val) := by
  rintro ⟨bs, h⟩; rw [putBA.eq_5]

theorem denotes_bytes : Denotes .bytes (fun v => putBytesBA v.val) := by
  rintro ⟨bs, h⟩; rw [putBA.eq_6]

theorem denotes_string : Denotes .string (fun v => putString v.val) := by
  rintro ⟨s, h⟩; rw [putBA.eq_7]

/-! ## the compound clauses

The emitted code is the function in the conclusion; the emitted proof is the
lemma applied to the element/component contracts. -/

/-- **Compiled `T[]`**: the length word, then the compiled element section. -/
theorem denotes_array {t : Ty} (hv : t.Valid) {step : Acc → Builder → Acc}
    {f : ValBA t → Builder} (hstep : Acc.Step t step f) :
    Denotes (.array t) (fun v => putUint v.val.length ++
      ((Acc.start (v.val.length * t.headSize)).elems step f v.val).finish) := by
  rintro ⟨vs, hb⟩
  rw [putBA.eq_8, Builder.toList_append, Builder.toList_append,
    Acc.toList_elems hv hstep vs]

/-- **Compiled `T[k]`**: the element section alone — no length word. -/
theorem denotes_fixedArray {t : Ty} {n : Nat} (hv : t.Valid) {step : Acc → Builder → Acc}
    {f : ValBA t → Builder} (hstep : Acc.Step t step f) :
    Denotes (.fixedArray t n) (fun v =>
      ((Acc.start (v.val.length * t.headSize)).elems step f v.val).finish) := by
  rintro ⟨vs, hb⟩
  rw [putBA.eq_9, Acc.toList_elems hv hstep vs]

/-- **Compiled `(T₁, …, Tₙ)`**: whatever the machine built from the tuple's
parts, closed with `finish`.  The emitter supplies the run of instructions —
one `static`/`dyn` per component — and this lemma turns the state they end in
into an encoding. -/
theorem toList_tuple {ts : List Ty} (hv : AllValid ts) {s : Acc} (v : TupleValBA ts)
    (h : Acc.Inv (headSizeSum ts) s (partsOfTupleBA ts v)) :
    s.finish.toList = (putBA (.tuple ts) v).toList := by
  rw [putBA.eq_10]
  exact h.finish_toList (headSizes_partsOfTupleBA ts hv v).symm

/-- The tuple's part list, one rewrite per component. -/
theorem partsOfTupleBA_nil (v : TupleValBA []) : partsOfTupleBA [] v = [] :=
  partsOfTupleBA.eq_1 v

/-- The tuple's part list, one rewrite per component — stated with
projections rather than a pair pattern, so that emitted proofs can rewrite
with it without destructuring the value first (the two forms agree by
structure eta). -/
theorem partsOfTupleBA_cons (t : Ty) (ts : List Ty) (v : TupleValBA (t :: ts)) :
    partsOfTupleBA (t :: ts) v = partOfBA t v.1 :: partsOfTupleBA ts v.2 :=
  partsOfTupleBA.eq_2 t ts v.1 v.2

/-! ## from builder to bytes

A compiled encoder is a `Builder`; the user-facing one runs it.  `run` is
determined by the denotation, so a compiled encoder proved equal to `putBA`
*as bytes* is equal to `encode` *as a `ByteArray`* — the tree shape need not
match, and it does not: the machine's appends associate to the left, the
generic layout's to the right. -/

/-- **The compiler's correctness statement**: a compiled encoder runs to
exactly what `encode` produces. -/
theorem run_eq_encode {t : Ty} {f : ValBA t → Builder} (hf : Denotes t f) (v : ValBA t) :
    (f v).run = encode t v := by
  rw [Builder.run_eq_toByteArray, hf v, ← Builder.run_eq_toByteArray, encode]

/-- The compiled encoder inherits the verified roundtrip: what it writes,
`decodeStrict` reads back as the very same value. -/
theorem decodeStrict_run {t : Ty} {f : ValBA t → Builder} (hf : Denotes t f)
    (hv : t.Valid) (v : ValBA t) (hb : (f v).run.size < 2 ^ 256) :
    decodeStrict t ((f v).run) = some v := by
  rw [run_eq_encode hf v] at hb ⊢
  exact decodeStrict_encode t hv v hb

end Compile
end EvmAbi
