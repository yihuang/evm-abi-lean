import EvmAbi.Compile

/-!
# EvmAbi.Compile.Decode

The **decoder half of the compiler's target language**, in `namespace
EvmAbi.Compile.Decode`: readers that a compiled decoder is assembled
from, each proved once against the generic runtime decoder `decodeBAVal`
(`EvmAbi.Codec.ByteArray`).

The generic decoder is interpretive in exactly the way the encoder was:
`decodeBAVal` matches on the `Ty` at every value, `decodeElemBAVal` asks
`t.isStatic` at every component *and every array element* (a walk over the
type, not a test), and `decodeElemsBAVal`/`decodeTupleBAVal` rebuild their
`GetBA` programs as they go.  For a fixed type all of it is known at compile
time.

The readers below are the compiled forms.  `elemStatic`/`elemDyn` read one
component — inline at the head cursor, or behind an offset word that must
equal the frontier — and are the only place that choice survives compilation:
`cons` chains one onto the reader for the remaining components, so a compiled
tuple is a nest of combinators with no `Ty` left in it, and `elems` runs one
per array element.
`readArray`/`readFixedArray`/`readTuple` are the three compound clauses of
`decodeBAVal` with their head sizes taken as *parameters* — the emitter
passes numerals, and the lemmas demand a proof that the numeral is the real
head size, so nothing is assumed.

`Reads t g` is the contract: `g` answers what `decodeBAVal t` answers.  It
composes exactly like `Denotes` does on the encoder side, and
`runStrict_eq` turns it into the user-facing statement about `decodeStrict`.
-/

namespace EvmAbi.Compile.Decode

open Ty Binary
open EvmAbi.Codec
open EvmAbi.Codec.ByteArray

/-- A compiled decoder for `t` reads what the generic decoder reads. -/
def Reads (t : Ty) (g : ByteArray → Nat → Option (ValBA t × Nat)) : Prop :=
  ∀ ba off, g ba off = decodeBAVal t ba off

/-- Two `GetBA` programs that run the same are the same. -/
private theorem getBA_ext {α : Type} {x y : GetBA α} (h : x.run = y.run) : x = y := by
  cases x; cases y; congr

/-! ## the leaves

One reader per primitive clause of `decodeBAVal`.  The `bytes` and `string`
clauses carry the payload's `< 2 ^ 256` bound inside the value they return;
that bound is extracted here as a lemma so the reader can state it in one
line (and so the emitter never has to print a proof). -/

/-- Read a `uintM`. -/
def readUint (m : Nat) (ba : ByteArray) (off : Nat) : Option (ValBA (.uint m) × Nat) :=
  match wordAtBA ba off with
  | some w =>
      if hm : 256 ≤ m then
        some (⟨w, toNat_lt_two_pow_of_le w hm⟩, 32)
      else if h : w.toNat < 2 ^ m then some (⟨w, h⟩, 32) else none
  | none => none

theorem reads_uint (m : Nat) : Reads (.uint m) (readUint m) := by
  intro ba off; rw [decodeBAVal.eq_1]; rfl

/-- Read an `intM`. -/
def readInt (m : Nat) (ba : ByteArray) (off : Nat) : Option (ValBA (.int m) × Nat) :=
  match decodeIntBA ba off with
  | some i => if h : -((2 ^ (m - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m - 1) : Nat) : Int) then
      some (⟨i, h⟩, 32)
    else none
  | none => none

theorem reads_int (m : Nat) : Reads (.int m) (readInt m) := by
  intro ba off; rw [decodeBAVal.eq_2]; rfl

/-- Read a `bool`. -/
def readBool (ba : ByteArray) (off : Nat) : Option (ValBA .bool × Nat) :=
  match decodeBoolBA ba off with
  | some b => some (b, 32)
  | none => none

theorem reads_bool : Reads .bool readBool := by
  intro ba off; rw [decodeBAVal.eq_3]; rfl

/-- Read an `address`. -/
def readAddress (ba : ByteArray) (off : Nat) : Option (ValBA .address × Nat) :=
  match decodeAddressBA ba off with
  | some n => if h : n < 2 ^ 160 then some (⟨n, h⟩, 32) else none
  | none => none

theorem reads_address : Reads .address readAddress := by
  intro ba off; rw [decodeBAVal.eq_4]; rfl

/-- Read a `bytesN`. -/
def readBytesN (m : Nat) (ba : ByteArray) (off : Nat) : Option (ValBA (.bytesN m) × Nat) :=
  match decodeBytesNBAVal m ba off with
  | some bs => if h : bs.size = m then some (⟨bs, h⟩, 32) else none
  | none => none

theorem reads_bytesN (m : Nat) : Reads (.bytesN m) (readBytesN m) := by
  intro ba off; rw [decodeBAVal.eq_5]; rfl

/-- A prefix-decoded payload is bounded by its own length word — the bound
the `bytes` and `string` values carry. -/
theorem size_lt_of_decodeBytesPrefixBAVal {ba : ByteArray} {off : Nat}
    {bs : ByteArray} {n : Nat} (hp : decodeBytesPrefixBAVal ba off = some (bs, n)) :
    bs.size < 2 ^ 64 := by
  have hma : decodeBytesPrefixBA ba off = some (bs.data.toList, n) := by
    rw [← decodeBytesPrefixBAVal_eq ba off, hp]
    rfl
  have hlist : decodeBytesPrefix (ba.data.toList.drop off) = some (bs.data.toList, n) := by
    rw [← decodeBytesPrefixBA_eq ba off]
    exact hma
  simpa [← Binary.ByteArray.size_eq_toList_length] using length_lt_of_decodeBytesPrefix hlist

/-- The same bound, transported onto a string through the UTF-8 decode. -/
theorem size_toUTF8_lt_of_decodeBytesPrefixBAVal {ba : ByteArray} {off : Nat}
    {bs : ByteArray} {n : Nat} {s : String}
    (hp : decodeBytesPrefixBAVal ba off = some (bs, n))
    (hs : String.fromUTF8? bs = some s) : s.toUTF8.size < 2 ^ 64 := by
  have hma : decodeBytesPrefixBA ba off = some (bs.data.toList, n) := by
    rw [← decodeBytesPrefixBAVal_eq ba off, hp]
    rfl
  have hlist : decodeBytesPrefix (ba.data.toList.drop off) = some (bs.data.toList, n) := by
    rw [← decodeBytesPrefixBA_eq ba off]
    exact hma
  have hs' : String.fromUTF8? (bs.data.toList.toByteArray) = some s := by
    rw [dataToList_toByteArray]
    exact hs
  exact size_toUTF8_lt_of_decodeBytesPrefix hlist hs'

/-- Read dynamic `bytes`. -/
def readBytes (ba : ByteArray) (off : Nat) : Option (ValBA .bytes × Nat) :=
  match hp : decodeBytesPrefixBAVal ba off with
  | some (bs, n) => some (⟨bs, size_lt_of_decodeBytesPrefixBAVal hp⟩, n)
  | none => none

theorem reads_bytes : Reads .bytes readBytes := by
  intro ba off; rw [decodeBAVal.eq_6]; rfl

/-- Read a `string`. -/
def readString (ba : ByteArray) (off : Nat) : Option (ValBA .string × Nat) :=
  match hp : decodeBytesPrefixBAVal ba off with
  | some (bs, n) => match hs : String.fromUTF8? bs with
      | some s => some (⟨s, size_toUTF8_lt_of_decodeBytesPrefixBAVal hp hs⟩, n)
      | none => none
  | none => none

theorem reads_string : Reads .string readString := by
  intro ba off; rw [decodeBAVal.eq_7]; rfl

/-! ## components

`decodeElemBAVal` decides static-vs-dynamic per component *and* per array
element.  `elemStatic`/`elemDyn` are its two branches with the sub-decoder
taken as a parameter, and they are the only place that distinction survives
compilation: the tuple chain and the element loop below are each written once,
against whichever reader they are handed. -/

/-- Read a static component inline at the head cursor.  `@[inline]`: the
element loop calls it once per element, and the reader it builds is a
structure the compiler can fold into the loop body. -/
@[inline] def elemStatic {t : Ty} (d : ByteArray → Nat → Option (ValBA t × Nat)) :
    GetBA (ValBA t) :=
  ⟨fun ba ho to E =>
    match d ba ho with
    | none => none
    | some (v, n) => some ⟨v, ho + n, to, E⟩⟩

/-- Read a dynamic component: its offset word must equal the frontier, and the
value itself is read at the tail cursor. -/
@[inline] def elemDyn {t : Ty} (d : ByteArray → Nat → Option (ValBA t × Nat)) :
    GetBA (ValBA t) :=
  ⟨fun ba ho to E =>
    match natAtBA ba ho with
    | none => none
    | some o =>
        if o = E then
          match d ba to with
          | none => none
          | some (v, n) => some ⟨v, ho + 32, to + n, E + n⟩
        else none⟩

theorem elemStatic_eq {t : Ty} {d : ByteArray → Nat → Option (ValBA t × Nat)}
    (hs : t.isStatic = true) (hd : Reads t d) : elemStatic d = decodeElemBAVal t := by
  refine getBA_ext ?_
  funext ba ho to E
  simp only [elemStatic, decodeElemBAVal, hs, hd ba ho]
  cases decodeBAVal t ba ho with
  | none => rfl
  | some p => obtain ⟨v, n⟩ := p; rfl

theorem elemDyn_eq {t : Ty} {d : ByteArray → Nat → Option (ValBA t × Nat)}
    (hs : t.isStatic = false) (hd : Reads t d) : elemDyn d = decodeElemBAVal t := by
  refine getBA_ext ?_
  funext ba ho to E
  simp only [elemDyn, decodeElemBAVal, hs, hd ba to]
  cases natAtBA ba ho with
  | none => rfl
  | some o =>
      by_cases hoE : o = E
      · simp only [if_pos hoE]
        cases decodeBAVal t ba to with
        | none => rfl
        | some p => obtain ⟨v, n⟩ := p; rfl
      · simp only [if_neg hoE]

/-! ### the tuple chain -/

/-- Read one component, then the rest — `GetBA`'s bind written flat, so a
compiled tuple costs no closure per component.  Like `elems` it takes the
*maker* (`elemStatic`/`elemDyn`) and the component's decoder rather than the
built reader: with both `@[inline]`, the chain that remains reads the
component directly instead of through a field. -/
@[inline] def cons {t : Ty} {ts : List Ty}
    (mk : (ByteArray → Nat → Option (ValBA t × Nat)) → GetBA (ValBA t))
    (d : ByteArray → Nat → Option (ValBA t × Nat)) (k : GetBA (TupleValBA ts)) :
    GetBA (TupleValBA (t :: ts)) :=
  ⟨fun ba ho to E =>
    match (mk d).run ba ho to E with
    | none => none
    | some r =>
        match k.run ba r.head r.tails r.frontier with
        | none => none
        | some r' => some ⟨(r.val, r'.val), r'.head, r'.tails, r'.frontier⟩⟩

/-- The end of a tuple: nothing to read. -/
def consNil : GetBA (TupleValBA []) := pure ()

theorem consNil_eq : consNil = decodeTupleBAVal [] := by
  rw [decodeTupleBAVal.eq_1]; rfl

theorem cons_eq {t : Ty} {ts : List Ty}
    {mk : (ByteArray → Nat → Option (ValBA t × Nat)) → GetBA (ValBA t)}
    {d : ByteArray → Nat → Option (ValBA t × Nat)} {k : GetBA (TupleValBA ts)}
    (he : mk d = decodeElemBAVal t) (hk : k = decodeTupleBAVal ts) :
    cons mk d k = decodeTupleBAVal (t :: ts) := by
  subst hk
  rw [decodeTupleBAVal.eq_2]
  refine getBA_ext ?_
  funext ba ho to E
  simp only [cons, he, GetBA.bind_run, GetBA.pure_run]
  cases (decodeElemBAVal t).run ba ho to E with
  | none => rfl
  | some r =>
      cases hr : (decodeTupleBAVal ts).run ba r.head r.tails r.frontier <;> simp only [hr]

/-! ### the element loop -/

/-- Read `k` consecutive elements, each with `mk d` — `elemStatic` or
`elemDyn`, applied to the element type's decoder.  Taking the *maker* rather
than the reader is what lets `@[specialize]` compile the loop against the
reader the compiler chose, instead of calling it through a field. -/
@[specialize] def elems {t : Ty}
    (mk : (ByteArray → Nat → Option (ValBA t × Nat)) → GetBA (ValBA t))
    (d : ByteArray → Nat → Option (ValBA t × Nat)) :
    (k : Nat) → GetBA ({ vs : List (ValBA t) // vs.length = k })
  | 0 => pure ⟨[], rfl⟩
  | k + 1 => do
      let v ← mk d
      let ⟨vs, h⟩ ← elems mk d k
      pure ⟨v :: vs, by simp [List.length_cons, h]⟩

theorem elems_eq {t : Ty} {mk : (ByteArray → Nat → Option (ValBA t × Nat)) → GetBA (ValBA t)}
    {d : ByteArray → Nat → Option (ValBA t × Nat)} (he : mk d = decodeElemBAVal t) :
    ∀ k, elems mk d k = decodeElemsBAVal t k
  | 0 => by rw [decodeElemsBAVal]; rfl
  | k + 1 => by rw [decodeElemsBAVal, elems, elems_eq he k, he]

/-! ## the compound clauses

The three clauses of `decodeBAVal` that recurse, with the head sizes taken as
parameters: the emitter passes numerals, and each lemma asks for a proof that
the numeral is the head size the type really has. -/

/-- Read a `T[]`: the length word, then that many elements. -/
def readArray {t : Ty} (hsz : Nat)
    (loop : (k : Nat) → GetBA ({ vs : List (ValBA t) // vs.length = k }))
    (ba : ByteArray) (off : Nat) : Option (ValBA (.array t) × Nat) :=
  if hsz = 0 then none else
    match natAtBA ba off with
    | none => none
    | some k => if hb : k < 2 ^ 64 then
        match (loop k).run ba (off + 32) (off + 32 + k * hsz) (k * hsz) with
        | some r => some (⟨r.val.val, by rw [r.val.property]; exact hb⟩, 32 + r.frontier)
        | none => none
      else none

theorem reads_array {t : Ty} {hsz : Nat}
    {loop : (k : Nat) → GetBA ({ vs : List (ValBA t) // vs.length = k })}
    (hh : hsz = t.headSize) (he : ∀ k, loop k = decodeElemsBAVal t k) :
    Reads (.array t) (readArray hsz loop) := by
  subst hh
  intro ba off
  rw [decodeBAVal.eq_8, readArray]
  simp only [he]
  rfl

/-- Read a `T[k]`: `k` elements, no length word. -/
def readFixedArray {t : Ty} {n : Nat} (hsz : Nat)
    (loop : (k : Nat) → GetBA ({ vs : List (ValBA t) // vs.length = k }))
    (ba : ByteArray) (off : Nat) : Option (ValBA (.fixedArray t n) × Nat) :=
  match (loop n).run ba off (off + n * hsz) (n * hsz) with
  | some r => some (r.val, r.frontier)
  | none => none

theorem reads_fixedArray {t : Ty} {n : Nat} {hsz : Nat}
    {loop : (k : Nat) → GetBA ({ vs : List (ValBA t) // vs.length = k })}
    (hh : hsz = t.headSize) (he : ∀ k, loop k = decodeElemsBAVal t k) :
    Reads (.fixedArray t n) (readFixedArray hsz loop) := by
  subst hh
  intro ba off
  rw [decodeBAVal.eq_9, readFixedArray, he]
  rfl

/-- Read a `(T₁, …, Tₙ)`: run the component chain over the two cursors. -/
def readTuple {ts : List Ty} (hss : Nat) (k : GetBA (TupleValBA ts))
    (ba : ByteArray) (off : Nat) : Option (ValBA (.tuple ts) × Nat) :=
  match k.run ba off (off + hss) hss with
  | some r => some (r.val, r.frontier)
  | none => none

theorem reads_tuple {ts : List Ty} {hss : Nat} {k : GetBA (TupleValBA ts)}
    (hh : hss = headSizeSum ts) (hk : k = decodeTupleBAVal ts) :
    Reads (.tuple ts) (readTuple hss k) := by
  subst hh; subst hk
  intro ba off
  rw [decodeBAVal.eq_10, readTuple]
  rfl

/-! ## from reader to the user's decoder -/

/-- The strict wrapper: decode at offset 0 and insist the whole buffer was
consumed. -/
def runStrict {t : Ty} (g : ByteArray → Nat → Option (ValBA t × Nat))
    (ba : ByteArray) : Option (ValBA t) :=
  match g ba 0 with
  | some (v, n) => if n = ba.size then some v else none
  | none => none

/-- **The compiler's correctness statement, decoder side**: a compiled reader
run strictly *is* `decodeStrict`. -/
theorem runStrict_eq {t : Ty} {g : ByteArray → Nat → Option (ValBA t × Nat)}
    (hg : Reads t g) (ba : ByteArray) : runStrict g ba = decodeStrict t ba := by
  rw [runStrict, decodeStrict, decodeStrictBAVal, hg ba 0]
  rfl

/-- The compiled decoder inherits the verified roundtrip: it reads back what
`encode` wrote, as the very same value. -/
theorem runStrict_encode {t : Ty} {g : ByteArray → Nat → Option (ValBA t × Nat)}
    (hg : Reads t g) (hv : t.Valid) (v : ValBA t) (hb : (encode t v).size < 2 ^ 256) :
    runStrict g (encode t v) = some v := by
  rw [runStrict_eq hg]
  exact decodeStrict_encode t hv v hb

/-- …and the uniqueness direction: a buffer a compiled decoder accepts *is*
the encoding of what it read. -/
theorem encode_of_runStrict {t : Ty} {g : ByteArray → Nat → Option (ValBA t × Nat)}
    (hg : Reads t g) (hv : t.Valid) (ba : ByteArray) (v : ValBA t)
    (h : runStrict g ba = some v) : encode t v = ba := by
  rw [runStrict_eq hg] at h
  exact encode_of_decodeStrict t hv ba v h

end EvmAbi.Compile.Decode
