import EvmAbi.Codec
import EvmAbi.Codec.Strict

/-!
# EvmAbi.Codec.ByteArray

The codec's primitive reads, **at an offset in a `ByteArray`** instead of
at the front of a `List UInt8`.

`decode` threads two `List UInt8` cursors: reaching a component means
`drop`ping to it, and reading its word means `take`ing 32 bytes into a
fresh list, so a caller holding real call data pays a full conversion up
front and an allocation per word after that.  This module is the layer that
removes the per-read part — every primitive here reads its own bytes and
nothing else, and the only lists built are the payloads that `Ty.Val`
genuinely is (`bytes`, `string`, `bytesN` data).

Nothing is reproved.  Each definition is paired with an agreement lemma
against its `EvmAbi.Codec` counterpart under the translation

```
offset `off`  ↦  ba.data.toList.drop off
```

so anything proved about the list primitives transports.

These are what an offset-cursor walk is built from: give the `Get2` state
three naturals over one shared buffer, read with these, and prove each
walker agrees with its list counterpart under the same translation.  That
walk is not here yet — `EvmAbi.Codec.Strict.decodeStrictBA` still converts
at the boundary.
-/

namespace EvmAbi

open Ty
open Binary

/-! ## windows

The payload primitives need their bytes as a list — that is what a
`bytes`/`string`/`bytesN` value *is* — but only their own bytes, not the
buffer's.  `windowList` extracts exactly the window. -/

/-- Walk `i` down from `stop` to `off`, consing `ba[i-1]!` onto `acc`: the
result is `[ba[off], …, ba[stop-1]] ++ acc`.  Every read is in bounds
because the caller passes `stop ≤ ba.size`. -/
def windowList.loop (ba : ByteArray) (off : Nat) (i : Nat) (acc : List UInt8) : List UInt8 :=
  if i > off then windowList.loop ba off (i - 1) (ba[i - 1]! :: acc) else acc
termination_by i

/-- The `len` bytes at `off`, as a list, without converting the rest of the
buffer.  The window is walked by index — `ba[i]!` — so no boxed-array
intermediate is built: the list is the only allocation.

The end is clamped to the buffer.  That is not just tidiness: `len` comes
off the wire — it is a length word an attacker chooses — and a window that
ran past the buffer would index out of bounds.  `take` clamps on the list
side, so the specification is unchanged. -/
def windowList (ba : ByteArray) (off len : Nat) : List UInt8 :=
  windowList.loop ba off (min (off + len) ba.size) []

/-- The loop accumulates exactly the window: `[ba[off], …, ba[i-1]] ++ acc`.
The `stop` bound is carried so every `ba[j]!` read is in bounds. -/
theorem windowList.loop_eq (ba : ByteArray) (off : Nat) (stop : Nat)
    (hstop : stop ≤ ba.size) :
    ∀ (i : Nat) (_hi : i ≤ stop) (acc : List UInt8),
      windowList.loop ba off i acc = (ba.data.toList.drop off).take (i - off) ++ acc := by
  intro i
  induction i with
  | zero =>
      intro hi acc
      unfold windowList.loop
      simp
  | succ i ih =>
      intro hi acc
      by_cases h : i + 1 > off
      · have hi' : i ≤ stop := by omega
        have hi_off : i + 1 - off = (i - off) + 1 := by omega
        have hlt : i - off < (ba.data.toList.drop off).length := by
          rw [List.length_drop, ← ByteArray.size_eq_toList_length]
          omega
        have hb : i < ba.size := by omega
        have hlen : ba.data.toList.length = ba.size := (ByteArray.size_eq_toList_length ba).symm
        have hget : ba[i]! = (ba.data.toList.drop off)[i - off] := by
          rw [getElem!_pos ba i hb, List.getElem_drop (i := off) (j := i - off) (h := hlt)]
          change ba.data.toList[i]'(by omega) = ba.data.toList[off + (i - off)]'(by omega)
          congr 1
          omega
        unfold windowList.loop
        simp [h, hi_off]
        rw [ih hi' (ba[i]! :: acc)]
        rw [List.take_succ_eq_append_getElem hlt]
        simp [hget]
      · have hoff : i + 1 ≤ off := by omega
        unfold windowList.loop
        simp [h, Nat.sub_eq_zero_of_le hoff]

@[simp] theorem windowList_eq (ba : ByteArray) (off len : Nat) :
    windowList ba off len = (ba.data.toList.drop off).take len := by
  rw [windowList]
  have hlen : ba.data.toList.length = ba.size := (ByteArray.size_eq_toList_length ba).symm
  have hstop : min (off + len) ba.size ≤ ba.size := Nat.min_le_right _ _
  rw [windowList.loop_eq ba off (min (off + len) ba.size) hstop _ (Nat.le_refl _) [],
    List.append_nil]
  rcases Nat.le_total (off + len) ba.size with h | h
  · rw [show min (off + len) ba.size = off + len by omega,
      show (off + len) - off = len by omega]
  · rw [show min (off + len) ba.size = ba.size by omega]
    rw [List.take_of_length_le (by rw [List.length_drop]; omega),
      List.take_of_length_le (by rw [List.length_drop]; omega)]

/-- Dropping to `off` and then to `k` more is dropping to `off + k`. -/
theorem drop_drop_ba (ba : ByteArray) (off k : Nat) :
    (ba.data.toList.drop off).drop k = ba.data.toList.drop (off + k) := by
  rw [List.drop_drop, Nat.add_comm]

/-- The length of a clamped window is arithmetic — `min len (ba.size - off)`
— so a decode can check that a `len`-byte payload fits without building the
list (a list build is the value itself, not the check). -/
@[simp] theorem take_length_drop_ba (ba : ByteArray) (off len : Nat) :
    ((ba.data.toList.drop off).take len).length = min len (ba.size - off) := by
  rw [List.length_take, List.length_drop, ← ByteArray.size_eq_toList_length]

/-! ## primitives at an offset

The numeric ones all funnel through `natAt buf 0`, so they funnel through
`natAtBA` here and inherit `natAtBA_eq`.  The payload ones read a window. -/

/-- `uintM` at an offset. -/
def decodeUintBA (ba : ByteArray) (off : Nat) : Option Nat := natAtBA ba off

theorem decodeUintBA_eq (ba : ByteArray) (off : Nat) :
    decodeUintBA ba off = decodeUint (ba.data.toList.drop off) := natAtBA_eq ba off

/-- `intM` at an offset. -/
def decodeIntBA (ba : ByteArray) (off : Nat) : Option Int :=
  (decodeUintBA ba off).map fun (n : Nat) =>
    if n < 2 ^ 255 then (n : Int) else (n : Int) - 2 ^ 256

theorem decodeIntBA_eq (ba : ByteArray) (off : Nat) :
    decodeIntBA ba off = decodeInt (ba.data.toList.drop off) := by
  rw [decodeIntBA, decodeInt, decodeUintBA_eq]

/-- `bool` at an offset. -/
def decodeBoolBA (ba : ByteArray) (off : Nat) : Option Bool :=
  match decodeUintBA ba off with
  | some 0 => some false
  | some 1 => some true
  | _      => none

theorem decodeBoolBA_eq (ba : ByteArray) (off : Nat) :
    decodeBoolBA ba off = decodeBool (ba.data.toList.drop off) := by
  rw [decodeBoolBA, decodeBool, decodeUintBA_eq]
  cases h : decodeUint (ba.data.toList.drop off) with
  | none => rfl
  | some n => match n with
    | 0 => rfl
    | 1 => rfl
    | k + 2 => rfl

/-- `address` at an offset. -/
def decodeAddressBA (ba : ByteArray) (off : Nat) : Option Nat := decodeUintBA ba off

theorem decodeAddressBA_eq (ba : ByteArray) (off : Nat) :
    decodeAddressBA ba off = decodeAddress (ba.data.toList.drop off) :=
  decodeUintBA_eq ba off

/-- `bytesN` at an offset: one word's window is all it looks at. -/
def decodeBytesNBA (n : Nat) (ba : ByteArray) (off : Nat) : Option (List UInt8) :=
  decodeBytesN n (windowList ba off 32)

theorem decodeBytesNBA_eq (n : Nat) (ba : ByteArray) (off : Nat) :
    decodeBytesNBA n ba off = decodeBytesN n (ba.data.toList.drop off) := by
  simp only [decodeBytesNBA, windowList_eq, decodeBytesN, List.take_take, Nat.min_self]

/-- Dynamic `bytes` at an offset: the length word, then the payload and its
padding as windows.  The length check is arithmetic, not a list build: a
clamped window at `off + 32` has exactly `len` bytes iff
`min len (ba.size - (off + 32)) = len`, so the payload list is constructed
once (for the value), not once for a length check and again for the value. -/
def decodeBytesPrefixBA (ba : ByteArray) (off : Nat) : Option (List UInt8 × Nat) :=
  (natAtBA ba off).bind fun len =>
    let pad := (32 - len % 32) % 32
    if min len (ba.size - (off + 32)) = len ∧
       windowList ba (off + 32 + len) pad = List.replicate pad 0 then
      some (windowList ba (off + 32) len, 32 + len + pad)
    else none

theorem decodeBytesPrefixBA_eq (ba : ByteArray) (off : Nat) :
    decodeBytesPrefixBA ba off = decodeBytesPrefix (ba.data.toList.drop off) := by
  rw [decodeBytesPrefixBA, decodeBytesPrefix, natAtBA_eq]
  simp only [windowList_eq, drop_drop_ba, take_length_drop_ba, Nat.add_assoc]

/-! ## the reader

`Get2`'s dual: the same three-component state, with the two cursors as
offsets into one buffer rather than sub-lists of a copy. -/

namespace GetBA

/-- The result of a `GetBA` run: the value, the advanced cursor *offsets*,
and the new expected tail frontier. -/
structure Result (α : Type) where
  /-- The decoded value. -/
  val : α
  /-- Remaining head cursor, as an offset. -/
  head : Nat
  /-- Remaining tail cursor, as an offset. -/
  tails : Nat
  /-- New expected tail frontier. -/
  frontier : Nat

/-- The offsets read as the sub-lists they stand for — the translation the
agreement lemmas are stated over. -/
def Result.toList (ba : ByteArray) (r : Result α) : Get2.Result α :=
  ⟨r.val, ba.data.toList.drop r.head, ba.data.toList.drop r.tails, r.frontier⟩

end GetBA

/-- A dual-cursor prefix reader over one `ByteArray`. -/
structure GetBA (α : Type) where
  run : ByteArray → Nat → Nat → Nat → Option (GetBA.Result α)

namespace GetBA

instance : Monad GetBA where
  pure a := ⟨fun _ ho to E => some ⟨a, ho, to, E⟩⟩
  bind x f := ⟨fun ba ho to E =>
    match x.run ba ho to E with
    | none => none
    | some r => (f r.val).run ba r.head r.tails r.frontier⟩

@[simp] theorem pure_run (a : α) (ba : ByteArray) (ho to E : Nat) :
    (pure a : GetBA α).run ba ho to E = some ⟨a, ho, to, E⟩ := rfl

@[simp] theorem bind_run (x : GetBA α) (f : α → GetBA β) (ba : ByteArray) (ho to E : Nat) :
    (x >>= f).run ba ho to E = (match x.run ba ho to E with
      | none => none
      | some r => (f r.val).run ba r.head r.tails r.frontier) := rfl

end GetBA

/-! ## the decoder

Clause for clause the same walk as `EvmAbi.Codec.decode`, reading at
offsets.  It returns the value and the bytes consumed; the new position is
`off + n`. -/

mutual
/-- **Canonical decoder over a `ByteArray`**: reads one canonical value of
type `t` at offset `off`, returning it and the bytes it consumed. -/
def decodeBA : (t : Ty) → ByteArray → Nat → Option (t.Val × Nat)
  | .uint m, ba, off => match decodeUintBA ba off with
      | some n => if h : n < 2 ^ m then some (⟨n, h⟩, 32) else none
      | none => none
  | .int m, ba, off => match decodeIntBA ba off with
      | some i => if h : -((2 ^ (m - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m - 1) : Nat) : Int) then
          some (⟨i, h⟩, 32)
        else none
      | none => none
  | .bool, ba, off => match decodeBoolBA ba off with
      | some b => some (b, 32)
      | none => none
  | .address, ba, off => match decodeAddressBA ba off with
      | some n => if h : n < 2 ^ 160 then some (⟨n, h⟩, 32) else none
      | none => none
  | .bytesN m, ba, off => match decodeBytesNBA m ba off with
      | some bs => if h : bs.length = m then some (⟨bs, h⟩, 32) else none
      | none => none
  | .bytes, ba, off => match hp : decodeBytesPrefixBA ba off with
      | some (bs, n) =>
          some (⟨bs, length_lt_of_decodeBytesPrefix (by rw [← decodeBytesPrefixBA_eq]; exact hp)⟩, n)
      | none => none
  | .string, ba, off => match hp : decodeBytesPrefixBA ba off with
      | some (bs, n) => match hs : String.fromUTF8? bs.toByteArray with
          | some s =>
              some (⟨s, size_toUTF8_lt_of_decodeBytesPrefix
                (by rw [← decodeBytesPrefixBA_eq]; exact hp) hs⟩, n)
          | none => none
      | none => none
  | .array t, ba, off => if t.headSize = 0 then none else
      match hk : natAtBA ba off with
      | none => none
      | some k =>
          match (decodeElemsBA t k).run ba (off + 32) (off + 32 + k * t.headSize)
              (k * t.headSize) with
          | some r => some (⟨r.val.val, by rw [r.val.property]; exact natAtBA_lt hk⟩, 32 + r.frontier)
          | none => none
  | .fixedArray t n, ba, off =>
      match (decodeElemsBA t n).run ba off (off + n * t.headSize) (n * t.headSize) with
      | some r => some (r.val, r.frontier)
      | none => none
  | .tuple ts, ba, off =>
      match (decodeTupleBA ts).run ba off (off + headSizeSum ts) (headSizeSum ts) with
      | some r => some (r.val, r.frontier)
      | none => none
termination_by t => (sizeOf t, 0)

/-- Read one component at its head slot. -/
def decodeElemBA (t : Ty) : GetBA t.Val := ⟨fun ba ho to E =>
  match t.isStatic with
  | true => match decodeBA t ba ho with
      | some (v, n) => some ⟨v, ho + n, to, E⟩
      | none => none
  | false => match natAtBA ba ho with
      | none => none
      | some o => if o = E then
          match decodeBA t ba to with
          | some (v, n) => some ⟨v, ho + 32, to + n, E + n⟩
          | none => none
        else none⟩
termination_by (sizeOf t, 1)

/-- Read `k` consecutive canonical elements. -/
def decodeElemsBA (t : Ty) (k : Nat) : GetBA ({ vs : List t.Val // vs.length = k }) :=
  match k with
  | 0 => pure ⟨[], rfl⟩
  | k + 1 => do
      let v ← decodeElemBA t
      let ⟨vs, h⟩ ← decodeElemsBA t k
      pure ⟨v :: vs, by simp [List.length_cons, h]⟩
termination_by (sizeOf t, k + 2)

/-- Read a canonical tuple. -/
def decodeTupleBA : (ts : List Ty) → GetBA (TupleVal ts)
  | [] => pure ()
  | t :: ts => do
      let v ← decodeElemBA t
      let vs ← decodeTupleBA ts
      pure (v, vs)
termination_by ts => (sizeOf ts, 2)
end

/-! ## agreement with the list decoder

Each definition above is its `EvmAbi.Codec` counterpart read at an offset.
The lemmas say so, and everything after them is a rewrite. -/

/- The `array` clause of each decoder reads its length word with a
*dependent* match, so neither scrutinee can be rewritten in place.  These
four lemmas resolve the match once, against a known length word, leaving a
plain one — the same device as `decode_bytes_pos`. -/

private theorem decode_array_none {t : Ty} {buf : List UInt8} (hhs : ¬ t.headSize = 0)
    (hk : natAt buf 0 = none) : decode (.array t) buf = none := by
  simp only [decode]
  rw [if_neg hhs]
  split
  · rfl
  · next k h => rw [hk] at h; contradiction

private theorem decode_array_pos {t : Ty} {buf : List UInt8} {k : Nat} (hhs : ¬ t.headSize = 0)
    (hk : natAt buf 0 = some k) :
    decode (.array t) buf =
      match (decodeElems t k).run (buf.drop 32) (buf.drop (32 + k * t.headSize))
          (k * t.headSize) with
      | some ⟨vs, _, rest, E⟩ =>
          some (⟨vs.val, by rw [vs.property]; exact natAt_lt hk⟩, 32 + E, rest)
      | none => none := by
  simp only [decode]
  rw [if_neg hhs]
  split
  · next h => rw [hk] at h; contradiction
  · next k' h => rw [hk] at h; obtain rfl := Option.some.inj h; rfl

private theorem decodeBA_array_none {t : Ty} {ba : ByteArray} {off : Nat}
    (hhs : ¬ t.headSize = 0) (hk : natAtBA ba off = none) : decodeBA (.array t) ba off = none := by
  simp only [decodeBA]
  rw [if_neg hhs]
  split
  · rfl
  · next k h => rw [hk] at h; contradiction

private theorem decodeBA_array_pos {t : Ty} {ba : ByteArray} {off k : Nat}
    (hhs : ¬ t.headSize = 0) (hk : natAtBA ba off = some k) :
    decodeBA (.array t) ba off =
      match (decodeElemsBA t k).run ba (off + 32) (off + 32 + k * t.headSize)
          (k * t.headSize) with
      | some r => some (⟨r.val.val, by rw [r.val.property]; exact natAtBA_lt hk⟩,
          32 + r.frontier)
      | none => none := by
  simp only [decodeBA]
  rw [if_neg hhs]
  split
  · next h => rw [hk] at h; contradiction
  · next k' h => rw [hk] at h; obtain rfl := Option.some.inj h; rfl

/-- The list decoder's remainder is exactly the drop by what it consumed —
a corollary of soundness, and what lets an offset stand in for a cursor. -/
theorem decode_rest (t : Ty) (hv : t.Valid) (v : t.Val) (buf rest : List UInt8) (n : Nat)
    (h : decode t buf = some (v, n, rest)) : rest = buf.drop n := by
  obtain ⟨hb, hn⟩ := decode_sound t hv v buf rest n h
  rw [← hb, hn, List.drop_left]

mutual
/-- **Agreement**: decoding at an offset is decoding the suffix. -/
theorem decodeBA_eq (t : Ty) (hv : t.Valid) (ba : ByteArray) (off : Nat) :
    decodeBA t ba off = (decode t (ba.data.toList.drop off)).map (fun p => (p.1, p.2.1)) := by
  cases t with
  | uint m =>
      rw [decodeBA, decode, decodeUintBA_eq]
      cases decodeUint (ba.data.toList.drop off) with
      | none => rfl
      | some n => by_cases h : n < 2 ^ m <;> simp [h]
  | int m =>
      rw [decodeBA, decode, decodeIntBA_eq]
      cases decodeInt (ba.data.toList.drop off) with
      | none => rfl
      | some i =>
          by_cases h : -((2 ^ (m - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m - 1) : Nat) : Int) <;>
            simp
  | bool =>
      rw [decodeBA, decode, decodeBoolBA_eq]
      cases decodeBool (ba.data.toList.drop off) with
      | none => rfl
      | some b => rfl
  | address =>
      rw [decodeBA, decode, decodeAddressBA_eq]
      cases decodeAddress (ba.data.toList.drop off) with
      | none => rfl
      | some n => by_cases h : n < 2 ^ 160 <;> simp [h]
  | bytesN m =>
      rw [decodeBA, decode, decodeBytesNBA_eq]
      cases decodeBytesN m (ba.data.toList.drop off) with
      | none => rfl
      | some bs => by_cases h : bs.length = m <;> simp [h]
  | bytes =>
      have hpe := decodeBytesPrefixBA_eq ba off
      simp only [decodeBA, decode]
      split <;> split <;> simp_all
  | string =>
      have hpe := decodeBytesPrefixBA_eq ba off
      simp only [decodeBA, decode]
      repeat' split
      all_goals (simp_all [Subtype.ext_iff]; try (obtain ⟨rfl, rfl⟩ := hpe); simp_all)
  | array t =>
      have hva := valid_array.mp hv
      have hne := natAtBA_eq ba off
      by_cases hhs : t.headSize = 0
      · simp only [decodeBA, decode, if_pos hhs]; rfl
      · cases hk : natAtBA ba off with
        | none =>
            rw [decodeBA_array_none hhs hk, decode_array_none hhs (by rw [← hne, hk])]
            rfl
        | some k =>
            have hkl : natAt (ba.data.toList.drop off) 0 = some k := by rw [← hne, hk]
            rw [decodeBA_array_pos hhs hk, decode_array_pos hhs hkl]
            have hw := decodeElemsBA_eq t hva.1 k ba (off + 32) (off + 32 + k * t.headSize)
              (k * t.headSize)
            rw [drop_drop_ba, drop_drop_ba,
              show off + (32 + k * t.headSize) = off + 32 + k * t.headSize by omega, ← hw]
            cases (decodeElemsBA t k).run ba (off + 32) (off + 32 + k * t.headSize)
                (k * t.headSize) <;> simp [GetBA.Result.toList]
  | fixedArray t n =>
      have hvt : t.Valid := hv
      simp only [decodeBA, decode]
      have hw := decodeElemsBA_eq t hvt n ba off (off + n * t.headSize) (n * t.headSize)
      split <;> split <;> simp_all [GetBA.Result.toList]
  | tuple ts =>
      have hvts : AllValid ts := hv
      simp only [decodeBA, decode]
      have hw := decodeTupleBA_eq ts hvts ba off (off + headSizeSum ts) (headSizeSum ts)
      split <;> split <;> simp_all [GetBA.Result.toList]
termination_by 8 * sizeOf t

/-- **Agreement**, per component. -/
theorem decodeElemBA_eq (t : Ty) (hv : t.Valid) (ba : ByteArray) (ho to E : Nat) :
    ((decodeElemBA t).run ba ho to E).map (GetBA.Result.toList ba) =
      (decodeElem t).run (ba.data.toList.drop ho) (ba.data.toList.drop to) E := by
  rw [decodeElemBA, decodeElem]
  cases hs : t.isStatic
  · simp only []
    rw [natAtBA_eq]
    cases natAt (ba.data.toList.drop ho) 0 with
    | none => rfl
    | some o =>
        simp only []
        by_cases hoE : o = E
        · rw [if_pos hoE, if_pos hoE, decodeBA_eq t hv ba to]
          cases hl : decode t (ba.data.toList.drop to) with
          | none => rfl
          | some q =>
              obtain ⟨v, n, rest⟩ := q
              rw [decode_rest t hv v _ rest n hl, drop_drop_ba]
              simp [GetBA.Result.toList]
        · rw [if_neg hoE, if_neg hoE]; rfl
  · simp only []
    rw [decodeBA_eq t hv ba ho]
    cases hl : decode t (ba.data.toList.drop ho) with
    | none => rfl
    | some q =>
        obtain ⟨v, n, rest⟩ := q
        rw [decode_rest t hv v _ rest n hl, drop_drop_ba]
        simp [GetBA.Result.toList]
termination_by 8 * sizeOf t + 1

/-- **Agreement**, element runs. -/
theorem decodeElemsBA_eq (t : Ty) (hv : t.Valid) (k : Nat) (ba : ByteArray) (ho to E : Nat) :
    ((decodeElemsBA t k).run ba ho to E).map (GetBA.Result.toList ba) =
      (decodeElems t k).run (ba.data.toList.drop ho) (ba.data.toList.drop to) E := by
  induction k generalizing ho to E with
  | zero => simp [decodeElemsBA, decodeElems, GetBA.Result.toList]
  | succ k ih =>
      simp only [decodeElemsBA, decodeElems, GetBA.bind_run, Get2.bind_run,
        GetBA.pure_run, Get2.pure_run]
      rw [← decodeElemBA_eq t hv ba ho to E]
      cases (decodeElemBA t).run ba ho to E with
      | none => rfl
      | some r =>
          simp only [Option.map_some, GetBA.Result.toList]
          rw [← ih r.head r.tails r.frontier]
          cases (decodeElemsBA t k).run ba r.head r.tails r.frontier <;> rfl
termination_by 8 * sizeOf t + 2

/-- **Agreement**, tuples. -/
theorem decodeTupleBA_eq : (ts : List Ty) → AllValid ts → (ba : ByteArray) → (ho to E : Nat) →
    ((decodeTupleBA ts).run ba ho to E).map (GetBA.Result.toList ba) =
      (decodeTuple ts).run (ba.data.toList.drop ho) (ba.data.toList.drop to) E
  | [], _, ba, ho, to, E => by simp [decodeTupleBA, decodeTuple, GetBA.Result.toList]
  | t :: ts, hv, ba, ho, to, E => by
      obtain ⟨hvt, hvs⟩ := hv
      simp only [decodeTupleBA, decodeTuple, GetBA.bind_run, Get2.bind_run,
        GetBA.pure_run, Get2.pure_run]
      rw [← decodeElemBA_eq t hvt ba ho to E]
      cases (decodeElemBA t).run ba ho to E with
      | none => rfl
      | some r =>
          simp only [Option.map_some, GetBA.Result.toList]
          rw [← decodeTupleBA_eq ts hvs ba r.head r.tails r.frontier]
          cases (decodeTupleBA ts).run ba r.head r.tails r.frontier <;> rfl
termination_by ts => 8 * sizeOf ts + 3
end

/-! ## the strict API, on offsets

`decodeStrictBA` now walks the buffer itself: the exact-consumption check
is `n = ba.size` rather than "the remaining cursor is the empty list".
`decodeStrictBA_eq` says it is the list `decodeStrict` of the same bytes,
so the capstones below are the list ones with one rewrite. -/

/-- Strict decode of a `ByteArray`: canonical layout, consumed exactly. -/
def decodeStrictBA (t : Ty) (ba : ByteArray) : Option t.Val :=
  match decodeBA t ba 0 with
  | some (v, n) => if n = ba.size then some v else none
  | none => none

/-- A buffer is a canonical encoding of `t`. -/
def IsCanonicalBA (t : Ty) (ba : ByteArray) : Prop :=
  (decodeStrictBA t ba).isSome = true

instance (t : Ty) (ba : ByteArray) : Decidable (IsCanonicalBA t ba) := by
  unfold IsCanonicalBA
  infer_instance

/-- **Agreement**: the offset walk is the list walk on the same bytes. -/
theorem decodeStrictBA_eq (t : Ty) (hv : t.Valid) (ba : ByteArray) :
    decodeStrictBA t ba = decodeStrict t ba.data.toList := by
  rw [decodeStrictBA, decodeStrict, decodeBA_eq t hv ba 0, List.drop_zero]
  cases hl : decode t ba.data.toList with
  | none => rfl
  | some q =>
      obtain ⟨v, n, rest⟩ := q
      obtain ⟨hb, hn⟩ := decode_sound t hv v ba.data.toList rest n hl
      have hlen := congrArg List.length hb
      rw [List.length_append, ← hn, ← ByteArray.size_eq_toList_length] at hlen
      have hiff : rest = [] ↔ n = ba.size := by
        constructor
        · intro h; rw [h, List.length_nil] at hlen; omega
        · intro h; exact List.eq_nil_of_length_eq_zero (by omega)
      simp only [Option.map_some]
      by_cases hrest : rest = []
      · rw [if_pos hrest, if_pos (hiff.mp hrest)]
      · rw [if_neg hrest, if_neg (fun hc => hrest (hiff.mpr hc))]

theorem isCanonicalBA_eq (t : Ty) (hv : t.Valid) (ba : ByteArray) :
    IsCanonicalBA t ba ↔ IsCanonical t ba.data.toList := by
  rw [IsCanonicalBA, IsCanonical, decodeStrictBA_eq t hv ba]

/-! ## capstones, `ByteArray` end to end -/

/-- **Canonical roundtrip**: what `encodeByteArray` writes, the offset
decoder reads back. -/
theorem decodeStrictBA_encodeByteArray (t : Ty) (hv : t.Valid) (v : t.Val)
    (hb : (encodeByteArray t v).size < 2 ^ 256) :
    decodeStrictBA t (encodeByteArray t v) = some v := by
  rw [size_encodeByteArray] at hb
  rw [decodeStrictBA_eq t hv, data_toList_encodeByteArray]
  exact decodeStrict_encode t hv v hb

/-- **Canonical uniqueness**: a strictly decodable buffer *is* the encoding
of its decoded value. -/
theorem encodeByteArray_of_decodeStrictBA (t : Ty) (hv : t.Valid) (ba : ByteArray)
    (v : t.Val) (h : decodeStrictBA t ba = some v) : encodeByteArray t v = ba := by
  rw [decodeStrictBA_eq t hv] at h
  apply Binary.ByteArray.data_inj
  rw [← Array.toList_inj, data_toList_encodeByteArray]
  exact encode_of_decodeStrict t hv ba.data.toList v h

/-- **Image characterization** (capstone). -/
theorem isCanonicalBA_iff (t : Ty) (hv : t.Valid) (ba : ByteArray)
    (hb : ba.size < 2 ^ 256) :
    IsCanonicalBA t ba ↔ ∃ v, encodeByteArray t v = ba := by
  rw [isCanonicalBA_eq t hv ba]
  rw [ByteArray.size_eq_toList_length] at hb
  rw [isCanonical_iff t hv _ hb]
  constructor
  · rintro ⟨v, he⟩
    refine ⟨v, ?_⟩
    apply Binary.ByteArray.data_inj
    rw [← Array.toList_inj, data_toList_encodeByteArray, he]
  · rintro ⟨v, he⟩
    exact ⟨v, by rw [← he, data_toList_encodeByteArray]⟩

/-- **Strict-decoder characterization** (capstone). -/
theorem decodeStrictBA_eq_some_iff (t : Ty) (hv : t.Valid) (ba : ByteArray)
    (v : t.Val) (hb : ba.size < 2 ^ 256) :
    decodeStrictBA t ba = some v ↔ encodeByteArray t v = ba := by
  constructor
  · exact encodeByteArray_of_decodeStrictBA t hv ba v
  · intro he
    rw [← he]
    exact decodeStrictBA_encodeByteArray t hv v (by rw [he]; exact hb)

end EvmAbi
