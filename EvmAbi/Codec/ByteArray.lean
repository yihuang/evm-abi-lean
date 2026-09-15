import EvmAbi.Spec
import EvmAbi.Spec.Strict
import EvmAbi.ValBA

/-!
# EvmAbi.Codec.ByteArray

The runtime decoder internals, nested under `EvmAbi.Codec`: primitive reads
**at an offset in a `ByteArray`**, the offset walker compiled code runs, and
the single agreement family that ties the two together.  The public runtime API
(`encode`, `decode`, `decodeStrict`, `IsCanonical`) lives in `EvmAbi.Codec`.

The runtime decoder is not a second decoder.  `decodeBAVal` is *defined* as
`Spec.decode` at the offset with the payloads materialised as `ByteArray`s
(`ValBA.ofList`), so its agreement with the specification is the definition,
and the theorems above it transport by rewrite.  The offset walker in the
middle of the file (`decodeBAValFast`, plus `decodeUintElems` for the `uint`
array fast path) is an implementation: `decodeBAVal_eq_fused` is the `@[csimp]`
swap that makes compiled code run it, and the merged agreement family
(`decodeBAValFast_eq_spec` with its `GetBA` companions) is the proof that it
computes the definition — one family, against the specification directly,
rather than a hand-written list-level decoder plus two transports.

The `t.Val`-level `decodeStrictBA` is the specification on the buffer's bytes,
with `decodeStrictBAFast` (one packed walk, then `ValBA.toList`) swapped in the
same way, so the list-valued API keeps the offset reader instead of slicing.

Every primitive is paired with an agreement lemma against its `EvmAbi.Spec`
counterpart under the translation `offset off ↦ ba.data.toList.drop off`, so
anything proved about the list primitives transports.
-/

namespace EvmAbi.Codec.ByteArray

open Ty
open Binary
open EvmAbi.Spec

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
        grind [windowList.loop, Nat.sub_eq_zero_of_le hoff]

@[simp] theorem windowList_eq (ba : ByteArray) (off len : Nat) :
    windowList ba off len = (ba.data.toList.drop off).take len := by
  rw [windowList]
  have hstop : min (off + len) ba.size ≤ ba.size := Nat.min_le_right _ _
  rw [windowList.loop_eq ba off (min (off + len) ba.size) hstop _ (Nat.le_refl _) [],
    List.append_nil]
  grind [List.take_of_length_le, List.length_drop, ByteArray.size_eq_toList_length]

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

/-- Walk `[off, off + n)` checking every byte is zero, one indexed read at a
time: `ba[off]!` is the `ByteArray` extern (`lean_byte_array_fget`, O(1)) and
allocates nothing, where the list check it replaces materialises the window
as a cons list — `ba.data.toList` builds the whole buffer as boxed bytes —
only to compare it against a `replicate` it also has to build.

The caller ensures `off + n ≤ ba.size`, so every read is in bounds.  That
precondition is not decoration: out of bounds `ba[off]!` is `default`, which
for `UInt8` is `0`, so an unguarded walk past the end would report the
padding *valid*.  `allZerosBA` is the guarded entry point. -/
def allZerosBA.loop (ba : ByteArray) (off n : Nat) : Bool :=
  match n with
  | 0 => true
  | n' + 1 => if ba[off]! = 0 then allZerosBA.loop ba (off + 1) n' else false

/-- Every byte of the window at `off` of length `len` is zero — checked by
index, so a padding check builds no list.  The window must fit: a clamped
window shorter than `len` is not the `replicate len 0` the spec's check
demands, and `len` comes off the wire, so this is the check that keeps
`allZerosBA.loop`'s reads in bounds. -/
def allZerosBA (ba : ByteArray) (off len : Nat) : Bool :=
  if min len (ba.size - off) = len then allZerosBA.loop ba off len else false

theorem allZerosBA.loop_eq (ba : ByteArray) : ∀ (off n : Nat), off + n ≤ ba.size →
    (allZerosBA.loop ba off n = true ↔
      (ba.data.toList.drop off).take n = List.replicate n 0) := by
  intro off n
  induction n generalizing off with
  | zero => intro _; simp [allZerosBA.loop]
  | succ n ih =>
      intro h
      rw [Binary.window_peel ba off n (by omega), List.replicate_succ]
      grind [allZerosBA.loop, ih (off + 1) (by omega)]

/-- The indexed zero-check agrees with the list check: `allZerosBA` is true
exactly when the window is the zero run. -/
theorem allZerosBA_eq (ba : ByteArray) (off len : Nat) :
    allZerosBA ba off len = true ↔ windowList ba off len = List.replicate len 0 := by
  rw [allZerosBA]
  by_cases hfit : min len (ba.size - off) = len
  · rw [if_pos hfit, windowList_eq]
    -- the `len = 0` case is not vacuous: `off` may be past the end, and then
    -- `hfit` holds without `off + len ≤ ba.size`.
    rcases Nat.eq_zero_or_pos len with h0 | hpos
    · subst h0; grind [allZerosBA.loop]
    · have hb : off + len ≤ ba.size := by
        have h1 : len ≤ ba.size - off := hfit ▸ Nat.min_le_right len (ba.size - off)
        omega
      grind [allZerosBA.loop_eq ba off len hb]
  · rw [if_neg hfit]
    grind [windowList_eq, take_length_drop_ba, List.length_replicate]

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
  simp only [decodeBoolBA, decodeBool, decodeUintBA_eq]
  grind

/-- `address` at an offset. -/
def decodeAddressBA (ba : ByteArray) (off : Nat) : Option (List UInt8) :=
  match decodeUintBA ba off with
  | some n => if _ : n < 2 ^ 160 then some (encodeBEU 20 n) else none
  | none => none

theorem decodeAddressBA_eq (ba : ByteArray) (off : Nat) :
    decodeAddressBA ba off = decodeAddress (ba.data.toList.drop off) := by
  simp only [decodeAddressBA, decodeAddress, decodeUintBA_eq]
  grind

/-- `bytesN` at an offset: one word's window is all it looks at. -/
def decodeBytesNBA (n : Nat) (ba : ByteArray) (off : Nat) : Option (List UInt8) :=
  decodeBytesN n (windowList ba off 32)

theorem decodeBytesNBA_eq (n : Nat) (ba : ByteArray) (off : Nat) :
    decodeBytesNBA n ba off = decodeBytesN n (ba.data.toList.drop off) := by
  simp only [decodeBytesNBA, windowList_eq, decodeBytesN, List.take_take, Nat.min_self]

/-- Dynamic `bytes` at an offset: the length word, then the payload as a
window.  Neither check builds a list — the length check is arithmetic (a
clamped window at `off + 32` has exactly `len` bytes iff
`min len (ba.size - (off + 32)) = len`) and the padding check is
`allZerosBA`'s index walk — so the only list constructed is the payload,
which is the value. -/
def decodeBytesPrefixBA (ba : ByteArray) (off : Nat) : Option (List UInt8 × Nat) :=
  (natAtBA ba off).bind fun len =>
    let pad := (32 - len % 32) % 32
    if len < 2 ^ 64 ∧ min len (ba.size - (off + 32)) = len ∧
       allZerosBA ba (off + 32 + len) pad then
      some (windowList ba (off + 32) len, 32 + len + pad)
    else none

theorem decodeBytesPrefixBA_eq (ba : ByteArray) (off : Nat) :
    decodeBytesPrefixBA ba off = decodeBytesPrefix (ba.data.toList.drop off) := by
  simp only [decodeBytesPrefixBA, decodeBytesPrefix, natAtBA_eq, allZerosBA_eq, windowList_eq,
    drop_drop_ba, take_length_drop_ba, Nat.add_assoc]

/-! ## the `ValBA` payloads

The runtime value family (`EvmAbi.ValBA`) decodes with `ByteArray`
payloads: the list walkers above convert a window into a cons list per
payload; these return the window itself, one `extract` (a memcpy) per
payload.  Each definition is the `…BA` counterpart under
`ValBA.toList`-shaped maps, so nothing is reproved. -/

/-- The `len` bytes at `off`, as a packed `ByteArray` — the `windowList`
analog for `ValBA` payloads.  Clamped exactly like `windowList`; the
caller checks the clamp before extracting a payload. -/
def windowBA (ba : ByteArray) (off len : Nat) : ByteArray :=
  ba.extract off (min (off + len) ba.size)

/-- A packed window denotes the list window. -/
theorem windowBA_data_toList (ba : ByteArray) (off len : Nat) :
    (windowBA ba off len).data.toList = windowList ba off len := by
  rw [windowBA, windowList_eq, ByteArray.data_extract, Array.toList_extract]
  grind [List.length_drop, ByteArray.size_eq_toList_length, List.take_of_length_le]

/-- Dynamic `bytes`/`string` at an offset: the same length word, clamp and
padding checks as `decodeBytesPrefixBA`, with the payload as one packed
window instead of a cons list. -/
def decodeBytesPrefixBAVal (ba : ByteArray) (off : Nat) : Option (ByteArray × Nat) :=
  (natAtBA ba off).bind fun len =>
    let pad := (32 - len % 32) % 32
    if len < 2 ^ 64 ∧ min len (ba.size - (off + 32)) = len ∧
       allZerosBA ba (off + 32 + len) pad then
      some (windowBA ba (off + 32) len, 32 + len + pad)
    else none

/-- The packed prefix decoder denotes the list one. -/
theorem decodeBytesPrefixBAVal_eq (ba : ByteArray) (off : Nat) :
    (decodeBytesPrefixBAVal ba off).map (fun p => (p.1.data.toList, p.2)) =
      decodeBytesPrefixBA ba off := by
  rw [decodeBytesPrefixBAVal, decodeBytesPrefixBA]
  cases natAtBA ba off <;> simp [windowBA_data_toList]

/-- `bytesN` at an offset, list-free: the payload word is at most 32 bytes,
so every check is arithmetic — the word must be present
(`off + 32 ≤ ba.size`), the payload must fit (`n ≤ 32`), and the rest of
the word must be zero padding — and the payload comes back as one packed
`extract`, exactly like `decodeBytesPrefixBAVal`. -/
def decodeBytesNBAVal (n : Nat) (ba : ByteArray) (off : Nat) : Option ByteArray :=
  if off + 32 ≤ ba.size ∧ n ≤ 32 ∧
     allZerosBA ba (off + n) (32 - n) then
    some (windowBA ba off n)
  else none

/-- The spec's `decodeBytesN` on the clamped 32-byte window is the packed,
list-free condition: the word is present (`off + 32 ≤ ba.size`), the
payload fits (`n ≤ 32`), and the rest of the word is zero padding. -/
private theorem decodeBytesN_window_eq (n : Nat) (ba : ByteArray) (off : Nat) :
    decodeBytesN n (windowList ba off 32) =
      if off + 32 ≤ ba.size ∧ n ≤ 32 ∧ allZerosBA ba (off + n) (32 - n) then
        some (windowList ba off n)
      else none := by
  -- a clamped window is idempotent under `take 32`
  have hW : (windowList ba off 32).take 32 = windowList ba off 32 := by
    simp [windowList_eq, List.take_take]
  -- the packed padding check is exactly the window's tail
  have hz : allZerosBA ba (off + n) (32 - n) = true ↔
      (windowList ba off 32).drop n = List.replicate (32 - n) 0 := by
    rw [allZerosBA_eq, windowList_eq, windowList_eq, ← drop_drop_ba, ← List.drop_take]
  -- the spec's two checks are the three packed guards: the padding halves
  -- are `hz`, and the length halves are `min` arithmetic, which `omega`
  -- decides once the window is named
  have hiff : ((windowList ba off 32).take n).length = n ∧
        (windowList ba off 32).drop n = List.replicate (32 - n) 0 ↔
      off + 32 ≤ ba.size ∧ n ≤ 32 ∧ allZerosBA ba (off + n) (32 - n) := by
    grind [windowList_eq, take_length_drop_ba, drop_drop_ba, List.drop_take,
      List.length_replicate]
  unfold decodeBytesN
  rw [hW]
  grind [windowList_eq, Nat.min_eq_left]

/-- The packed `bytesN` payload denotes the list one. -/
theorem decodeBytesNBAVal_eq (n : Nat) (ba : ByteArray) (off : Nat) :
    (decodeBytesNBAVal n ba off).map (fun w => w.data.toList) =
      decodeBytesNBA n ba off := by
  rw [decodeBytesNBAVal, decodeBytesNBA, decodeBytesN_window_eq]
  split <;> simp [windowBA_data_toList]

/-- `address` as a packed payload: the twelve leading bytes of the word must
be zero, and the address is the twenty that follow.

The list decoder reads the word into a `Nat` and re-expands it with
`encodeBEU 20`, to recover bytes the buffer already held.
`decodeAddress_eq_window` says both of its steps are statements about those
bytes, so this is a zero check and one `extract`. -/
def decodeAddressBAVal (ba : ByteArray) (off : Nat) : Option ByteArray :=
  if off + 32 ≤ ba.size ∧ allZerosBA ba off 12 then
    some (windowBA ba (off + 12) 20)
  else none

/-- The spec's `decodeAddress` on the clamped window is the packed, list-free
condition: the word is present (`off + 32 ≤ ba.size`) and its first twelve
bytes are zero. -/
private theorem decodeAddressBA_window_eq (ba : ByteArray) (off : Nat) :
    decodeAddressBA ba off =
      if off + 32 ≤ ba.size ∧ allZerosBA ba off 12 then
        some (windowList ba (off + 12) 20)
      else none := by
  have hlen : 32 ≤ (ba.data.toList.drop off).length ↔ off + 32 ≤ ba.size := by
    rw [List.length_drop, ← Binary.ByteArray.size_eq_toList_length]; omega
  have hpre : ((ba.data.toList.drop off).take 32).take 12 = windowList ba off 12 := by
    rw [windowList_eq, List.take_take]; simp
  have hpay : ((ba.data.toList.drop off).take 32).drop 12
      = windowList ba (off + 12) 20 := by
    rw [windowList_eq, List.drop_take, drop_drop_ba]
  rw [decodeAddressBA_eq, decodeAddress_eq_window, hpre, hpay]
  by_cases h1 : off + 32 ≤ ba.size
  · by_cases h2 : allZerosBA ba off 12 = true
    · rw [if_pos ⟨hlen.mpr h1, (allZerosBA_eq _ _ _).mp h2⟩, if_pos ⟨h1, h2⟩]
    · rw [if_neg (fun h => h2 ((allZerosBA_eq _ _ _).mpr h.2)),
        if_neg (fun h => h2 h.2)]
  · rw [if_neg (fun h => h1 (hlen.mp h.1)), if_neg (fun h => h1 h.1)]

/-- The packed `address` payload denotes the list one. -/
theorem decodeAddressBAVal_eq (ba : ByteArray) (off : Nat) :
    (decodeAddressBAVal ba off).map (fun w => w.data.toList) =
      decodeAddressBA ba off := by
  rw [decodeAddressBAVal, decodeAddressBA_window_eq]
  split <;> simp [windowBA_data_toList]
/-! ## the `ValBA` decoder

The same walk with `ValBA` values: payload-carrying clauses return
packed windows, the rest are unchanged.  Every definition agrees with its
`…BA` counterpart under the `ValBA.toList` maps below, so the capstones
of the `List` decoder transport. -/

mutual
/-- **Canonical decoder over a `ByteArray`, `ValBA` values**: reads one
canonical value of type `t` at offset `off`. -/
def decodeBAValFast : (t : Ty) → ByteArray → Nat → Option (ValBA t × Nat)
  | .uint m, ba, off => match wordAtBA ba off with
      | some w =>
          -- At `m.bits = 256`, and any wider, the bound holds of every word.  The
          -- test matters: `w.toNat` is what builds the bignum the limbs exist
          -- to avoid, and a `uint256` is almost every uint there is.  Below
          -- 256 the value fits in fewer limbs, so its `toNat` is cheap anyway.
          if hm : 256 ≤ m.bits then
            some (⟨w, toNat_lt_two_pow_of_le w hm⟩, 32)
          else if h : w.toNat < 2 ^ m.bits then some (⟨w, h⟩, 32) else none
      | none => none
  | .int m, ba, off => match decodeIntBA ba off with
      | some i => if h : -((2 ^ (m.bits - 1) : Nat) : Int) ≤ i ∧ i < ((2 ^ (m.bits - 1) : Nat) : Int) then
          some (⟨i, h⟩, 32)
        else none
      | none => none
  | .bool, ba, off => match decodeBoolBA ba off with
      | some b => some (b, 32)
      | none => none
  | .address, ba, off => match decodeAddressBAVal ba off with
      | some bs => if h : bs.size = 20 then some (⟨bs, h⟩, 32) else none
      | none => none
  | .bytesN m, ba, off => match decodeBytesNBAVal m.bytes ba off with
      | some bs => if h : bs.size = m.bytes then some (⟨bs, h⟩, 32) else none
      | none => none
  | .bytes, ba, off => match hp : decodeBytesPrefixBAVal ba off with
      | some (bs, n) =>
          some (⟨bs, by
            have hma : decodeBytesPrefixBA ba off = some (bs.data.toList, n) := by
              rw [← decodeBytesPrefixBAVal_eq ba off, hp]
              rfl
            have hlist : decodeBytesPrefix (ba.data.toList.drop off) = some (bs.data.toList, n) := by
              rw [← decodeBytesPrefixBA_eq ba off]
              exact hma
            simpa [← ByteArray.size_eq_toList_length] using length_lt_of_decodeBytesPrefix hlist⟩, n)
      | none => none
  | .string, ba, off => match hp : decodeBytesPrefixBAVal ba off with
      | some (bs, n) => match hs : String.fromUTF8? bs with
          | some s =>
              some (⟨s, by
                have hma : decodeBytesPrefixBA ba off = some (bs.data.toList, n) := by
                  rw [← decodeBytesPrefixBAVal_eq ba off, hp]
                  rfl
                have hlist : decodeBytesPrefix (ba.data.toList.drop off) = some (bs.data.toList, n) := by
                  rw [← decodeBytesPrefixBA_eq ba off]
                  exact hma
                have hs' : String.fromUTF8? (bs.data.toList.toByteArray) = some s := by
                  rw [dataToList_toByteArray]
                  exact hs
                exact size_toUTF8_lt_of_decodeBytesPrefix hlist hs'⟩, n)
          | none => none
      | none => none
  | .array t, ba, off =>
      match natAtBA ba off with
      | none => none
      | some k => if hb : k < 2 ^ 64 then
          match (decodeElemsBAVal t k).run ba (off + 32) (off + 32 + k * t.headSize)
              (k * t.headSize) with
          | some r => some (⟨r.val.val, by rw [r.val.property]; exact hb⟩, 32 + r.frontier)
          | none => none
        else none
  | .fixedArray t n _, ba, off =>
      match (decodeElemsBAVal t n).run ba off (off + n * t.headSize) (n * t.headSize) with
      | some r => some (r.val, r.frontier)
      | none => none
  | .tuple head tail, ba, off =>
      let hsz := head.headSize + headSizeSum tail
      match (decodeElemBAVal head).run ba off (off + hsz) hsz with
      | none => none
      | some r =>
          match (decodeTupleBAVal tail).run ba r.head r.tails r.frontier with
          | none => none
          | some s => some ((r.val, s.val), s.frontier)
termination_by t => (sizeOf t, 0)

/-- Read one component at its head slot, `ValBA` values. -/
def decodeElemBAVal (t : Ty) : GetBA (ValBA t) := ⟨fun ba ho to E =>
  match t.isStatic with
  | true => match decodeBAValFast t ba ho with
      | some (v, n) => some ⟨v, ho + n, to, E⟩
      | none => none
  | false => match natAtBA ba ho with
      | none => none
      | some o => if o = E then
          match decodeBAValFast t ba to with
          | some (v, n) => some ⟨v, ho + 32, to + n, E + n⟩
          | none => none
        else none⟩
termination_by (sizeOf t, 1)

/-- Read `k` consecutive canonical elements, `ValBA` values. -/
def decodeElemsBAVal (t : Ty) (k : Nat) : GetBA ({ vs : List (ValBA t) // vs.length = k }) :=
  match k with
  | 0 => pure ⟨[], rfl⟩
  | k + 1 => do
      let v ← decodeElemBAVal t
      let ⟨vs, h⟩ ← decodeElemsBAVal t k
      pure ⟨v :: vs, by simp [List.length_cons, h]⟩
termination_by (sizeOf t, k + 2)

/-- Read a canonical tuple, `ValBA` values. -/
def decodeTupleBAVal : (ts : List Ty) → GetBA (TupleValBA ts)
  | [] => pure ()
  | t :: ts => do
      let v ← decodeElemBAVal t
      let vs ← decodeTupleBAVal ts
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

private theorem decode_array_none {t : Ty} {buf : List UInt8}
    (hk : natAt buf 0 = none) : decode (.array t) buf = none := by
  simp only [decode]
  grind

private theorem decode_array_pos {t : Ty} {buf : List UInt8} {k : Nat}
    (hk : natAt buf 0 = some k) (hb : k < 2 ^ 64) :
    decode (.array t) buf =
      match (decodeElems t k).run (buf.drop 32) (buf.drop (32 + k * t.headSize))
          (k * t.headSize) with
      | some ⟨vs, _, rest, E⟩ =>
          some (⟨vs.val, by rw [vs.property]; exact hb⟩, 32 + E, rest)
      | none => none := by
  simp only [decode]
  grind

/-- Above the length bound both decoders reject, so the agreement proofs
dispose of that branch without touching the element walk. -/
private theorem decode_array_big {t : Ty} {buf : List UInt8} {k : Nat}
    (hk : natAt buf 0 = some k) (hb : ¬ k < 2 ^ 64) : decode (.array t) buf = none := by
  simp only [decode]
  grind

theorem decode_rest (t : Ty) (v : t.Val) (buf rest : List UInt8) (n : Nat)
    (h : decode t buf = some (v, n, rest)) : rest = buf.drop n := by
  obtain ⟨hb, hn⟩ := decode_sound t v buf rest n h
  rw [← hb, hn, List.drop_left]

/-! ## the strict API, on the buffer's bytes

`decodeStrictBA` reads the buffer's bytes through the specification, so its
agreement lemma is `rfl` and the capstones below are the `Spec` ones with one
rewrite.  What runs for users is the `ValBA` decoder; this list-valued decoder
exists for the `t.Val` API and the benchmark baseline. -/

/-- Strict decode of a `ByteArray` to specification values: the list decoder
on the buffer's bytes. -/
def decodeStrictBA (t : Ty) (ba : ByteArray) : Option t.Val :=
  Spec.decodeStrict t ba.data.toList

/-- A buffer is a canonical encoding of `t`. -/
def IsCanonicalBA (t : Ty) (ba : ByteArray) : Prop :=
  (decodeStrictBA t ba).isSome = true

instance (t : Ty) (ba : ByteArray) : Decidable (IsCanonicalBA t ba) := by
  unfold IsCanonicalBA
  infer_instance

/-- **Agreement**: reading the buffer's bytes *is* the specification — by
construction, not by a case analysis. -/
theorem decodeStrictBA_eq (t : Ty) (ba : ByteArray) :
    decodeStrictBA t ba = decodeStrict t ba.data.toList := rfl

theorem isCanonicalBA_eq (t : Ty) (ba : ByteArray) :
    IsCanonicalBA t ba ↔ IsCanonical t ba.data.toList := by
  rw [IsCanonicalBA, IsCanonical, decodeStrictBA_eq t ba]


/-! ## the `ValBA` decoder agrees

Every `…BAVal` definition is its `…BA` counterpart under the
`ValBA.toList` maps, so the `List` capstones transport to the runtime
value family by one rewrite. -/

/- The `array` clause of the `ValBA` decoder matches its length word
dependently, so neither scrutinee can be rewritten in place — the same
device as `decodeBA_array_none`/`_pos` resolves it. -/

private theorem decodeBAValFast_array_none {t : Ty} {ba : ByteArray} {off : Nat}
    (hk : natAtBA ba off = none) :
    decodeBAValFast (.array t) ba off = none := by
  simp only [decodeBAValFast]
  grind

private theorem decodeBAValFast_array_pos {t : Ty} {ba : ByteArray} {off k : Nat}
    (hk : natAtBA ba off = some k) (hb : k < 2 ^ 64) :
    decodeBAValFast (.array t) ba off =
      match (decodeElemsBAVal t k).run ba (off + 32) (off + 32 + k * t.headSize)
          (k * t.headSize) with
      | some r => some (⟨r.val.val, by rw [r.val.property]; exact hb⟩, 32 + r.frontier)
      | none => none := by
  simp only [decodeBAValFast]
  grind

/-- Above the length bound both decoders reject, so the agreement proofs
dispose of that branch without touching the element walk. -/
private theorem decodeBAValFast_array_big {t : Ty} {ba : ByteArray} {off k : Nat}
    (hk : natAtBA ba off = some k) (hb : ¬ k < 2 ^ 64) : decodeBAValFast (.array t) ba off = none := by
  simp only [decodeBAValFast]
  grind

/-- `String.fromUTF8?` is injective on the same bytes: the packed window
and its list denotation give the same string. -/
private theorem fromUTF8?_data_eq {b : ByteArray} {l : List UInt8} {s s' : String}
    (hb : b.data.toList = l)
    (h1 : String.fromUTF8? b = some s)
    (h2 : String.fromUTF8? l.toByteArray = some s') : s = s' := by
  have hb' : b = l.toByteArray := by
    grind [ByteArray.data_inj, Array.toList_inj, List.toList_data_toByteArray]
  grind

/-- …and a `some` on one side cannot meet a `none` on the other. -/
private theorem fromUTF8?_some_ne_none_data {b : ByteArray} {l : List UInt8} {s : String}
    (hb : b.data.toList = l)
    (h1 : String.fromUTF8? b = some s)
    (h2 : String.fromUTF8? l.toByteArray = none) : False := by
  have hb' : b = l.toByteArray := by
    grind [ByteArray.data_inj, Array.toList_inj, List.toList_data_toByteArray]
  grind

/-- …and the mirror image. -/
private theorem fromUTF8?_none_ne_some_data {b : ByteArray} {l : List UInt8} {s : String}
    (hb : b.data.toList = l)
    (h1 : String.fromUTF8? b = none)
    (h2 : String.fromUTF8? l.toByteArray = some s) : False := by
  have hb' : b = l.toByteArray := by
    grind [ByteArray.data_inj, Array.toList_inj, List.toList_data_toByteArray]
  grind

/-! ## the `uint` array fast path

The generic walk costs ~eight allocations per element (`GetBA` bind,
`Result`, `Option`, pair); for `.array (.uint m)` at width ≥ 256 the walk
below reads a word with a cons, a `UInt256` and an `Option`.  The `@[csimp]`
swap sits on `decodeBAValFast` rather than `decodeElemsBAVal` because the
`mutual` block's bodies are already compiled when any later attribute
appears; nested arrays keep the generic walk for the same reason. -/

/-- Read `k` consecutive `uint` words at `ho`, bit width ≥ 256 so every
word is in range by `toNat_lt_two_pow_of_le`. -/
def decodeUintElems (m : Width) (hm : 256 ≤ m.bits) (ba : ByteArray) :
    (k ho : Nat) → Option { vs : List (ValBA (.uint m)) // vs.length = k }
  | 0, _ => some ⟨[], rfl⟩
  | k + 1, ho =>
      if h : ho + 32 ≤ ba.size then
        match decodeUintElems m hm ba k (ho + 32) with
        | some ⟨vs, hl⟩ =>
            some ⟨⟨UInt256.ofBEByteArrayAt ba ho h, toNat_lt_two_pow_of_le _ hm⟩ :: vs,
              by simp [hl]⟩
        | none => none
      else none

/-- One `uint` element read, width ≥ 256: a word if it is in bounds, cursors
advanced by 32 on the head side only. -/
private theorem decodeElemBAVal_uint_run (m : Width) (hm : 256 ≤ m.bits) (ba : ByteArray)
    (ho to E : Nat) : (decodeElemBAVal (.uint m)).run ba ho to E =
      if h : ho + 32 ≤ ba.size then
        some ⟨⟨UInt256.ofBEByteArrayAt ba ho h, toNat_lt_two_pow_of_le _ hm⟩, ho + 32, to, E⟩
      else none := by
  rw [decodeElemBAVal]
  grind [decodeBAValFast, wordAtBA, Ty.isStatic]

/-- The fused walk is the generic one.  Static elements never touch the tail
cursor or the frontier, so the run only advances the head — by 32 per word. -/
theorem decodeUintElems_run (m : Width) (hm : 256 ≤ m.bits) (ba : ByteArray) (k : Nat) :
    ∀ ho to E, (decodeElemsBAVal (.uint m) k).run ba ho to E =
      match decodeUintElems m hm ba k ho with
      | some vs => some ⟨vs, ho + 32 * k, to, E⟩
      | none => none := by
  induction k with
  | zero => intro ho to E; simp [decodeElemsBAVal, decodeUintElems]
  | succ k ih =>
      intro ho to E
      rw [decodeElemsBAVal, decodeUintElems]
      simp only [GetBA.bind_run, decodeElemBAVal_uint_run m hm]
      grind [ih (ho + 32) to E, GetBA.pure_run]

/-- `decodeBAValFast` with the `uint` array walk fused (the swap the compiler
acts on; every theorem stays stated over `decodeBAValFast`). -/
def decodeBAValFused (t : Ty) (ba : ByteArray) (off : Nat) : Option (ValBA t × Nat) :=
  match t with
  | .array (.uint m) =>
      if hm : 256 ≤ m.bits then
        match natAtBA ba off with
        | none => none
        | some k =>
            if hb : k < 2 ^ 64 then
              match decodeUintElems m hm ba k (off + 32) with
              | some vs => some (⟨vs.val, by rw [vs.property]; exact hb⟩, 32 + k * 32)
              | none => none
            else none
      else decodeBAValFast (.array (.uint m)) ba off
  | t => decodeBAValFast t ba off

/-- The `uint` array walk, fused into the walker: for `.array (.uint m)` at a
width where every word is in range, the generic element loop is replaced by one
that reads a word per element.  This is the optimization half of the `@[csimp]`
swap; the correctness half is the merged family below. -/
theorem decodeBAValFast_eq_fused : @decodeBAValFast = @decodeBAValFused := by
  funext t ba off
  match t with
  | .uint _ | .int _ | .bool | .address | .bytesN _ | .bytes | .string
  | .fixedArray _ _ _ | .tuple _ _ => rfl
  | .array (.int _) | .array .bool | .array .address | .array (.bytesN _)
  | .array .bytes | .array .string | .array (.array _) | .array (.fixedArray _ _ _)
  | .array (.tuple _ _) => rfl
  | .array (.uint m) =>
      show decodeBAValFast (.array (.uint m)) ba off =
        if hm : 256 ≤ m.bits then
          match natAtBA ba off with
          | none => none
          | some k =>
              if hb : k < 2 ^ 64 then
                match decodeUintElems m hm ba k (off + 32) with
                | some vs => some (⟨vs.val, by rw [vs.property]; exact hb⟩, 32 + k * 32)
                | none => none
              else none
        else decodeBAValFast (.array (.uint m)) ba off
      by_cases hm : 256 ≤ m.bits
      · rw [dif_pos hm]
        cases hk : natAtBA ba off with
        | none =>
            rw [decodeBAValFast_array_none hk]
        | some k =>
            by_cases hb : k < 2 ^ 64
            · rw [decodeBAValFast_array_pos hk hb, decodeUintElems_run m hm ba k]
              simp only [dif_pos hb]
              cases hrec : decodeUintElems m hm ba k (off + 32) with
              | none => rfl
              | some vs => rfl
            · rw [decodeBAValFast_array_big hk hb]
              simp only [dif_neg hb]
      · rw [dif_neg hm]


/-! ## one agreement family: the walker against the specification

The runtime decoder is *defined* as the specification decoder composed with
`ValBA.ofList`, so the gap the `@[csimp]` swap has to close is a single
family: the offset walker reads what `Spec.decode` reads, at the same offset,
under the denotation.  This replaces two families (walker → list walker →
specification) and the list walker between them.

Every clause is an explicit case split, because `grind` cannot push the
denotation's `Option.map` through a `match`: the walker's clauses produce
packed values, the specification's produce list values, and the map sits
outside the match.  `run_of_map_some`/`run_of_map_none` turn the sibling's map
equality into the specification's answer once the walker's match is known.

Most clauses are one `grind`: rewriting the specification side back to the
walker's own primitive puts the *same term* under both matches (`←
decodeIntBA_eq`, `← decodeAddressBA_eq`, `← decodeBoolBA_eq`, and for the two
packed windows `← decodeUintBA_eq` / `← decodeBytesNBA_eq`), and `grind` then
splits that one discriminant and reduces both matches.  The packed windows need
one more hint: the bridge is `map_toNat_wordAtBA` / `decodeBytesNBAVal_eq`, a
*map* equation, so `decodeUintBA` — `natAtBA` by definition — has to be in the
hint list for `grind` to unfold it and meet the bridge's right-hand side.  The
type mismatch is not the obstacle: the walker's `Option UInt256` against the
specification's `Option Nat` is exactly what the old clone transport crossed,
with the same hints.  The hint list is the obstacle.

Two kinds of clause stay explicit.  `bytes`/`string` read a length word and
their result depends on it, so the specification clause is a *dependent* match
(`match hp : decodeBytesPrefix …`); that blocks rewriting its scrutinee back to
the packed primitive, so those clauses split both matches and hand
`decodeBytesPrefixBAVal_eq` (and, for `string`, the three `fromUTF8?_*`
injectivity facts) to `grind`.  `array`/`fixedArray`/`tuple` discharge their
obligation with a sibling's run equality (`decodeElemsBAVal_eq_spec`, …), which
is a map equality over a `GetBA` run: `grind` cannot case the run under the
denotation's map and then apply it, so those clauses case on the run and read
the answer off with `run_of_map_some`/`run_of_map_none`. -/

/-- Reading a `…_eq_spec` map equality at a `some`: the specification's answer
is the sibling's answer, mapped.  This is how a clause reads the specification
out of the walker's own result, and the same shape serves the top-level option
and the three `GetBA` runs. -/
private theorem run_of_map_some {α β : Type} {o : Option α} {f : α → β}
    {rhs : Option β} {r : α} (h : o.map f = rhs) (hr : o = some r) :
    rhs = some (f r) := by
  rw [← h, hr]
  rfl

/-- …and at a `none`. -/
private theorem run_of_map_none {α β : Type} {o : Option α} {f : α → β}
    {rhs : Option β} (h : o.map f = rhs) (hr : o = none) : rhs = none := by
  rw [← h, hr]
  rfl

mutual
/-- **Agreement**: the walker is the specification decoder at the same
offset, under the denotation. -/
theorem decodeBAValFast_eq_spec (t : Ty) (ba : ByteArray) (off : Nat) :
    (decodeBAValFast t ba off).map (fun p => (ValBA.toList t p.1, p.2)) =
      (decode t (ba.data.toList.drop off)).map (fun p => (p.1, p.2.1)) := by
  cases t with
  | uint m =>
      simp only [decodeBAValFast, decode, ← decodeUintBA_eq]
      unfold ValBA.toList
      grind [map_toNat_wordAtBA ba off, decodeUintBA, toNat_lt_two_pow_of_le]
  | int m =>
      simp only [decodeBAValFast, decode, decodeIntBA_eq]
      unfold ValBA.toList
      grind
  | bool =>
      simp only [decodeBAValFast, decode, decodeBoolBA_eq]
      grind [ValBA.toList]
  | address =>
      simp only [decodeBAValFast, decode]
      rw [← decodeAddressBA_eq]
      unfold ValBA.toList
      grind [decodeAddressBAVal_eq ba off, Binary.ByteArray.size_eq_toList_length]
  | bytesN m =>
      simp only [decodeBAValFast, decode, ← decodeBytesNBA_eq]
      unfold ValBA.toList
      grind [decodeBytesNBAVal_eq m.bytes ba off, Binary.ByteArray.size_eq_toList_length]
  | bytes =>
      rw [decodeBAValFast, decode]
      have hpe := decodeBytesPrefixBAVal_eq ba off
      have hpe2 := decodeBytesPrefixBA_eq ba off
      split <;> split <;> grind [ValBA.toList]
  | string =>
      rw [decodeBAValFast, decode]
      have hpe := decodeBytesPrefixBAVal_eq ba off
      have hpe2 := decodeBytesPrefixBA_eq ba off
      repeat' split
      all_goals (simp_all [ValBA.toList]; try (obtain ⟨rfl, rfl⟩ := hpe); simp_all)
      all_goals
        first
        | exact fromUTF8?_data_eq hpe.1 (by assumption) (by assumption)
        | exact fromUTF8?_some_ne_none_data hpe.1 (by assumption) (by assumption)
        | exact fromUTF8?_none_ne_some_data hpe.1 (by assumption) (by assumption)
  | array t =>
      cases hk : natAtBA ba off with
      | none =>
          rw [decodeBAValFast_array_none hk, decode_array_none (by rw [← natAtBA_eq]; exact hk)]
          rfl
      | some k =>
          by_cases hb : k < 2 ^ 64
          case neg =>
              rw [decodeBAValFast_array_big hk hb,
                decode_array_big (by rw [← natAtBA_eq]; exact hk) hb]
              rfl
          rw [decodeBAValFast_array_pos hk hb,
            decode_array_pos (by rw [← natAtBA_eq]; exact hk) hb]
          rw [drop_drop_ba, drop_drop_ba, ← Nat.add_assoc]
          cases he : (decodeElemsBAVal t k).run ba (off + 32) (off + 32 + k * t.headSize)
              (k * t.headSize) with
          | none =>
              rw [run_of_map_none
                (decodeElemsBAVal_eq_spec t k ba (off + 32) (off + 32 + k * t.headSize)
                  (k * t.headSize)) he]
              simp only [Option.map_none]
          | some r =>
              have hh := run_of_map_some
                (decodeElemsBAVal_eq_spec t k ba (off + 32) (off + 32 + k * t.headSize)
                  (k * t.headSize)) he
              rw [hh]
              simp only [Option.map_some]
              unfold ValBA.toList
              rfl
  | fixedArray t n _ =>
      simp only [decodeBAValFast, decode]
      rw [drop_drop_ba]
      cases he : (decodeElemsBAVal t n).run ba off (off + n * t.headSize) (n * t.headSize) with
      | none =>
          rw [run_of_map_none
            (decodeElemsBAVal_eq_spec t n ba off (off + n * t.headSize) (n * t.headSize)) he]
          simp only [Option.map_none]
      | some r =>
          have hh := run_of_map_some
            (decodeElemsBAVal_eq_spec t n ba off (off + n * t.headSize) (n * t.headSize)) he
          rw [hh]
          simp only [Option.map_some]
          unfold ValBA.toList
          rfl
  | tuple head tail =>
      rw [decodeBAValFast, decode]
      have hde := decodeElemBAVal_eq_spec head ba off (off + (head.headSize + headSizeSum tail))
        (head.headSize + headSizeSum tail)
      rw [drop_drop_ba]
      cases h1 : (decodeElemBAVal head).run ba off (off + (head.headSize + headSizeSum tail))
          (head.headSize + headSizeSum tail) with
      | none =>
          rw [run_of_map_none hde h1]
          simp only [Option.map_none]
      | some r =>
          have hh := run_of_map_some hde h1
          rw [hh]
          dsimp only
          cases h2 : (decodeTupleBAVal tail).run ba r.head r.tails r.frontier with
          | none =>
              rw [run_of_map_none
                (decodeTupleBAVal_eq_spec tail ba r.head r.tails r.frontier) h2]
              simp only [Option.map_none]
          | some s =>
              have hh2 := run_of_map_some
                (decodeTupleBAVal_eq_spec tail ba r.head r.tails r.frontier) h2
              rw [hh2]
              simp only [Option.map_some]
              simp only [ValBA.toList.eq_10]
termination_by 8 * sizeOf t

/-- **Agreement**, per component. -/
theorem decodeElemBAVal_eq_spec (t : Ty) (ba : ByteArray) (ho to E : Nat) :
    ((decodeElemBAVal t).run ba ho to E).map
        (fun r => ⟨ValBA.toList t r.val, ba.data.toList.drop r.head,
          ba.data.toList.drop r.tails, r.frontier⟩) =
      (decodeElem t).run (ba.data.toList.drop ho) (ba.data.toList.drop to) E := by
  rw [decodeElemBAVal, decodeElem]
  cases hs : t.isStatic
  · simp only []
    rw [natAtBA_eq]
    cases hnat : natAt (ba.data.toList.drop ho) 0 with
    | none => rfl
    | some o =>
        simp only []
        by_cases hoE : o = E
        · rw [if_pos hoE, if_pos hoE]
          cases hw : decodeBAValFast t ba to with
          | none =>
              rw [Option.map_eq_none_iff.mp (run_of_map_none (decodeBAValFast_eq_spec t ba to) hw)]
              simp only [Option.map_none]
          | some p =>
              obtain ⟨v, n⟩ := p
              have hh := decodeBAValFast_eq_spec t ba to
              rw [hw] at hh
              cases hd : decode t (ba.data.toList.drop to) with
              | none => rw [hd] at hh; simp at hh
              | some q =>
                  obtain ⟨v', n', rest⟩ := q
                  grind [decode_rest t v' _ rest n' hd, drop_drop_ba,
                    Option.map_some, Option.some.injEq, Prod.mk.injEq]
        · rw [if_neg hoE, if_neg hoE]; rfl
  · simp only []
    cases hw : decodeBAValFast t ba ho with
    | none =>
        rw [Option.map_eq_none_iff.mp (run_of_map_none (decodeBAValFast_eq_spec t ba ho) hw)]
        simp only [Option.map_none]
    | some p =>
        obtain ⟨v, n⟩ := p
        have hh := decodeBAValFast_eq_spec t ba ho
        rw [hw] at hh
        cases hd : decode t (ba.data.toList.drop ho) with
        | none => rw [hd] at hh; simp at hh
        | some q =>
            obtain ⟨v', n', rest⟩ := q
            grind [decode_rest t v' _ rest n' hd, drop_drop_ba,
              Option.map_some, Option.some.injEq, Prod.mk.injEq]
termination_by 8 * sizeOf t + 1

/-- **Agreement**, element runs. -/
theorem decodeElemsBAVal_eq_spec (t : Ty) (k : Nat) (ba : ByteArray) (ho to E : Nat) :
    ((decodeElemsBAVal t k).run ba ho to E).map
        (fun r => ⟨⟨r.val.val.map (ValBA.toList t), by simp [r.val.property]⟩,
          ba.data.toList.drop r.head, ba.data.toList.drop r.tails, r.frontier⟩) =
      (decodeElems t k).run (ba.data.toList.drop ho) (ba.data.toList.drop to) E := by
  induction k generalizing ho to E with
  | zero => simp [decodeElemsBAVal, decodeElems]
  | succ k ih =>
      simp only [decodeElemsBAVal, decodeElems, GetBA.bind_run, Get2.bind_run,
        GetBA.pure_run, Get2.pure_run]
      rw [← decodeElemBAVal_eq_spec t ba ho to E]
      cases h : (decodeElemBAVal t).run ba ho to E with
      | none => rfl
      | some r =>
          simp only [Option.map_some]
          rw [← ih r.head r.tails r.frontier]
          grind [GetBA.Result.toList]
termination_by 8 * sizeOf t + 2

/-- **Agreement**, tuples. -/
theorem decodeTupleBAVal_eq_spec : (ts : List Ty) → (ba : ByteArray) →
    (ho to E : Nat) →
    ((decodeTupleBAVal ts).run ba ho to E).map
        (fun r => ⟨TupleValBA.toList ts r.val, ba.data.toList.drop r.head,
          ba.data.toList.drop r.tails, r.frontier⟩) =
      (decodeTuple ts).run (ba.data.toList.drop ho) (ba.data.toList.drop to) E
  | [], ba, ho, to, E => by simp [decodeTupleBAVal, decodeTuple]
  | t :: ts, ba, ho, to, E => by
      simp only [decodeTupleBAVal, decodeTuple, GetBA.bind_run, Get2.bind_run,
        GetBA.pure_run, Get2.pure_run]
      rw [← decodeElemBAVal_eq_spec t ba ho to E]
      cases h : (decodeElemBAVal t).run ba ho to E with
      | none => rfl
      | some r =>
          simp only [Option.map_some]
          rw [← decodeTupleBAVal_eq_spec ts ba r.head r.tails r.frontier]
          cases (decodeTupleBAVal ts).run ba r.head r.tails r.frontier <;>
            simp [TupleValBA.toList_cons]
termination_by ts => 8 * sizeOf ts + 3
end

/-! ## the runtime decoder, defined as the specification

The walker above is an *implementation*, not the definition: `decodeBAVal`
is the specification decoder at the offset, with the payloads materialised as
`ByteArray`s.  The merged family is its whole correctness argument, and the
`@[csimp]` swap is what makes compiled code run the walker in its place. -/

/-- **Runtime decoder**: `Spec.decode` at the offset, with `ValBA` payloads. -/
def decodeBAVal (t : Ty) (ba : ByteArray) (off : Nat) : Option (ValBA t × Nat) :=
  (decode t (ba.data.toList.drop off)).map (fun p => (ValBA.ofList t p.1, p.2.1))

/-- Two answers that *denote* the same thing are equal: `ValBA.toList` is
injective, so the denotation is a faithful reading of a runtime answer. -/
private theorem eq_of_map_toList {t : Ty} {o₁ o₂ : Option (ValBA t × Nat)}
    (h : o₁.map (fun p => (ValBA.toList t p.1, p.2)) =
         o₂.map (fun p => (ValBA.toList t p.1, p.2))) : o₁ = o₂ := by
  cases o₁ with
  | none =>
      cases o₂ with
      | none => rfl
      | some q => simp [Option.map_none] at h
  | some p =>
      cases o₂ with
      | none => simp [Option.map_none] at h
      | some q =>
          obtain ⟨p1, p2⟩ := p
          obtain ⟨q1, q2⟩ := q
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          rw [ValBA.toList_injective t h.1, h.2]

/-- The walker is the definition: both denote the specification's answer. -/
theorem decodeBAValFast_eq : @decodeBAValFast = @decodeBAVal := by
  funext t ba off
  refine eq_of_map_toList ?_
  rw [decodeBAValFast_eq_spec t ba off, decodeBAVal]
  cases hd : decode t (ba.data.toList.drop off) with
  | none => rfl
  | some q =>
      obtain ⟨v, n, rest⟩ := q
      simp only [hd, Option.map_some, ValBA.toList_ofList]

/-- **The swap the compiler acts on**: in compiled code the specification
composition is replaced by the offset walker with the `uint` array fast path
fused in. -/
@[csimp] theorem decodeBAVal_eq_fused : @decodeBAVal = @decodeBAValFused :=
  decodeBAValFast_eq.symm.trans decodeBAValFast_eq_fused

/-- The fused walker is the definition too, by the two halves above. -/
theorem decodeBAValFused_eq : @decodeBAValFused = @decodeBAVal :=
  decodeBAValFast_eq_fused.symm.trans decodeBAValFast_eq

/-- **List-valued fast path**: one packed walk, with the payloads denoted back
to the lists `t.Val` calls for.  This is what keeps `decodeStrictBA` — the
`t.Val`-level decoder, and the benchmark's baseline — off the buffer-slicing
path `Spec.decodeStrict` takes. -/
def decodeStrictBAFast (t : Ty) (ba : ByteArray) : Option t.Val :=
  match decodeBAValFused t ba 0 with
  | some (v, n) => if n = ba.size then some (ValBA.toList t v) else none
  | none => none

/-- **The `t.Val` swap**: the specification-on-the-bytes definition and the
packed walk with the payloads denoted agree.  The two exact-consumption checks
are the same test once `decode_sound` relates the spec's remainder to the byte
count. -/
@[csimp] theorem decodeStrictBA_eq_fast : @decodeStrictBA = @decodeStrictBAFast := by
  funext t ba
  rw [decodeStrictBAFast, decodeStrictBA, decodeStrict, decodeBAValFused_eq, decodeBAVal,
    List.drop_zero]
  cases hd : decode t ba.data.toList with
  | none => rfl
  | some q =>
      obtain ⟨v, n, rest⟩ := q
      have hs := decode_sound t v ba.data.toList rest n hd
      have hbuf : encode t v ++ rest = ba.data.toList := hs.1
      have hlen : n = (encode t v).length := hs.2
      have hlen' : (encode t v).length + rest.length = (ba.data.toList).length := by
        rw [← List.length_append, hbuf]
      simp only [hd, Option.map_some, ValBA.toList_ofList]
      by_cases hn : n = ba.size
      · have hrest : rest = [] := by
          rw [← hlen, hn, ← Binary.ByteArray.size_eq_toList_length] at hlen'
          exact List.eq_nil_of_length_eq_zero (by omega)
        simp only [if_pos hn, if_pos hrest]
      · have hrest : rest ≠ [] := by
          intro hnil
          rw [hnil, List.length_nil, Nat.add_zero, ← hlen,
            ← Binary.ByteArray.size_eq_toList_length] at hlen'
          exact hn hlen'
        simp only [if_neg hn, if_neg hrest]

/-- **Strict `ValBA` decode**: canonical layout, consumed exactly, packed
values. -/
def decodeStrictBAVal (t : Ty) (ba : ByteArray) : Option (ValBA t) :=
  match decodeBAVal t ba 0 with
  | some (v, n) => if n = ba.size then some v else none
  | none => none

/-- **Agreement**: the strict `ValBA` decode denotes the strict list decode of
the same bytes.  With the decoder defined as the specification, this is one
`grind` on the soundness of `Spec.decode`. -/
theorem decodeStrictBAVal_eq (t : Ty) (ba : ByteArray) :
    (decodeStrictBAVal t ba).map (ValBA.toList t) = decodeStrictBA t ba := by
  rw [decodeStrictBAVal, decodeStrictBA, decodeStrict, decodeBAVal, List.drop_zero]
  cases hl : decode t ba.data.toList with
  | none => rfl
  | some q =>
      obtain ⟨v, n, rest⟩ := q
      have hs := decode_sound t v ba.data.toList rest n hl
      have hbuf : encode t v ++ rest = ba.data.toList := hs.1
      have hlen : n = (encode t v).length := hs.2
      simp only [hl, Option.map_some, ValBA.toList_ofList]
      by_cases hn : n = ba.size
      · have hrest : rest = [] := by
          have h1 : (encode t v).length + rest.length = (ba.data.toList).length := by
            rw [← List.length_append, hbuf]
          rw [← hlen, hn, ← Binary.ByteArray.size_eq_toList_length] at h1
          exact List.eq_nil_of_length_eq_zero (by omega)
        simp only [if_pos hn, if_pos hrest, Option.map_some, ValBA.toList_ofList]
      · have hrest : rest ≠ [] := by
          intro hnil
          have h1 : (encode t v).length + rest.length = (ba.data.toList).length := by
            rw [← List.length_append, hbuf]
          rw [hnil, List.length_nil, Nat.add_zero, ← hlen,
            ← Binary.ByteArray.size_eq_toList_length] at h1
          exact hn h1
        simp only [if_neg hn, if_neg hrest, Option.map_none]

/-! ## capstones, `ByteArray` end to end -/

/-- **Canonical roundtrip**: what `encodeByteArray` writes, the offset
decoder reads back. -/
theorem decodeStrictBA_encodeByteArray (t : Ty) (v : t.Val)
    (hb : (encodeByteArray t v).size < 2 ^ 256) :
    decodeStrictBA t (encodeByteArray t v) = some v := by
  rw [size_encodeByteArray] at hb
  rw [decodeStrictBA_eq t, data_toList_encodeByteArray]
  exact decodeStrict_encode t v hb

/-- **Canonical uniqueness**: a strictly decodable buffer *is* the encoding
of its decoded value. -/
theorem encodeByteArray_of_decodeStrictBA (t : Ty) (ba : ByteArray)
    (v : t.Val) (h : decodeStrictBA t ba = some v) : encodeByteArray t v = ba := by
  rw [decodeStrictBA_eq t] at h
  grind [Binary.ByteArray.data_inj, Array.toList_inj, data_toList_encodeByteArray,
    encode_of_decodeStrict]

/-- **Image characterization** (capstone). -/
theorem isCanonicalBA_iff (t : Ty) (ba : ByteArray)
    (hb : ba.size < 2 ^ 256) :
    IsCanonicalBA t ba ↔ ∃ v, encodeByteArray t v = ba := by
  rw [isCanonicalBA_eq t ba]
  rw [ByteArray.size_eq_toList_length] at hb
  rw [isCanonical_iff t _ hb]
  constructor
  · rintro ⟨v, he⟩
    refine ⟨v, ?_⟩
    grind [Binary.ByteArray.data_inj, Array.toList_inj, data_toList_encodeByteArray]
  · rintro ⟨v, he⟩
    exact ⟨v, by grind [data_toList_encodeByteArray, Array.toList_inj,
      Binary.ByteArray.data_inj]⟩

/-- **Strict-decoder characterization** (capstone). -/
theorem decodeStrictBA_eq_some_iff (t : Ty) (ba : ByteArray)
    (v : t.Val) (hb : ba.size < 2 ^ 256) :
    decodeStrictBA t ba = some v ↔ encodeByteArray t v = ba := by
  constructor
  · exact encodeByteArray_of_decodeStrictBA t ba v
  · intro he
    rw [← he]
    exact decodeStrictBA_encodeByteArray t v (by rw [he]; exact hb)

end EvmAbi.Codec.ByteArray
