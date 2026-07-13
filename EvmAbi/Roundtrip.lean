import EvmAbi.Roundtrip.Basic
import EvmAbi.Roundtrip.Primitives
import EvmAbi.Roundtrip.Packing
import EvmAbi.Roundtrip.DynArray
import EvmAbi.Roundtrip.DynTuple

/-
# ABI encode/decode roundtrip proofs

Aggregator + the composable `wfFactsWF` visitor and the top-level results `roundtrip_wf` /
`roundtrip_args_wff` (nested structs included). No `sorry`. The proof is organized as:

* `Roundtrip.Basic`       — tactic macros + ByteArray-slice read helpers
* `Roundtrip.Primitives`  — atom/bytes/string roundtrips
* `Roundtrip.Packing`     — encoder characterization (arrayPack/tuplePack, size = headSize)
* `Roundtrip.DynArray`    — WF dynamic array / fixedArray roundtrips
* `Roundtrip.DynTuple`    — WF dynamic tuple roundtrip + alignment + encodeArgs level
This file: the WF visitor over all well-formed types, plus concrete-signature demos.
-/

open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode
set_option autoImplicit false

/-! ### ABI function-call level roundtrip: `encodeArgs` then `decodeArgs` -/

/-- The practical capstone: encoding function arguments then decoding them recovers the values.
    Reduces to the tuple roundtrip (`encodeArgs = encode (.tuple types)`,
    `decodeArgs = decode (.tuple types) >>= extract`). Carries the necessary WF preconditions
    (`data.size < 2^256` and the head-area bound the dynamic tuple decoder requires). -/
theorem roundtrip_args_wf (types : List ABIType) (data : ByteArray) (values : List ABIValue)
    (hrt : ∀ t ∈ types, ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 →
      encode t v = Except.ok ev → data.extract o (o + ev.size) = ev → decode t data o = Except.ok (v, o + ev.size))
    (hsize : ∀ t ∈ types, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdvd : ∀ t ∈ types, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size)
    (hwf : data.size < 2^256)
    (hbd : (types.foldl (fun a t => a + headSize t) 0) + 32 ≤ data.size)
    (henc : encodeArgs types values = Except.ok data) :
    decodeArgs types data 0 = Except.ok values := by
  unfold encodeArgs at henc
  split at henc
  · simp at henc
  · have hrt_tuple : decode (.tuple types) data 0 = Except.ok (.tuple values, 0 + data.size) :=
      roundtrip_tuple_wf types data hrt hsize hdvd (.tuple values) data 0 hwf (by simpa using hbd) henc
        (by simp)
    unfold decodeArgs
    rw [hrt_tuple]
    rfl

/-- The three facts a type contributes to a roundtrip composition: the offset-general
    WF roundtrip, the static size law, and 32-byte alignment. -/
structure WFFacts (t : ABIType) : Prop where
  rt : ∀ (v : ABIValue) (ri : RoundtripInput t v), ri.enc.size < 2^256 →
    decode t ri.data ri.off = Except.ok (v, ri.off + ri.enc.size)
  size_eq : isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t
  szdvd : ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size

/-! Shared `WFFacts` component builders — the non-tuple cases, reused by both the tuple-free
    (`wfFacts`) and well-formed (`wfFactsWF`) recursions. -/

theorem WFFacts.uint (s : ByteSize) : WFFacts (.uint s) :=
  ⟨fun v ri _ => roundtrip_off_uint s v ri,
   fun _ v ev he => size_eq_uint s v ev he,
   fun v ev _ he => by rw [size_eq_uint s v ev he]; exact headSize_dvd_32 (.uint s)⟩
theorem WFFacts.int (s : ByteSize) : WFFacts (.int s) :=
  ⟨fun v ri _ => roundtrip_off_int s v ri,
   fun _ v ev he => size_eq_int s v ev he,
   fun v ev _ he => by rw [size_eq_int s v ev he]; exact headSize_dvd_32 (.int s)⟩
theorem WFFacts.bool : WFFacts .bool :=
  ⟨fun v ri _ => roundtrip_off_bool v ri,
   fun _ v ev he => size_eq_bool v ev he,
   fun v ev _ he => by rw [size_eq_bool v ev he]; exact headSize_dvd_32 .bool⟩
theorem WFFacts.address : WFFacts .address :=
  ⟨fun v ri _ => roundtrip_off_address v ri,
   fun _ v ev he => size_eq_address v ev he,
   fun v ev _ he => by rw [size_eq_address v ev he]; exact headSize_dvd_32 .address⟩
theorem WFFacts.fixedBytes (s : ByteSize) : WFFacts (.fixedBytes s) :=
  ⟨fun v ri _ => roundtrip_off_fixedBytes s v ri,
   fun _ v ev he => size_eq_fixedBytes s v ev he,
   fun v ev _ he => by rw [size_eq_fixedBytes s v ev he]; exact headSize_dvd_32 (.fixedBytes s)⟩
theorem WFFacts.bytes : WFFacts .bytes :=
  ⟨fun v ri _ => roundtrip_off_bytes v ri,
   fun h => absurd h (by simp [isDynamic]), szdvd_bytes⟩
theorem WFFacts.string : WFFacts .string :=
  ⟨fun v ri _ => roundtrip_off_string v ri,
   fun h => absurd h (by simp [isDynamic]), szdvd_string⟩
theorem WFFacts.array (e : ABIType) (ih : WFFacts e) : WFFacts (.array e) :=
  ⟨fun v ri hwf => match ri with
    | ⟨enc, data, off, he, hd⟩ =>
        roundtrip_array_wf e data (fun v' ev' o' hlt he' hd' => ih.rt v' ⟨ev', data, o', he', hd'⟩ hlt) ih.szdvd v enc off hwf he hd,
   fun h => absurd h (by simp [isDynamic]),
   fun v ev hwf he => szdvd_array e ih.szdvd v ev hwf he⟩
theorem WFFacts.fixedArray (n : Nat) (e : ABIType) (ih : WFFacts e) : WFFacts (.fixedArray n e) :=
  ⟨fun v ri hwf => match ri with
    | ⟨enc, data, off, he, hd⟩ =>
        roundtrip_fixedArray_wf n e data (fun v' ev' o' hlt he' hd' => ih.rt v' ⟨ev', data, o', he', hd'⟩ hlt) ih.szdvd v enc off hwf he hd,
   fun hstat v ev he => by
      have hstat_e : isDynamic e = false := by simpa [isDynamic] using hstat
      exact size_eq_fixedArray_core n e (ih.size_eq hstat_e) hstat_e v ev he,
   fun v ev hwf he => szdvd_fixedArray n e ih.szdvd v ev hwf he⟩

/-! ### Covering nested tuples (structs): the well-formed fragment

Excludes only the one pathology — an empty fixed-array of a dynamic element type
(`fixedArray 0 e`, `e` dynamic), which encodes to 0 bytes and genuinely fails to decode.
Over well-formed types every dynamic encoding is >= 32 bytes, so the dynamic tuple
decoder's head-area bound is derivable and tuples compose inside containers. -/


-- "no empty fixed-array of a dynamic element type, anywhere" (excludes the one pathology)
inductive WellFormedType : ABIType → Prop
  | uint (s : ByteSize) : WellFormedType (.uint s)
  | int (s : ByteSize) : WellFormedType (.int s)
  | bool : WellFormedType .bool
  | address : WellFormedType .address
  | bytes : WellFormedType .bytes
  | fixedBytes (s : ByteSize) : WellFormedType (.fixedBytes s)
  | string : WellFormedType .string
  | array (e : ABIType) : WellFormedType e → WellFormedType (.array e)
  | fixedArray (n : Nat) (e : ABIType) : (isDynamic e = true → 0 < n) → WellFormedType e → WellFormedType (.fixedArray n e)
  | tuple (ts : List ABIType) : (∀ t ∈ ts, WellFormedType t) → WellFormedType (.tuple ts)

theorem dyn_encoding_ge_32_bytes (v : ABIValue) (ev : ByteArray) (henc : encode .bytes v = Except.ok ev) : 32 ≤ ev.size := by
  cases v with
  | bytes v' =>
    openEnc henc
    split at henc
    · have he : ev = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size) := (Except.ok.inj henc).symm
      rw [he, ByteArray.size_append]; have := uint256ToBytes_size_ge v'.size; omega
    · exact absurd henc (by simp)
  | _ => badVal henc

theorem dyn_encoding_ge_32_string (v : ABIValue) (ev : ByteArray) (henc : encode .string v = Except.ok ev) : 32 ≤ ev.size := by
  cases v with
  | string v' =>
    openEnc henc
    split at henc
    · have he : ev = uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size) := (Except.ok.inj henc).symm
      rw [he, ByteArray.size_append]; have := uint256ToBytes_size_ge v'.toUTF8.size; omega
    · exact absurd henc (by simp)
  | _ => badVal henc

theorem dyn_encoding_ge_32_array (e : ABIType) (v : ABIValue) (ev : ByteArray) (henc : encode (.array e) v = Except.ok ev) : 32 ≤ ev.size := by
  cases v with
  | array vals =>
    obtain ⟨encd, -, -, he⟩ := encode_array_inv e vals ev henc
    rw [he, ByteArray.size_append]; have := uint256ToBytes_size_ge vals.length; omega
  | _ => badArrVal henc e

theorem dyn_encoding_ge_32_fixedArray (n : Nat) (e : ABIType) (hn : isDynamic e = true → 0 < n)
    (hdyn : isDynamic (.fixedArray n e) = true) (v : ABIValue) (ev : ByteArray)
    (henc : encode (.fixedArray n e) v = Except.ok ev) : 32 ≤ ev.size := by
  cases v with
  | array vals =>
    obtain ⟨encd, hEL', hvn, he⟩ := encode_fixedArray_inv n e vals ev henc
    have hisdyn_e : isDynamic e = true := by simpa [isDynamic] using hdyn
    have hlen_eq : encd.length = vals.length := encodeListElems_length e vals encd hEL'
    rw [he, hisdyn_e, arrayPack_dyn, ByteArray.size_append]
    have hge := dynHeadsFrom_size_ge encd (if encd.length = 0 then 32 else encd.length * 32)
    have : 0 < encd.length := by rw [hlen_eq, hvn]; exact hn hisdyn_e
    omega
  | _ => badArrVal henc e

theorem tupleHeadsFrom_ge_32 : ∀ (encd : List (Bool × ByteArray)) (off : Nat), (∃ b ∈ encd, b.1 = true) →
    32 ≤ ((tupleHeadsFrom off encd).foldl (·++·) ByteArray.empty).size := by
  intro encd
  induction encd with
  | nil => intro off h; obtain ⟨b, hb, _⟩ := h; simp at hb
  | cons x xs ih =>
    intro off h
    obtain ⟨d, e⟩ := x
    rw [tupleHeadsFrom_cons, ba_foldl_cons, ByteArray.size_append]
    cases d with
    | true =>
      simp only [if_true]
      have := uint256ToBytes_size_ge off; omega
    | false =>
      simp only [Bool.false_eq_true, if_false]
      have hxs : ∃ b ∈ xs, b.1 = true := by
        obtain ⟨b, hb, hb1⟩ := h
        rcases List.mem_cons.mp hb with rfl | hb'
        · simp at hb1
        · exact ⟨b, hb', hb1⟩
      have := ih off hxs; omega

theorem go_has_dyn_entry (ts : List ABIType) :
    ∀ (vs : List ABIValue) (encd : List (Bool × ByteArray)),
      instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd →
      ts.any isDynamic = true → ∃ b ∈ encd, b.1 = true := by
  induction ts with
  | nil => intro vs encd _ h; simp at h
  | cons t ts' ih =>
    intro vs encd hgo h
    obtain ⟨v, vs', b, tail, rfl, hb, htail, rfl⟩ := go_cons_inv t ts' vs encd hgo
    rw [List.any_cons] at h
    by_cases hd : isDynamic t = true
    · exact ⟨(isDynamic t, b), by simp, hd⟩
    · have hdf : isDynamic t = false := by simpa using hd
      have h' : ts'.any isDynamic = true := by rw [hdf, Bool.false_or] at h; exact h
      obtain ⟨b', hb', hb'1⟩ := ih vs' tail htail h'
      exact ⟨b', List.mem_cons_of_mem _ hb', hb'1⟩

theorem dyn_encoding_ge_32_tuple (ts : List ABIType) (hdyn : isDynamic (.tuple ts) = true)
    (v : ABIValue) (ev : ByteArray) (henc : encode (.tuple ts) v = Except.ok ev) : 32 ≤ ev.size := by
  cases v with
  | tuple vs =>
    obtain ⟨encd, hgo, hpack⟩ := encode_tuple_inv ts vs ev henc
    have hany : (ts.map isDynamic).any id = true := by rw [tuple_any_isDynamic]; exact hdyn
    have hany_ts : ts.any isDynamic = true := by simpa [List.any_map] using hany
    have hHAeq : (ts.map headSize).foldl (· + ·) 0 = ts.foldl (fun a t => a + headSize t) 0 := by rw [List.foldl_map]
    rw [hpack, tuplePack_dyn _ _ _ hany, hHAeq, ByteArray.size_append]
    have hentry := go_has_dyn_entry ts vs encd hgo hany_ts
    have hheads := tupleHeadsFrom_ge_32 encd (ts.foldl (fun a t => a + headSize t) 0) hentry
    omega
  | _ => badVal henc

theorem dyn_encoding_ge_32 (t : ABIType) (hwf : WellFormedType t) (hdyn : isDynamic t = true)
    (v : ABIValue) (ev : ByteArray) (henc : encode t v = Except.ok ev) : 32 ≤ ev.size := by
  cases t with
  | bytes => exact dyn_encoding_ge_32_bytes v ev henc
  | string => exact dyn_encoding_ge_32_string v ev henc
  | array e => exact dyn_encoding_ge_32_array e v ev henc
  | fixedArray n e => cases hwf with | fixedArray _ _ hn _ => exact dyn_encoding_ge_32_fixedArray n e hn hdyn v ev henc
  | tuple ts => exact dyn_encoding_ge_32_tuple ts hdyn v ev henc
  | uint s => exact absurd hdyn (by simp [isDynamic])
  | int s => exact absurd hdyn (by simp [isDynamic])
  | bool => exact absurd hdyn (by simp [isDynamic])
  | address => exact absurd hdyn (by simp [isDynamic])
  | fixedBytes s => exact absurd hdyn (by simp [isDynamic])

theorem go_has_big_dyn_entry (ts : List ABIType) (hwf : ∀ t ∈ ts, WellFormedType t) :
    ∀ (vs : List ABIValue) (encd : List (Bool × ByteArray)),
      instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd →
      ts.any isDynamic = true → (∀ b ∈ encd, b.1 = true → b.2.size < 2^256) →
      ∃ b ∈ encd, b.1 = true ∧ 32 ≤ b.2.size := by
  induction ts with
  | nil => intro vs encd _ h _; simp at h
  | cons t ts' ih =>
    intro vs encd hgo h hbnd
    have hmemt : t ∈ (t :: ts') := by simp
    obtain ⟨v, vs', b, tail, rfl, hb_enc, htail, rfl⟩ := go_cons_inv t ts' vs encd hgo
    rw [List.any_cons] at h
    by_cases hd : isDynamic t = true
    · exact ⟨(isDynamic t, b), by simp, hd, dyn_encoding_ge_32 t (hwf t hmemt) hd v b hb_enc⟩
    · have hdf : isDynamic t = false := by simpa using hd
      have h' : ts'.any isDynamic = true := by rw [hdf, Bool.false_or] at h; exact h
      obtain ⟨b', hb', hb'1, hb'sz⟩ := ih (fun t' ht' => hwf t' (List.mem_cons_of_mem t ht')) vs' tail htail h'
        (fun b'' hb'' => hbnd b'' (List.mem_cons_of_mem _ hb''))
      exact ⟨b', List.mem_cons_of_mem _ hb', hb'1, hb'sz⟩

theorem dyn_tuple_hbd (ts : List ABIType) (hwf : ∀ t ∈ ts, WellFormedType t)
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdyn : ts.any isDynamic = true) (v : ABIValue) (enc : ByteArray)
    (henc : encode (.tuple ts) v = Except.ok enc) (hsz : enc.size < 2^256) :
    ts.foldl (fun a t => a + headSize t) 0 + 32 ≤ enc.size := by
  cases v with
  | tuple vs =>
    obtain ⟨encd, hgo, hpack⟩ := encode_tuple_inv ts vs enc henc
    have hany : (ts.map isDynamic).any id = true := by simpa [List.any_map] using hdyn
    have hHAeq : (ts.map headSize).foldl (· + ·) 0 = ts.foldl (fun a t => a + headSize t) 0 := by rw [List.foldl_map]
    have hpackht : enc = (tupleHeadsFrom (ts.foldl (fun a t => a + headSize t) 0) encd).foldl (·++·) ByteArray.empty ++ tupleTails encd := by
      rw [hpack, tuplePack_dyn _ _ _ hany, hHAeq]
    have hpsz : enc.size = ((tupleHeadsFrom (ts.foldl (fun a t => a + headSize t) 0) encd).foldl (·++·) ByteArray.empty).size + (tupleTails encd).size := by
      rw [hpackht, ByteArray.size_append]
    have hge := tupleHeadsFrom_size_ge ts hsize vs encd (ts.foldl (fun a t => a + headSize t) 0) hgo
    have hbnd_dyn : ∀ b ∈ encd, b.1 = true → b.2.size < 2^256 := fun b hb hb1 => by
      have := tupleTails_mem_le encd b hb hb1; omega
    obtain ⟨b, hb, hb1, hbsize⟩ := go_has_big_dyn_entry ts hwf vs encd hgo hdyn hbnd_dyn
    have := tupleTails_mem_le encd b hb hb1
    omega
  | _ => badVal henc

theorem size_eq_tuple_wf (ts : List ABIType)
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hstat : isDynamic (.tuple ts) = false) (v : ABIValue) (ev : ByteArray)
    (henc : encode (.tuple ts) v = Except.ok ev) : ev.size = headSize (.tuple ts) := by
  cases v with
  | tuple vs =>
    obtain ⟨encd, hgo, hpack⟩ := encode_tuple_inv ts vs ev henc
    have hany : (ts.map isDynamic).any id = false := by rw [tuple_any_isDynamic]; exact hstat
    rw [hpack, tuplePack_static _ _ _ hany]
    exact tuplePackStatic_size_wf ts hsize (tuple_static_elems ts hstat) vs encd hgo
  | _ => badVal henc

/-- `WFFacts` for every well-formed type, INCLUDING tuples (structs). The dynamic-tuple `rt`
    discharges its head-area bound internally via `dyn_tuple_hbd`, so it stays bound-free and
    composes into arrays/tuples at every level. -/
theorem wfFactsWF : (t : ABIType) → WellFormedType t → WFFacts t
  | .uint s, _ => .uint s
  | .int s, _ => .int s
  | .bool, _ => .bool
  | .address, _ => .address
  | .fixedBytes s, _ => .fixedBytes s
  | .bytes, _ => .bytes
  | .string, _ => .string
  | .array e, hwf => .array e (wfFactsWF e (by cases hwf with | array _ h => exact h))
  | .fixedArray n e, hwf => .fixedArray n e (wfFactsWF e (by cases hwf with | fixedArray _ _ _ h => exact h))
  | .tuple ts, hwf =>
      have hfield : ∀ t' ∈ ts, WellFormedType t' := by cases hwf with | tuple _ h => exact h
      ⟨fun v ri hsz => by
          rcases ri with ⟨enc, data, off, henc, hdata⟩
          cases hdyn : ts.any isDynamic with
          | false =>
            have hstat_tuple : isDynamic (.tuple ts) = false := by rw [← tuple_any_isDynamic]; simpa [List.any_map] using hdyn
            exact roundtrip_tuple_stat_wf ts data
              (fun t' ht' v' ev' o' hlt he' hd' => (wfFactsWF t' (hfield t' ht')).rt v' ⟨ev', data, o', he', hd'⟩ hlt)
              (fun t' ht' => (wfFactsWF t' (hfield t' ht')).size_eq)
              hstat_tuple v enc off hsz henc hdata
          | true =>
            have hhbd := dyn_tuple_hbd ts hfield (fun t' ht' => (wfFactsWF t' (hfield t' ht')).size_eq) hdyn v enc henc hsz
            have hle : off + enc.size ≤ data.size := not_gt_of_extract_eq data off enc.size (by rw [hdata]) (by omega)
            have hbd : off + ts.foldl (fun a t => a + headSize t) 0 + 32 ≤ data.size := by omega
            exact roundtrip_tuple_wf ts data
              (fun t' ht' v' ev' o' hlt he' hd' => (wfFactsWF t' (hfield t' ht')).rt v' ⟨ev', data, o', he', hd'⟩ hlt)
              (fun t' ht' => (wfFactsWF t' (hfield t' ht')).size_eq)
              (fun t' ht' => (wfFactsWF t' (hfield t' ht')).szdvd)
              v enc off hsz hbd henc hdata,
       fun hstat => size_eq_tuple_wf ts (fun t' ht' => (wfFactsWF t' (hfield t' ht')).size_eq) hstat,
       fun v ev hsz henc => szdvd_tuple ts
          (fun t' ht' => (wfFactsWF t' (hfield t' ht')).size_eq)
          (fun t' ht' => (wfFactsWF t' (hfield t' ht')).szdvd) v ev hsz henc⟩
  termination_by t => sizeOf t
  decreasing_by
    all_goals simp_wf
    all_goals first
      | omega
      | (have hm := ‹_ ∈ _›; have := List.sizeOf_lt_of_mem hm; omega)

/-- Clean roundtrip (offset 0) for ANY well-formed type via a `RoundtripInput` — atomics,
    bytes/string, nested arrays/fixedArrays, AND tuples/structs (nested to any depth). -/
theorem roundtrip_of_input (t : ABIType) (hwf : WellFormedType t) (v : ABIValue) (ri : RoundtripInput t v)
    (hsz : ri.enc.size < 2^256) : decode t ri.data ri.off = Except.ok (v, ri.off + ri.enc.size) :=
  (wfFactsWF t hwf).rt v ri hsz

/-- Clean roundtrip (offset 0) for ANY well-formed type — atomics, bytes/string, nested
    arrays/fixedArrays, AND tuples/structs (nested to any depth). -/
theorem roundtrip_wf (t : ABIType) (hwf : WellFormedType t) (v : ABIValue) (data : ByteArray)
    (hsz : data.size < 2^256) (henc : encode t v = Except.ok data) :
    decode t data 0 = Except.ok (v, data.size) := by
  have h := roundtrip_of_input t hwf v (RoundtripInput.self t v data henc) hsz
  simpa using h

/-- Function-call roundtrip for ANY well-formed argument list, including struct arguments —
    no per-signature proof needed. -/
theorem roundtrip_args_wff (types : List ABIType) (data : ByteArray) (values : List ABIValue)
    (hwf : ∀ t ∈ types, WellFormedType t)
    (hsz : data.size < 2^256)
    (henc : encodeArgs types values = Except.ok data) :
    decodeArgs types data 0 = Except.ok values := by
  unfold encodeArgs at henc
  split at henc
  · simp at henc
  · have hd : decode (.tuple types) data 0 = Except.ok (.tuple values, data.size) := by
      simpa using
        roundtrip_of_input (.tuple types) (.tuple types hwf) (.tuple values)
          (RoundtripInput.self (.tuple types) (.tuple values) data henc) hsz
    unfold decodeArgs; rw [hd]; rfl

/-! ### Concrete signatures, derived from the well-formed visitor

With `wfFactsWF` in hand the worked signatures are one-liners: the visitor supplies every
per-field fact and (for dynamic tuples) discharges the head-area bound internally, so these
carry only `enc.size < 2^256` — no manual dispatch, no `hbd`. -/

/-- `(bytes, uintN)` — a mixed dynamic+static tuple roundtrip. -/
theorem roundtrip_tuple_bytes_uint (s : ByteSize) (data : ByteArray)
    (v : ABIValue) (enc : ByteArray) (off : Nat) (hwf : enc.size < 2^256)
    (henc : encode (.tuple [.bytes, .uint s]) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.tuple [.bytes, .uint s]) data off = Except.ok (v, off + enc.size) :=
  (wfFactsWF (.tuple [.bytes, .uint s]) (.tuple _ (by intro t ht; fin_cases ht <;> constructor))).rt
    v ⟨enc, data, off, henc, hdata⟩ hwf

/-- ERC20-style `(bytes, uintN)` argument decode. -/
theorem roundtrip_args_bytes_uint (s : ByteSize) (data : ByteArray) (values : List ABIValue)
    (hwf : data.size < 2^256) (henc : encodeArgs [.bytes, .uint s] values = Except.ok data) :
    decodeArgs [.bytes, .uint s] data 0 = Except.ok values :=
  roundtrip_args_wff [.bytes, .uint s] data values (by intro t ht; fin_cases ht <;> constructor) hwf henc

/-- `(address, uintN)` — static tuple (ERC20 `transfer(to, amount)` arguments). -/
theorem roundtrip_tuple_addr_uint (s : ByteSize) (data : ByteArray)
    (v : ABIValue) (enc : ByteArray) (off : Nat) (hwf : enc.size < 2^256)
    (henc : encode (.tuple [.address, .uint s]) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.tuple [.address, .uint s]) data off = Except.ok (v, off + enc.size) :=
  (wfFactsWF (.tuple [.address, .uint s]) (.tuple _ (by intro t ht; fin_cases ht <;> constructor))).rt
    v ⟨enc, data, off, henc, hdata⟩ hwf

/-- ERC20 `transfer`-style argument decode. -/
theorem roundtrip_args_addr_uint (s : ByteSize) (data : ByteArray) (values : List ABIValue)
    (hwf : data.size < 2^256) (henc : encodeArgs [.address, .uint s] values = Except.ok data) :
    decodeArgs [.address, .uint s] data 0 = Except.ok values :=
  roundtrip_args_wff [.address, .uint s] data values (by intro t ht; fin_cases ht <;> constructor) hwf henc

/-- `(uintN, bytes)` — mixed static + dynamic tuple. -/
theorem roundtrip_tuple_uint_bytes (s : ByteSize) (data : ByteArray)
    (v : ABIValue) (enc : ByteArray) (off : Nat) (hwf : enc.size < 2^256)
    (henc : encode (.tuple [.uint s, .bytes]) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.tuple [.uint s, .bytes]) data off = Except.ok (v, off + enc.size) :=
  (wfFactsWF (.tuple [.uint s, .bytes]) (.tuple _ (by intro t ht; fin_cases ht <;> constructor))).rt
    v ⟨enc, data, off, henc, hdata⟩ hwf
