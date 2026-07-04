import EvmAbi.Roundtrip.Packing

/-! WF-conditioned dynamic array / fixedArray roundtrips (roundtrip_array_wf, roundtrip_fixedArray_wf) + groundwork. -/

open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode
set_option autoImplicit false

/-! ## Dynamic-element groundwork (for the well-formedness-conditioned roundtrip)

The dynamic-element roundtrips (dyn array/fixedArray/tuple) hold only under a well-formedness
bound (`enc.size < 2^256`, so every offset fits in 32 bytes): without it an encode can succeed
while producing head pointers `≥ 2^256`, which `uint256ToBytes` renders as >32-byte heads,
corrupting the layout the decoder relies on — so the *unconditional* statement is genuinely
false, not merely unproven, and this file carries no unconditional dynamic-element roundtrip.
The lemmas below are the verified core of the WF-conditioned argument — in particular
`ddeg_concat`, which shows `decodeDynamicElemsGo` recovers the values from the head/tail layout.
They are assembled into `roundtrip_{array,fixedArray,tuple}_wf` and the `wfFactsWF` visitor
(nested structs included), all sorry-free. -/

theorem roundUp32_dvd (n : Nat) : 32 ∣ roundUp32 n := ⟨(n+31)/32, by unfold roundUp32; ring⟩

theorem roundUp32_eq_of_dvd (n : Nat) (h : 32 ∣ n) : roundUp32 n = n := by
  obtain ⟨k, rfl⟩ := h; unfold roundUp32; omega

theorem uint256ToBytes_size32 (v : Nat) (hv : v < 2 ^ 256) : (uint256ToBytes v).size = 32 :=
  uint256ToBytes_size v (natToBytes_size_bound v hv)

/-- The running head-pointer offsets written by `arrayPack` for a dynamic array. -/
def dynHeadsFrom (off : Nat) : List ByteArray → List ByteArray
  | [] => []
  | e :: es => uint256ToBytes off :: dynHeadsFrom (off + roundUp32 e.size) es

theorem dynHeadsFrom_cons (off : Nat) (e : ByteArray) (es : List ByteArray) :
    dynHeadsFrom off (e :: es) = uint256ToBytes off :: dynHeadsFrom (off + roundUp32 e.size) es := rfl

theorem concat_size_dvd (encd : List ByteArray) (h : ∀ b ∈ encd, 32 ∣ b.size) :
    32 ∣ (encd.foldl (·++·) ByteArray.empty).size := by
  induction encd with
  | nil => simp
  | cons x xs ih =>
    rw [ba_foldl_cons, ByteArray.size_append]
    exact Nat.dvd_add (h x (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem dynHeadsFrom_size (l : List ByteArray) :
    ∀ (off : Nat), off + (l.foldl (·++·) ByteArray.empty).size < 2^256 → (∀ b ∈ l, 32 ∣ b.size) →
    ((dynHeadsFrom off l).foldl (·++·) ByteArray.empty).size = 32 * l.length := by
  induction l with
  | nil => intro off _ _; simp [dynHeadsFrom]
  | cons e es ih =>
    intro off hb halign
    rw [dynHeadsFrom_cons, ba_foldl_cons, ByteArray.size_append]
    have hofflt : off < 2^256 := by rw [ba_foldl_cons, ByteArray.size_append] at hb; omega
    rw [uint256ToBytes_size32 off hofflt]
    have hru : roundUp32 e.size = e.size := roundUp32_eq_of_dvd e.size (halign e (by simp))
    have hb' : (off + e.size) + (es.foldl (·++·) ByteArray.empty).size < 2^256 := by
      rw [ba_foldl_cons, ByteArray.size_append] at hb; omega
    rw [hru, ih (off + e.size) hb' (fun b hbm => halign b (by simp [hbm]))]
    grind

/-- One step of the dynamic-element head grid: with the pointer grid for `ev :: er` at slot `i`
and the packed tails at `curTail`, read off the slot's pointer word and `ev`'s payload, and
re-establish the grid/tails slices for `er` at slot `i + 1` / tail `curTail + ev.size`.
Packages the slice bookkeeping of `ddeg_concat`'s cons case. -/
theorem dynHeads_grid_step (data ev : ByteArray) (er : List ByteArray) (i off curTail : Nat)
    (halign : ∀ b ∈ ev :: er, 32 ∣ b.size)
    (hbound : curTail + ((ev :: er).foldl (·++·) ByteArray.empty).size < 2^256)
    (hheads : data.extract (off + i * 32) (off + i * 32 + 32 * (ev :: er).length)
            = (dynHeadsFrom curTail (ev :: er)).foldl (·++·) ByteArray.empty)
    (htails : data.extract (off + curTail) (off + curTail + ((ev :: er).foldl (·++·) ByteArray.empty).size)
            = (ev :: er).foldl (·++·) ByteArray.empty) :
    data.extract (off + i * 32) (off + i * 32 + 32) = uint256ToBytes curTail
    ∧ data.extract (off + curTail) (off + curTail + ev.size) = ev
    ∧ data.extract (off + (i + 1) * 32) (off + (i + 1) * 32 + 32 * er.length)
        = (dynHeadsFrom (curTail + ev.size) er).foldl (·++·) ByteArray.empty
    ∧ data.extract (off + curTail + ev.size) (off + curTail + ev.size + (er.foldl (·++·) ByteArray.empty).size)
        = er.foldl (·++·) ByteArray.empty := by
  have hru_ev : roundUp32 ev.size = ev.size := roundUp32_eq_of_dvd ev.size (halign ev (by simp))
  have hcurTail_lt : curTail < 2^256 := by rw [ba_foldl_cons, ByteArray.size_append] at hbound; omega
  have hP32 : (uint256ToBytes curTail).size = 32 := uint256ToBytes_size32 curTail hcurTail_lt
  have hbound' : curTail + ev.size + (er.foldl (·++·) ByteArray.empty).size < 2^256 := by
    rw [ba_foldl_cons, ByteArray.size_append] at hbound; omega
  have hheads_exp : (dynHeadsFrom curTail (ev :: er)).foldl (·++·) ByteArray.empty
      = uint256ToBytes curTail ++ (dynHeadsFrom (curTail + ev.size) er).foldl (·++·) ByteArray.empty := by
    rw [dynHeadsFrom_cons, ba_foldl_cons, hru_ev]
  rw [show (ev :: er).length = er.length + 1 from by simp, hheads_exp] at hheads
  rw [ba_foldl_cons ev er] at htails
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact extract_head32 data (off + i * 32) (off + i * 32 + 32 * (er.length + 1))
      (uint256ToBytes curTail) ((dynHeadsFrom (curTail + ev.size) er).foldl (·++·) ByteArray.empty)
      hP32 (by omega) hheads
  · exact extract_append_left_of_slice data (off + curTail) ev (er.foldl (·++·) ByteArray.empty) htails
  · have hYsz : ((dynHeadsFrom (curTail + ev.size) er).foldl (·++·) ByteArray.empty).size = 32 * er.length :=
      dynHeadsFrom_size er (curTail + ev.size) (by omega) (fun b hb => halign b (by simp [hb]))
    rw [show off + (i + 1) * 32 = off + i * 32 + 32 from by omega, ← hYsz]
    exact extract_tail_after32 data (off + i * 32) (off + i * 32 + 32 * (er.length + 1))
      (uint256ToBytes curTail) _ hP32 (by rw [hYsz]; omega) hheads
  · exact extract_append_right_of_slice data (off + curTail) ev (er.foldl (·++·) ByteArray.empty) htails

/-- Core dynamic-element decode: `decodeDynamicElemsGo` recovers the values, given that the head
    region (a grid of 32-byte pointers) and the contiguous tail region are present in `data` and
    all offsets fit in 32 bytes (`curTail + tails.size < 2^256`). -/
theorem ddeg_concat (e : ABIType) (data : ByteArray)
    (hrt : ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 → encode e v = Except.ok ev →
      data.extract o (o + ev.size) = ev → (foldABIType DecoderEntry e) data o = Except.ok (v, o + ev.size))
    :
    ∀ (vs : List ABIValue) (encd : List ByteArray) (i n off curTail maxEnd : Nat) (vals : List ABIValue),
      encodeListElems (encode e) vs = Except.ok encd →
      n = i + vs.length →
      maxEnd = off + curTail →
      curTail + (encd.foldl (·++·) ByteArray.empty).size < 2^256 →
      (∀ b ∈ encd, 32 ∣ b.size) →
      off + n * 32 ≤ data.size →
      data.extract (off + i * 32) (off + i * 32 + 32 * encd.length) = (dynHeadsFrom curTail encd).foldl (·++·) ByteArray.empty →
      data.extract (off + curTail) (off + curTail + (encd.foldl (·++·) ByteArray.empty).size) = encd.foldl (·++·) ByteArray.empty →
      decodeDynamicElemsGo (foldABIType DecoderEntry e) n i off data vals maxEnd
        = Except.ok (vals.reverse ++ vs, off + curTail + (encd.foldl (·++·) ByteArray.empty).size) := by
  intro vs
  induction vs with
  | nil =>
    intro encd i n off curTail maxEnd vals henc hn hmax _ _ _ _ _
    simp only [encodeListElems, Except.ok.injEq] at henc; subst henc
    simp only [List.foldl_nil, ByteArray.size_empty, Nat.add_zero, List.append_nil]
    unfold decodeDynamicElemsGo
    have hni : ¬ i < n := by simp only [List.length_nil, Nat.add_zero] at hn; omega
    rw [dif_neg hni, hmax]
  | cons v rest ih =>
    intro encd i n off curTail maxEnd vals henc hn hmax hbound halign hsize hheads htails
    obtain ⟨ev, er, hev, her, rfl⟩ := encodeListElems_cons_ok e v rest encd henc
    obtain ⟨hheadchunk, htailchunk, hheads', htails'⟩ :=
      dynHeads_grid_step data ev er i off curTail halign hbound hheads htails
    have hev_lt : ev.size < 2^256 := by rw [ba_foldl_cons, ByteArray.size_append] at hbound; omega
    have hbound' : (curTail + ev.size) + (er.foldl (·++·) ByteArray.empty).size < 2^256 := by
      rw [ba_foldl_cons, ByteArray.size_append] at hbound; omega
    have hdec_v : (foldABIType DecoderEntry e) data (off + curTail) = Except.ok (v, off + curTail + ev.size) :=
      hrt v ev (off + curTail) hev_lt hev htailchunk
    have hni : i < n := by simp only [List.length_cons] at hn; omega
    unfold decodeDynamicElemsGo
    rw [dif_pos hni]
    rw [if_neg (show ¬ (off + i * 32 + 32 > data.size) from by omega)]
    simp only [hheadchunk, bytesToNat_uint256ToBytes]
    rw [hdec_v]
    show decodeDynamicElemsGo (foldABIType DecoderEntry e) n (i + 1) off data (v :: vals) (max (off + curTail + ev.size) maxEnd) = _
    rw [show max (off + curTail + ev.size) maxEnd = off + (curTail + ev.size) from by rw [hmax]; omega]
    rw [ih er (i + 1) n off (curTail + ev.size) (off + (curTail + ev.size)) (v :: vals) her
        (by simp only [List.length_cons] at hn ⊢; omega) rfl hbound'
        (fun b hb => halign b (by simp [hb])) hsize hheads'
        (by rw [show off + (curTail + ev.size) = off + curTail + ev.size from by omega]; exact htails')]
    have h1 : (v :: vals).reverse ++ rest = vals.reverse ++ v :: rest := by simp
    have h2 : off + (curTail + ev.size) + (er.foldl (·++·) ByteArray.empty).size = off + curTail + ((ev :: er).foldl (·++·) ByteArray.empty).size := by
      rw [ba_foldl_cons, ByteArray.size_append]; omega
    rw [h1, h2]

/-! ### arrayPack characterization + size divisibility (dynamic groundwork, cont.) -/

/-- The fold step used by `arrayPack` for a dynamic array (defeq to its destructuring lambda). -/
abbrev packStep : Nat × ByteArray × ByteArray → ByteArray → Nat × ByteArray × ByteArray :=
  fun acc enc => (acc.1 + roundUp32 enc.size, acc.2.1 ++ uint256ToBytes acc.1, acc.2.2 ++ enc)

theorem packStep_fold (encd : List ByteArray) (startOff : Nat) (h0 t0 : ByteArray) :
    encd.foldl packStep (startOff, h0, t0)
      = (startOff + (encd.map (fun e => roundUp32 e.size)).sum,
         h0 ++ (dynHeadsFrom startOff encd).foldl (·++·) ByteArray.empty,
         t0 ++ encd.foldl (·++·) ByteArray.empty) := by
  induction encd generalizing startOff h0 t0 with
  | nil => simp [dynHeadsFrom]
  | cons e es ih =>
    rw [List.foldl_cons]
    show es.foldl packStep (startOff + roundUp32 e.size, h0 ++ uint256ToBytes startOff, t0 ++ e) = _
    rw [ih (startOff + roundUp32 e.size) (h0 ++ uint256ToBytes startOff) (t0 ++ e), dynHeadsFrom_cons,
        ba_foldl_cons (uint256ToBytes startOff) (dynHeadsFrom (startOff + roundUp32 e.size) es),
        ba_foldl_cons e es]
    simp only [List.map_cons, List.sum_cons, ByteArray.append_assoc, Nat.add_assoc]

/-- `arrayPack` for a dynamic array is the head-pointer grid followed by the concatenated tails. -/
theorem arrayPack_dyn (encd : List ByteArray) :
    arrayPack true encd
      = (dynHeadsFrom (if encd.length = 0 then 32 else encd.length * 32) encd).foldl (·++·) ByteArray.empty
        ++ encd.foldl (·++·) ByteArray.empty := by
  unfold arrayPack
  simp only [Bool.not_true]
  rw [show (List.foldl packStep (if encd.length = 0 then 32 else encd.length * 32, ByteArray.empty, ByteArray.empty) encd) = _ from packStep_fold encd _ ByteArray.empty ByteArray.empty]
  simp [ByteArray.empty_append]

theorem uint256ToBytes_size_ge (v : Nat) : 32 ≤ (uint256ToBytes v).size := by
  unfold uint256ToBytes padLeft; split
  · omega
  · rename_i h; simp only [ByteArray.size_append, zeros_size]; omega

theorem dynHeadsFrom_size_ge (l : List ByteArray) : ∀ (off : Nat), 32 * l.length ≤ ((dynHeadsFrom off l).foldl (·++·) ByteArray.empty).size := by
  induction l with
  | nil => intro off; simp [dynHeadsFrom]
  | cons e es ih =>
    intro off
    rw [dynHeadsFrom_cons, ba_foldl_cons, ByteArray.size_append]
    have := uint256ToBytes_size_ge off
    have := ih (off + roundUp32 e.size)
    simp only [List.length_cons]; omega

/-- Under the well-formedness bound, a dynamic array's packing is 32-aligned. -/
theorem arrayPack_size_dvd (elemDyn : Bool) (encd : List ByteArray)
    (hbound : (arrayPack elemDyn encd).size < 2^256) (halign : ∀ b ∈ encd, 32 ∣ b.size) :
    32 ∣ (arrayPack elemDyn encd).size := by
  cases elemDyn with
  | false =>
    have : arrayPack false encd = encd.foldl (·++·) ByteArray.empty := by simp [arrayPack]
    rw [this]; exact concat_size_dvd encd halign
  | true =>
    by_cases hemp : encd = []
    · subst hemp; rw [arrayPack_dyn]; simp [dynHeadsFrom]
    · have hne0 : encd.length ≠ 0 := fun h => hemp (List.eq_nil_of_length_eq_zero h)
      rw [arrayPack_dyn] at hbound ⊢
      rw [ByteArray.size_append] at hbound ⊢
      rw [show (if encd.length = 0 then 32 else encd.length * 32) = encd.length * 32 from by rw [if_neg hne0]] at hbound ⊢
      have htails_dvd : 32 ∣ (encd.foldl (·++·) ByteArray.empty).size := concat_size_dvd encd halign
      have hge : 32 * encd.length ≤ ((dynHeadsFrom (encd.length * 32) encd).foldl (·++·) ByteArray.empty).size := dynHeadsFrom_size_ge encd (encd.length * 32)
      have hbnd : encd.length * 32 + (encd.foldl (·++·) ByteArray.empty).size < 2^256 := by omega
      rw [dynHeadsFrom_size encd (encd.length * 32) hbnd halign]
      exact Nat.dvd_add ⟨encd.length, rfl⟩ htails_dvd

/-! ### WF-conditioned dynamic array roundtrip -/

theorem mem_size_le_concat (encd : List ByteArray) (b : ByteArray) (hb : b ∈ encd) :
    b.size ≤ (encd.foldl (·++·) ByteArray.empty).size := by
  induction encd with
  | nil => simp at hb
  | cons x xs ih =>
    rw [ba_foldl_cons, ByteArray.size_append]
    rcases List.mem_cons.mp hb with h | h
    · subst h; omega
    · have := ih h; omega

theorem concat_le_arrayPack (elemDyn : Bool) (encd : List ByteArray) :
    (encd.foldl (·++·) ByteArray.empty).size ≤ (arrayPack elemDyn encd).size := by
  cases elemDyn with
  | false => rw [show arrayPack false encd = encd.foldl (·++·) ByteArray.empty from by simp [arrayPack]]
  | true => rw [arrayPack_dyn, ByteArray.size_append]; omega

theorem decodeStaticElemsGo_concat_wf (e : ABIType) (data : ByteArray)
    (dec : ByteArray → Nat → Except Error (ABIValue × Nat))
    (hdec : ∀ (v : ABIValue) (ev : ByteArray) (off : Nat), ev.size < 2^256 → encode e v = Except.ok ev →
      data.extract off (off + ev.size) = ev → dec data off = Except.ok (v, off + ev.size)) :
    ∀ (vs : List ABIValue) (encd : List ByteArray) (i n pos : Nat) (acc : List ABIValue),
      n = i + vs.length →
      encodeListElems (encode e) vs = Except.ok encd →
      (encd.foldl (·++·) ByteArray.empty).size < 2^256 →
      data.extract pos (pos + (encd.foldl (·++·) ByteArray.empty).size) = encd.foldl (·++·) ByteArray.empty →
      decodeStaticElemsGo dec n i pos data acc
        = Except.ok (acc.reverse ++ vs, pos + (encd.foldl (·++·) ByteArray.empty).size) := by
  intro vs
  induction vs with
  | nil =>
    intro encd i n pos acc hn henc _ _
    simp only [encodeListElems, Except.ok.injEq] at henc; subst henc
    simp only [List.foldl_nil, ByteArray.size_empty, Nat.add_zero, List.append_nil]
    unfold decodeStaticElemsGo
    have hni : ¬ i < n := by simp only [List.length_nil, Nat.add_zero] at hn; omega
    simp [hni]
  | cons v rest ih =>
    intro encd i n pos acc hn henc hbound hslice
    obtain ⟨ev, er, hev, her, rfl⟩ := encodeListElems_cons_ok e v rest encd henc
    rw [ba_foldl_cons] at hslice hbound ⊢
    have hsz : (ev ++ er.foldl (·++·) ByteArray.empty).size = ev.size + (er.foldl (·++·) ByteArray.empty).size := ByteArray.size_append
    have hev_lt : ev.size < 2^256 := by rw [hsz] at hbound; omega
    have hslice_ev := extract_append_left_of_slice data pos ev (er.foldl (·++·) ByteArray.empty) hslice
    have hslice_rest := extract_append_right_of_slice data pos ev (er.foldl (·++·) ByteArray.empty) hslice
    unfold decodeStaticElemsGo
    have hni : i < n := by simp only [List.length_cons] at hn; omega
    rw [dif_pos hni, hdec v ev pos hev_lt hev hslice_ev]
    show decodeStaticElemsGo dec n (i + 1) (pos + ev.size) data (v :: acc) = _
    have hbound' : (er.foldl (·++·) ByteArray.empty).size < 2^256 := by rw [hsz] at hbound; omega
    rw [ih er (i + 1) n (pos + ev.size) (v :: acc) (by simp only [List.length_cons] at hn ⊢; omega) her hbound' hslice_rest]
    have h1 : (v :: acc).reverse ++ rest = acc.reverse ++ v :: rest := by simp
    have h2 : pos + ev.size + (er.foldl (·++·) ByteArray.empty).size = pos + (ev ++ er.foldl (·++·) ByteArray.empty).size := by rw [hsz]; omega
    rw [h1, h2]


/-- Elements of a successful `encodeListElems` are 32-byte aligned (their sizes are bounded by
the pack, so the per-element `hdvd` applies). Shared preamble of the array/fixedArray roundtrips. -/
theorem encodeListElems_align (e : ABIType)
    (hdvd : ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode e v = Except.ok ev → 32 ∣ ev.size)
    (vals : List ABIValue) (encd : List ByteArray) (d : Bool)
    (hEL : encodeListElems (encode e) vals = Except.ok encd)
    (hsz : (arrayPack d encd).size < 2^256) :
    ∀ b ∈ encd, 32 ∣ b.size := fun b hb => by
  obtain ⟨w, hw⟩ := encodeListElems_mem e vals encd hEL b hb
  have hble : b.size ≤ (arrayPack d encd).size :=
    le_trans (mem_size_le_concat encd b hb) (concat_le_arrayPack d encd)
  exact hdvd w b (by omega) hw

/-- Step lemma for the static-element branch: decoding the plain concatenation of
statically-packed element encodings at `off` recovers the values — the static counterpart of
`decodeDynamicElems_pack_wf`. -/
theorem decodeStaticElems_concat_wf (e : ABIType) (data : ByteArray)
    (hrt : ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 → encode e v = Except.ok ev →
      data.extract o (o + ev.size) = ev → (foldABIType DecoderEntry e) data o = Except.ok (v, o + ev.size))
    (vals : List ABIValue) (encd : List ByteArray) (off : Nat)
    (hEL : encodeListElems (encode e) vals = Except.ok encd)
    (hsz : (encd.foldl (·++·) ByteArray.empty).size < 2^256)
    (hslice : data.extract off (off + (encd.foldl (·++·) ByteArray.empty).size)
              = encd.foldl (·++·) ByteArray.empty) :
    decodeStaticElems (foldABIType DecoderEntry e) vals.length data off
      = Except.ok (vals, off + (encd.foldl (·++·) ByteArray.empty).size) := by
  unfold decodeStaticElems
  rw [decodeStaticElemsGo_concat_wf e data (foldABIType DecoderEntry e) hrt vals encd 0 vals.length off []
        (by omega) hEL hsz hslice]
  rw [List.reverse_nil, List.nil_append]

/-- Step lemma for the dynamic-element branch of the array/fixedArray roundtrips: decoding the
`arrayPack true` region (32-byte head-pointer grid ++ concatenated tails) at `off` recovers the
values. Packages the heads/tails split, the grid sizing, and the `ddeg_concat` induction. -/
theorem decodeDynamicElems_pack_wf (e : ABIType) (data : ByteArray)
    (hrt : ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 → encode e v = Except.ok ev →
      data.extract o (o + ev.size) = ev → (foldABIType DecoderEntry e) data o = Except.ok (v, o + ev.size))
    (vals : List ABIValue) (encd : List ByteArray) (off : Nat)
    (hvne : vals ≠ [])
    (hEL : encodeListElems (encode e) vals = Except.ok encd)
    (halign : ∀ b ∈ encd, 32 ∣ b.size)
    (hsz : (arrayPack true encd).size < 2^256)
    (hslice : data.extract off (off + (arrayPack true encd).size) = arrayPack true encd) :
    decodeDynamicElems (foldABIType DecoderEntry e) vals.length data off
      = Except.ok (vals, off + (arrayPack true encd).size) := by
  have hlenv : encd.length = vals.length := encodeListElems_length e vals encd hEL
  have hne0 : encd.length ≠ 0 := by rw [hlenv]; exact fun h => hvne (List.eq_nil_of_length_eq_zero h)
  have hvpos : vals.length ≠ 0 := by rw [← hlenv]; exact hne0
  set heads := (dynHeadsFrom (vals.length * 32) encd).foldl (·++·) ByteArray.empty with hh
  set tails := encd.foldl (·++·) ByteArray.empty with ht
  have hpackht : arrayPack true encd = heads ++ tails := by
    rw [hh, ht, arrayPack_dyn, if_neg hne0, hlenv]
  have hpsz : (arrayPack true encd).size = heads.size + tails.size := by
    rw [hpackht, ByteArray.size_append]
  have hge : vals.length * 32 ≤ heads.size := by
    rw [hh]; have := dynHeadsFrom_size_ge encd (vals.length * 32); rw [hlenv] at this; omega
  have hheads_size : heads.size = vals.length * 32 := by
    rw [hh]; have := dynHeadsFrom_size encd (vals.length * 32) (by rw [← ht]; omega) halign
    rw [hlenv] at this; omega
  have hslice' : data.extract off (off + (heads ++ tails).size) = heads ++ tails := by
    rw [← hpackht]; exact hslice
  have hheads_ex := extract_append_left_of_slice data off heads tails hslice'
  have htails_ex := extract_append_right_of_slice data off heads tails hslice'
  have hheadseq : data.extract (off + 0 * 32) (off + 0 * 32 + 32 * encd.length)
      = (dynHeadsFrom (vals.length * 32) encd).foldl (·++·) ByteArray.empty := by
    simp only [Nat.zero_mul, Nat.add_zero]
    rw [show 32 * encd.length = heads.size from by rw [hheads_size, hlenv]; ring, ← hh]
    exact hheads_ex
  have htailseq : data.extract (off + vals.length * 32) (off + vals.length * 32 + tails.size) = tails := by
    rw [← hheads_size]; exact htails_ex
  have hbound_all : off + (arrayPack true encd).size ≤ data.size :=
    not_gt_of_extract_eq data off (arrayPack true encd).size (by rw [hslice]) (by omega)
  unfold decodeDynamicElems
  rw [ddeg_concat e data hrt vals encd 0 vals.length off (vals.length * 32) (off + vals.length * 32) []
        hEL (by omega) rfl (by rw [← ht]; omega) halign (by omega) hheadseq htailseq]
  rw [List.reverse_nil, List.nil_append,
      show off + vals.length * 32 + tails.size = off + (arrayPack true encd).size from by
        rw [hpsz, hheads_size]; omega]

theorem roundtrip_array_wf (e : ABIType) (data : ByteArray)
    (hrt : ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 → encode e v = Except.ok ev →
      data.extract o (o + ev.size) = ev → decode e data o = Except.ok (v, o + ev.size))
    (hdvd : ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode e v = Except.ok ev → 32 ∣ ev.size)
    (v : ABIValue) (enc : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256)
    (henc : encode (.array e) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.array e) data off = Except.ok (v, off + enc.size) := by
  cases v with
  | array vals =>
    obtain ⟨encd, hEL', hlt, hpack⟩ := encode_array_inv e vals enc henc
    have hPsz : (uint256ToBytes vals.length).size = 32 :=
      uint256ToBytes_size vals.length (natToBytes_size_bound vals.length hlt)
    set packed := arrayPack (isDynamic e) encd with hpk
    have hencsz : enc.size = 32 + packed.size := by rw [hpack, ByteArray.size_append, hPsz]
    have hpk_lt : packed.size < 2^256 := by rw [hencsz] at hwf; omega
    have hbound_all : off + enc.size ≤ data.size :=
      not_gt_of_extract_eq data off enc.size (by rw [hdata]) (by rw [hencsz]; omega)
    have hb32 : ¬ (off + 32 > data.size) := by rw [hencsz] at hbound_all; omega
    have hslice : data.extract off (off + (uint256ToBytes vals.length ++ packed).size)
                = uint256ToBytes vals.length ++ packed := by rw [← hpack]; exact hdata
    have hprefix : data.extract off (off + 32) = uint256ToBytes vals.length := by
      have := extract_append_left_of_slice data off (uint256ToBytes vals.length) packed hslice
      rwa [hPsz] at this
    have hlen : bytesToNat (data.extract off (off + 32)) = vals.length := by
      rw [hprefix]; exact bytesToNat_uint256ToBytes vals.length
    have hsuffix : data.extract (off + 32) (off + 32 + packed.size) = packed := by
      have := extract_append_right_of_slice data off (uint256ToBytes vals.length) packed hslice
      rwa [hPsz] at this
    have halign : ∀ b ∈ encd, 32 ∣ b.size :=
      encodeListElems_align e hdvd vals encd (isDynamic e) hEL' (by rw [← hpk]; exact hpk_lt)
    unfold decode foldABIType
    delta instABIVisitorDecoderEntry
    dsimp
    rw [if_neg hb32]
    simp only [hlen]
    cases hdyn : isDynamic e with
    | false =>
      have hpackc : packed = encd.foldl (·++·) ByteArray.empty := by rw [hpk, hdyn]; simp [arrayPack]
      simp only [decodeArrayElems, Bool.false_eq_true, if_false]
      rw [decodeStaticElems_concat_wf e data hrt vals encd (off + 32) hEL'
            (by rw [← hpackc]; exact hpk_lt) (by rw [← hpackc]; exact hsuffix)]
      rw [show off + 32 + (encd.foldl (·++·) ByteArray.empty).size = off + enc.size from by rw [← hpackc]; omega]
      rfl
    | true =>
      simp only [decodeArrayElems, if_true]
      by_cases hvemp : vals = []
      · subst hvemp
        simp only [encodeListElems, Except.ok.injEq] at hEL'; subst hEL'
        have hpe : packed = ByteArray.empty := by rw [hpk, hdyn, arrayPack_dyn]; simp [dynHeadsFrom]
        simp only [List.length_nil]
        unfold decodeDynamicElems decodeDynamicElemsGo
        simp only [Nat.lt_irrefl, ↓reduceDIte, List.reverse_nil]
        rw [show off + enc.size = off + 32 from by rw [hencsz, hpe, ByteArray.size_empty]]
        rfl
      · have hpkT : packed = arrayPack true encd := by rw [hpk, hdyn]
        rw [decodeDynamicElems_pack_wf e data hrt vals encd (off + 32) hvemp hEL' halign
              (by rw [← hpkT]; exact hpk_lt) (by rw [← hpkT]; exact hsuffix)]
        rw [show off + 32 + (arrayPack true encd).size = off + enc.size from by rw [← hpkT]; omega]
        rfl
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | tuple _ => badArrVal henc e

/-! ### Concrete WF roundtrips for the common dynamic-element arrays -/

theorem szdvd_bytes (v : ABIValue) (ev : ByteArray) (_hsz : ev.size < 2^256) (henc : encode .bytes v = Except.ok ev) : 32 ∣ ev.size := by
  cases v with
  | bytes v' =>
    openEnc henc
    split at henc
    · rename_i hlt
      have hev := Except.ok.inj henc
      rw [← hev, ByteArray.size_append]
      have hPsz : (uint256ToBytes v'.size).size = 32 := uint256ToBytes_size v'.size (natToBytes_size_bound v'.size (by assumption))
      have hpad : (padRight v' (roundUp32 v'.size)).size = roundUp32 v'.size := by
        unfold padRight; split
        · have : v'.size ≤ roundUp32 v'.size := by unfold roundUp32; omega
          omega
        · simp [zeros_size]; unfold roundUp32; omega
      rw [hPsz, hpad]; exact Nat.dvd_add (by norm_num) (roundUp32_dvd v'.size)
    · badErr henc ev
  | _ => badVal henc

theorem szdvd_string (v : ABIValue) (ev : ByteArray) (_hsz : ev.size < 2^256) (henc : encode .string v = Except.ok ev) : 32 ∣ ev.size := by
  cases v with
  | string v' =>
    openEnc henc
    split at henc
    · rename_i hlt
      have hev := Except.ok.inj henc
      rw [← hev, ByteArray.size_append]
      have hPsz : (uint256ToBytes v'.toUTF8.size).size = 32 := uint256ToBytes_size v'.toUTF8.size (natToBytes_size_bound v'.toUTF8.size (by assumption))
      have hpad : (padRight v'.toUTF8 (roundUp32 v'.toUTF8.size)).size = roundUp32 v'.toUTF8.size := by
        unfold padRight; split
        · have : v'.toUTF8.size ≤ roundUp32 v'.toUTF8.size := by unfold roundUp32; omega
          omega
        · simp [zeros_size]; unfold roundUp32; omega
      rw [hPsz, hpad]; exact Nat.dvd_add (by norm_num) (roundUp32_dvd v'.toUTF8.size)
    · badErr henc ev
  | _ => badVal henc

/-- `bytes[]` roundtrips under the well-formedness bound (`enc.size < 2^256`). -/
theorem roundtrip_bytes_array_wf (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256) (henc : encode (.array .bytes) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.array .bytes) data off = Except.ok (v, off + enc.size) :=
  roundtrip_array_wf .bytes data
    (fun v ev o _ h2 h3 => roundtrip_off_bytes v ev data o h2 h3) szdvd_bytes v enc off hwf henc hdata

/-- `string[]` roundtrips under the well-formedness bound (`enc.size < 2^256`). -/
theorem roundtrip_string_array_wf (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256) (henc : encode (.array .string) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.array .string) data off = Except.ok (v, off + enc.size) :=
  roundtrip_array_wf .string data
    (fun v ev o _ h2 h3 => roundtrip_off_string v ev data o h2 h3) szdvd_string v enc off hwf henc hdata

/-! ### WF-conditioned dynamic fixed-array roundtrip -/
theorem decodeArrayElems_zero (dec : ByteArray → Nat → Except Error (ABIValue × Nat)) (isDyn : Bool) (data : ByteArray) (off : Nat) :
    decodeArrayElems dec isDyn 0 data off = Except.ok ([], off) := by
  unfold decodeArrayElems
  cases isDyn with
  | false => simp only [Bool.false_eq_true, if_false]; unfold decodeStaticElems decodeStaticElemsGo; simp
  | true => simp only [if_true]; unfold decodeDynamicElems decodeDynamicElemsGo; simp

theorem roundtrip_fixedArray_wf (n : Nat) (e : ABIType) (data : ByteArray)
    (hrt : ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 → encode e v = Except.ok ev →
      data.extract o (o + ev.size) = ev → decode e data o = Except.ok (v, o + ev.size))
    (hdvd : ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode e v = Except.ok ev → 32 ∣ ev.size)
    (v : ABIValue) (enc : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256)
    (henc : encode (.fixedArray n e) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.fixedArray n e) data off = Except.ok (v, off + enc.size) := by
  cases v with
  | array vals =>
    obtain ⟨encd, hEL', hlen, hpack⟩ := encode_fixedArray_inv n e vals enc henc
    have halign : ∀ b ∈ encd, 32 ∣ b.size :=
      encodeListElems_align e hdvd vals encd (isDynamic e) hEL' (by rw [← hpack]; exact hwf)
    unfold decode foldABIType
    delta instABIVisitorDecoderEntry
    dsimp
    cases hdyn : isDynamic e with
    | false =>
      have hpackc : enc = encd.foldl (·++·) ByteArray.empty := by rw [hpack, hdyn]; simp [arrayPack]
      simp only [decodeArrayElems, Bool.false_eq_true, if_false]
      rw [show n = vals.length from hlen.symm]
      rw [decodeStaticElems_concat_wf e data hrt vals encd off hEL'
            (by rw [← hpackc]; exact hwf) (by rw [← hpackc]; exact hdata)]
      rw [show off + (encd.foldl (·++·) ByteArray.empty).size = off + enc.size from by rw [← hpackc]]
      rfl
    | true =>
      by_cases hvemp : vals = []
      · subst hvemp
        simp only [encodeListElems, Except.ok.injEq] at hEL'; subst hEL'
        have hn0 : n = 0 := by simpa using hlen.symm
        subst hn0
        have hee : enc.size = 0 := by rw [hpack, hdyn, arrayPack_dyn]; simp [dynHeadsFrom]
        rw [decodeArrayElems_zero, show off + enc.size = off from by omega]
        rfl
      · have hpkT : enc = arrayPack true encd := by rw [hpack, hdyn]
        simp only [decodeArrayElems, if_true]
        rw [show n = vals.length from hlen.symm]
        rw [decodeDynamicElems_pack_wf e data hrt vals encd off hvemp hEL' halign
              (by rw [← hpkT]; exact hwf) (by rw [← hpkT]; exact hdata)]
        rw [show off + (arrayPack true encd).size = off + enc.size from by rw [hpkT]]
        rfl
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | tuple _ => badArrVal henc e

/-! ### General array szdvd + nested composition demo -/
-- general array szdvd, given element alignment
theorem szdvd_array (e : ABIType)
    (hdvd_e : ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode e v = Except.ok ev → 32 ∣ ev.size)
    (v : ABIValue) (ev : ByteArray) (hsz : ev.size < 2^256) (henc : encode (.array e) v = Except.ok ev) :
    32 ∣ ev.size := by
  cases v with
  | array vals =>
    obtain ⟨encd, hEL', hlt, hpack⟩ := encode_array_inv e vals ev henc
    have hPsz : (uint256ToBytes vals.length).size = 32 :=
      uint256ToBytes_size vals.length (natToBytes_size_bound vals.length hlt)
    have hencsz : ev.size = 32 + (arrayPack (isDynamic e) encd).size := by
      rw [hpack, ByteArray.size_append, hPsz]
    have halign : ∀ b ∈ encd, 32 ∣ b.size :=
      encodeListElems_align e hdvd_e vals encd (isDynamic e) hEL' (by omega)
    rw [hencsz]
    exact Nat.dvd_add (by norm_num) (arrayPack_size_dvd (isDynamic e) encd (by omega) halign)
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | tuple _ => badArrVal henc e

/-- Nested `bytes[][]` roundtrips under the bound — demonstrates the WF results compose. -/
theorem roundtrip_bytes_array_array_wf (v : ABIValue) (enc data : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256) (henc : encode (.array (.array .bytes)) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.array (.array .bytes)) data off = Except.ok (v, off + enc.size) :=
  roundtrip_array_wf (.array .bytes) data
    (fun v ev o hsz h2 h3 => roundtrip_bytes_array_wf v ev data o hsz h2 h3)
    (szdvd_array .bytes szdvd_bytes) v enc off hwf henc hdata
