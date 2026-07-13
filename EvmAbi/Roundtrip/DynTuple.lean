import EvmAbi.Roundtrip.DynArray

/-! WF-conditioned dynamic tuple roundtrip (decodeTupleDynamic / dtd_concat, roundtrip_tuple_wf), 32-byte alignment (szdvd_*), and the function-call (encodeArgs/decodeArgs) level. -/

open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode
set_option autoImplicit false

/-! ### Dynamic tuple groundwork: tuplePack fold characterization -/

def tupleHeadsFrom (off : Nat) : List (Bool × ByteArray) → List ByteArray
  | [] => []
  | (isDyn, enc) :: rest => (if isDyn then uint256ToBytes off else enc) :: tupleHeadsFrom (if isDyn then off + roundUp32 enc.size else off) rest

def tupleTails : List (Bool × ByteArray) → ByteArray
  | [] => ByteArray.empty
  | (isDyn, enc) :: rest => (if isDyn then enc else ByteArray.empty) ++ tupleTails rest

theorem tupleHeadsFrom_cons (off : Nat) (isDyn : Bool) (enc : ByteArray) (rest : List (Bool × ByteArray)) :
    tupleHeadsFrom off ((isDyn, enc) :: rest)
      = (if isDyn then uint256ToBytes off else enc) :: tupleHeadsFrom (if isDyn then off + roundUp32 enc.size else off) rest := rfl

abbrev tupleStep : Nat × ByteArray × ByteArray → Bool × ByteArray → Nat × ByteArray × ByteArray :=
  fun acc p => if p.1 then (acc.1 + roundUp32 p.2.size, acc.2.1 ++ uint256ToBytes acc.1, acc.2.2 ++ p.2)
               else (acc.1, acc.2.1 ++ p.2, acc.2.2)

theorem tupleStep_fold (encoded : List (Bool × ByteArray)) (startOff : Nat) (h0 t0 : ByteArray) :
    encoded.foldl tupleStep (startOff, h0, t0)
      = (encoded.foldl (fun o p => if p.1 then o + roundUp32 p.2.size else o) startOff,
         h0 ++ (tupleHeadsFrom startOff encoded).foldl (·++·) ByteArray.empty,
         t0 ++ tupleTails encoded) := by
  induction encoded generalizing startOff h0 t0 with
  | nil => simp [tupleHeadsFrom, tupleTails]
  | cons p rest ih =>
    obtain ⟨isDyn, enc⟩ := p
    cases isDyn with
    | true =>
      show rest.foldl tupleStep (startOff + roundUp32 enc.size, h0 ++ uint256ToBytes startOff, t0 ++ enc) = _
      rw [ih (startOff + roundUp32 enc.size) (h0 ++ uint256ToBytes startOff) (t0 ++ enc)]
      have ho : ((true, enc) :: rest).foldl (fun o p => if p.1 then o + roundUp32 p.2.size else o) startOff
              = rest.foldl (fun o p => if p.1 then o + roundUp32 p.2.size else o) (startOff + roundUp32 enc.size) := by simp [List.foldl_cons]
      have hh : (tupleHeadsFrom startOff ((true, enc) :: rest)).foldl (·++·) ByteArray.empty
              = uint256ToBytes startOff ++ (tupleHeadsFrom (startOff + roundUp32 enc.size) rest).foldl (·++·) ByteArray.empty := by
        rw [tupleHeadsFrom_cons]; simp only [↓reduceIte]; rw [ba_foldl_cons]
      have ht : tupleTails ((true, enc) :: rest) = enc ++ tupleTails rest := by rw [tupleTails]; simp
      rw [ho, hh, ht, ByteArray.append_assoc, ByteArray.append_assoc]
    | false =>
      show rest.foldl tupleStep (startOff, h0 ++ enc, t0) = _
      rw [ih startOff (h0 ++ enc) t0]
      have ho : ((false, enc) :: rest).foldl (fun o p => if p.1 then o + roundUp32 p.2.size else o) startOff
              = rest.foldl (fun o p => if p.1 then o + roundUp32 p.2.size else o) startOff := by simp [List.foldl_cons]
      have hh : (tupleHeadsFrom startOff ((false, enc) :: rest)).foldl (·++·) ByteArray.empty
              = enc ++ (tupleHeadsFrom startOff rest).foldl (·++·) ByteArray.empty := by
        rw [tupleHeadsFrom_cons]; simp only [Bool.false_eq_true, ↓reduceIte]; rw [ba_foldl_cons]
      have ht : tupleTails ((false, enc) :: rest) = tupleTails rest := by rw [tupleTails]; simp
      rw [ho, hh, ht, ByteArray.append_assoc]

/-- `tuplePack` for a dynamic tuple is the interleaved head region followed by the dynamic tails. -/
theorem tuplePack_dyn (headSizes : List Nat) (dynamics : List Bool) (encoded : List (Bool × ByteArray))
    (hd : dynamics.any id = true) :
    tuplePack headSizes dynamics encoded
      = (tupleHeadsFrom (headSizes.foldl (·+·) 0) encoded).foldl (·++·) ByteArray.empty ++ tupleTails encoded := by
  unfold tuplePack
  simp only [hd, Bool.not_true, Bool.false_eq_true, if_false]
  rw [show (List.foldl tupleStep (headSizes.foldl (·+·) 0, ByteArray.empty, ByteArray.empty) encoded)
        = _ from tupleStep_fold encoded _ ByteArray.empty ByteArray.empty]
  simp [ByteArray.empty_append]

/-! ### Dynamic tuple decode (decodeTupleDynamic) -/
theorem headSize_dynamic (t : ABIType) (h : isDynamic t = true) : headSize t = 32 := by
  unfold headSize
  rw [h]
  rfl

theorem foldl_add_eq_sum_map (l : List ABIType) (f : ABIType → Nat) :
    l.foldl (fun a t => a + f t) 0 = (l.map f).sum := by
  simp [List.foldl_map, List.sum_eq_foldl]

theorem headSize_mem_le (l : List ABIType) (t : ABIType) (h : t ∈ l) :
    headSize t ≤ l.foldl (fun a t => a + headSize t) 0 := by
  simpa [foldl_add_eq_sum_map] using List.le_sum_of_mem (List.mem_map_of_mem (f := headSize) h)

theorem foldl_append_ge (processed ts : List ABIType) :
    processed.foldl (fun a t => a + headSize t) 0 ≤ (processed ++ ts).foldl (fun a t => a + headSize t) 0 := by
  rw [List.foldl_append, headSize_foldl_shift _ ts]; omega

theorem foldl_snoc (processed : List ABIType) (t : ABIType) :
    (processed ++ [t]).foldl (fun a t => a + headSize t) 0 = processed.foldl (fun a t => a + headSize t) 0 + headSize t := by
  rw [List.foldl_append]; simp only [List.foldl_cons, List.foldl_nil]

theorem tupleTails_dyn (b : ByteArray) (tail : List (Bool × ByteArray)) :
    tupleTails ((true, b) :: tail) = b ++ tupleTails tail := by rw [tupleTails]; simp
theorem tupleTails_stat (b : ByteArray) (tail : List (Bool × ByteArray)) :
    tupleTails ((false, b) :: tail) = tupleTails tail := by rw [tupleTails]; simp
theorem tupleHeadsFrom_stat (off : Nat) (b : ByteArray) (tail : List (Bool × ByteArray)) :
    tupleHeadsFrom off ((false, b) :: tail) = b :: tupleHeadsFrom off tail := by rw [tupleHeadsFrom]; simp
theorem tupleHeadsFrom_dyn (off : Nat) (b : ByteArray) (tail : List (Bool × ByteArray)) :
    tupleHeadsFrom off ((true, b) :: tail) = uint256ToBytes off :: tupleHeadsFrom (off + roundUp32 b.size) tail := by rw [tupleHeadsFrom]; simp

theorem dtd_nil (fullTs : List ABIType) (data : ByteArray) (offset i : Nat) (acc : List ABIValue) (maxEnd : Nat) :
    decodeTupleDynamic (All.nil : All DecoderEntry []) fullTs [] data offset i acc maxEnd = Except.ok (acc.reverse, maxEnd) := rfl

theorem dtd_cons {t : ABIType} {ts'' : List ABIType} (dec' : DecoderEntry t) (rest : All DecoderEntry ts'')
    (fullTs : List ABIType) (data : ByteArray) (offset i : Nat) (acc : List ABIValue) (maxEnd : Nat) :
    decodeTupleDynamic (All.cons dec' rest) fullTs (t :: ts'') data offset i acc maxEnd
      = (let headOff := offset + (fullTs.take i).foldl (fun acc t => acc + headSize t) 0
         if headOff + 32 > data.size then .error (.dataTooShortForHead headOff)
         else if isDynamic t then
           (dec' data (offset + bytesToNat (data.extract headOff (headOff + 32))) >>= fun x =>
             decodeTupleDynamic rest fullTs ts'' data offset (i + 1) (x.1 :: acc) (max maxEnd x.2))
         else
           (dec' data headOff >>= fun x =>
             decodeTupleDynamic rest fullTs ts'' data offset (i + 1) (x.1 :: acc) maxEnd)) := rfl

theorem dtd_concat (fullTs : List ABIType) (data : ByteArray) (offset : Nat)
    (hbd : offset + fullTs.foldl (fun a t => a + headSize t) 0 + 32 ≤ data.size)
    (hrt : ∀ t ∈ fullTs, ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 →
      encode t v = Except.ok ev → data.extract o (o + ev.size) = ev → decode t data o = Except.ok (v, o + ev.size))
    (hsize : ∀ t ∈ fullTs, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdvd : ∀ t ∈ fullTs, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size)
    (hHA : fullTs.foldl (fun a t => a + headSize t) 0 < 2^256) :
    ∀ (processed ts : List ABIType) (vs : List ABIValue) (encoded : List (Bool × ByteArray))
      (tailCur maxEnd : Nat) (acc : List ABIValue),
      fullTs = processed ++ ts →
      instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encoded →
      maxEnd = offset + tailCur →
      tailCur + (tupleTails encoded).size < 2^256 →
      data.extract (offset + processed.foldl (fun a t => a + headSize t) 0)
        (offset + processed.foldl (fun a t => a + headSize t) 0 + ((tupleHeadsFrom tailCur encoded).foldl (·++·) ByteArray.empty).size)
        = (tupleHeadsFrom tailCur encoded).foldl (·++·) ByteArray.empty →
      data.extract (offset + tailCur) (offset + tailCur + (tupleTails encoded).size) = tupleTails encoded →
      decodeTupleDynamic (foldAll DecoderEntry ts) fullTs ts data offset processed.length acc maxEnd
        = Except.ok (acc.reverse ++ vs, offset + tailCur + (tupleTails encoded).size) := by
  intro processed ts
  induction ts generalizing processed with
  | nil =>
    intro vs encoded tailCur maxEnd acc hsplit hgo hmax _ _ _
    obtain ⟨rfl, rfl⟩ := go_nil_inv vs encoded hgo
    simp only [foldAll, tupleTails, ByteArray.size_empty, Nat.add_zero, List.append_nil]
    rw [dtd_nil, hmax]
  | cons t ts' ih =>
    intro vs encoded tailCur maxEnd acc hsplit hgo hmax htbound hheads htails
    have hmemt : t ∈ fullTs := by rw [hsplit]; simp
    obtain ⟨v, vs', b, tail, rfl, hb_enc, htail, rfl⟩ := go_cons_inv t ts' vs encoded hgo
    -- head offset
    have hhp : (fullTs.take processed.length).foldl (fun acc t => acc + headSize t) 0 = processed.foldl (fun acc t => acc + headSize t) 0 := by
      rw [hsplit, List.take_left]
    have hhp_le : processed.foldl (fun a t => a + headSize t) 0 ≤ fullTs.foldl (fun a t => a + headSize t) 0 := by
      rw [hsplit]; exact foldl_append_ge processed (t :: ts')
    rw [foldAll]
    rw [dtd_cons]
    simp only [hhp]
    have hheadle : ¬ (offset + processed.foldl (fun a t => a + headSize t) 0 + 32 > data.size) := by omega
    rw [if_neg hheadle]
    set hp := processed.foldl (fun a t => a + headSize t) 0 with hpdef
    have hlen1 : processed.length + 1 = (processed ++ [t]).length := by simp
    have hpsnoc : (processed ++ [t]).foldl (fun a t => a + headSize t) 0 = hp + headSize t := by rw [hpdef]; exact foldl_snoc processed t
    have hsplit' : fullTs = (processed ++ [t]) ++ ts' := by rw [hsplit]; simp
    cases hd : isDynamic t with
    | false =>
      rw [hd] at htbound hheads htails
      rw [tupleHeadsFrom_stat, ba_foldl_cons] at hheads
      have hbeq : b.size = headSize t := hsize t hmemt hd v b hb_enc
      have hb_lt : b.size < 2^256 := by have := headSize_mem_le fullTs t hmemt; omega
      set P := (tupleHeadsFrom tailCur tail).foldl (·++·) ByteArray.empty with hPdef
      have hchunk := extract_append_left_of_slice data (offset + hp) b P hheads
      have hslice_suffix := extract_append_right_of_slice data (offset + hp) b P hheads
      have hdec : (foldABIType DecoderEntry t) data (offset + hp) = Except.ok (v, offset + hp + b.size) := hrt t hmemt v b _ hb_lt hb_enc hchunk
      rw [hdec]
      show decodeTupleDynamic (foldAll DecoderEntry ts') fullTs ts' data offset (processed.length + 1) (v :: acc) maxEnd = _
      rw [hlen1]
      have hheads' : data.extract (offset + (processed ++ [t]).foldl (fun a t => a + headSize t) 0) (offset + (processed ++ [t]).foldl (fun a t => a + headSize t) 0 + P.size) = P := by
        rw [show offset + (processed ++ [t]).foldl (fun a t => a + headSize t) 0 = offset + hp + b.size from by rw [hpsnoc]; omega]; exact hslice_suffix
      have htails' : data.extract (offset + tailCur) (offset + tailCur + (tupleTails tail).size) = tupleTails tail := by rw [← tupleTails_stat b]; exact htails
      rw [ih (processed ++ [t]) vs' tail tailCur maxEnd (v :: acc) hsplit' htail hmax (by rw [tupleTails_stat] at htbound; exact htbound) hheads' htails']
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append, tupleTails_stat]
    | true =>
      rw [hd] at htbound hheads htails
      rw [tupleTails_dyn] at htails htbound
      have htc_lt : tailCur < 2^256 := by rw [ByteArray.size_append] at htbound; omega
      have hb_lt : b.size < 2^256 := by rw [ByteArray.size_append] at htbound; omega
      have hru : roundUp32 b.size = b.size := roundUp32_eq_of_dvd b.size (hdvd t hmemt v b hb_lt hb_enc)
      have hP32 : (uint256ToBytes tailCur).size = 32 := uint256ToBytes_size32 tailCur htc_lt
      rw [tupleHeadsFrom_dyn, hru, ba_foldl_cons] at hheads
      set P := (tupleHeadsFrom (tailCur + b.size) tail).foldl (·++·) ByteArray.empty with hPdef
      have hchunk := extract_head32 data (offset + hp) (offset + hp + (uint256ToBytes tailCur ++ P).size)
        (uint256ToBytes tailCur) P hP32 (by rw [ByteArray.size_append, hP32]; omega) hheads
      have htchunk := extract_append_left_of_slice data (offset + tailCur) b (tupleTails tail) htails
      have hslice_suffix := extract_tail_after32 data (offset + hp) (offset + hp + (uint256ToBytes tailCur ++ P).size)
        (uint256ToBytes tailCur) P hP32 (by rw [ByteArray.size_append, hP32]; omega) hheads
      have htslice_suffix : data.extract (offset + (tailCur + b.size)) (offset + (tailCur + b.size) + (tupleTails tail).size) = tupleTails tail := by
        rw [show offset + (tailCur + b.size) = offset + tailCur + b.size from by omega]
        exact extract_append_right_of_slice data (offset + tailCur) b (tupleTails tail) htails
      rw [hchunk, bytesToNat_uint256ToBytes]
      have hdec : (foldABIType DecoderEntry t) data (offset + tailCur) = Except.ok (v, offset + tailCur + b.size) := hrt t hmemt v b _ hb_lt hb_enc htchunk
      rw [hdec]
      show decodeTupleDynamic (foldAll DecoderEntry ts') fullTs ts' data offset (processed.length + 1) (v :: acc) (max maxEnd (offset + tailCur + b.size)) = _
      rw [hlen1, show max maxEnd (offset + tailCur + b.size) = offset + (tailCur + b.size) from by rw [hmax]; omega]
      have hheads' : data.extract (offset + (processed ++ [t]).foldl (fun a t => a + headSize t) 0) (offset + (processed ++ [t]).foldl (fun a t => a + headSize t) 0 + P.size) = P := by
        rw [show offset + (processed ++ [t]).foldl (fun a t => a + headSize t) 0 = offset + hp + 32 from by rw [hpsnoc]; have := headSize_dynamic t hd; omega]; exact hslice_suffix
      rw [ih (processed ++ [t]) vs' tail (tailCur + b.size) (offset + (tailCur + b.size)) (v :: acc) hsplit' htail rfl (by rw [ByteArray.size_append] at htbound; omega) hheads' htslice_suffix]
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append, tupleTails_dyn, ByteArray.size_append]
      grind

/-! ### Dynamic tuple roundtrip under the well-formedness bound `enc.size < 2 ^ 256` -/

theorem tupleHeadsFrom_size (ts : List ABIType)
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdvd : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size) :
    ∀ (vs : List ABIValue) (encoded : List (Bool × ByteArray)) (off : Nat),
      instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encoded →
      off + (tupleTails encoded).size < 2^256 →
      ((tupleHeadsFrom off encoded).foldl (·++·) ByteArray.empty).size = ts.foldl (fun a t => a + headSize t) 0 := by
  induction ts with
  | nil =>
    intro vs encoded off hgo _
    obtain ⟨rfl, rfl⟩ := go_nil_inv vs encoded hgo
    simp [tupleHeadsFrom]
  | cons t ts' ih =>
    intro vs encoded off hgo hbnd
    have hmemt : t ∈ (t :: ts') := by simp
    obtain ⟨v, vs', b, tail, rfl, hb_enc, htail, rfl⟩ := go_cons_inv t ts' vs encoded hgo
    have ihs : ∀ t' ∈ ts', isDynamic t' = false → ∀ (v : ABIValue) (ev : ByteArray), encode t' v = Except.ok ev → ev.size = headSize t' := fun t' ht' => hsize t' (by simp [ht'])
    have ihd : ∀ t' ∈ ts', ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t' v = Except.ok ev → 32 ∣ ev.size := fun t' ht' => hdvd t' (by simp [ht'])
    cases hd : isDynamic t with
    | false =>
      rw [hd] at hbnd
      have hbeq : b.size = headSize t := hsize t hmemt hd v b hb_enc
      rw [tupleHeadsFrom_stat, ba_foldl_cons, ByteArray.size_append,
          ih ihs ihd vs' tail off htail (by rw [tupleTails_stat] at hbnd; exact hbnd),
          List.foldl_cons, headSize_foldl_shift (0 + headSize t) ts']
      omega
    | true =>
      rw [hd, tupleTails_dyn] at hbnd
      have hbnd2 : off + b.size + (tupleTails tail).size < 2^256 := by rw [ByteArray.size_append] at hbnd; omega
      have hoff_lt : off < 2^256 := by omega
      have hb_lt : b.size < 2^256 := by omega
      have hru : roundUp32 b.size = b.size := roundUp32_eq_of_dvd b.size (hdvd t hmemt v b hb_lt hb_enc)
      have hP32 : (uint256ToBytes off).size = 32 := uint256ToBytes_size32 off hoff_lt
      rw [tupleHeadsFrom_dyn, hru, ba_foldl_cons, ByteArray.size_append, hP32,
          ih ihs ihd vs' tail (off + b.size) htail (by omega),
          List.foldl_cons, headSize_foldl_shift (0 + headSize t) ts', headSize_dynamic t hd]

theorem tupleHeadsFrom_size_ge (ts : List ABIType)
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t) :
    ∀ (vs : List ABIValue) (encoded : List (Bool × ByteArray)) (off : Nat),
      instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encoded →
      ts.foldl (fun a t => a + headSize t) 0 ≤ ((tupleHeadsFrom off encoded).foldl (·++·) ByteArray.empty).size := by
  induction ts with
  | nil => intro vs encoded off hgo; simp
  | cons t ts' ih =>
    intro vs encoded off hgo
    have hmemt : t ∈ (t :: ts') := by simp
    obtain ⟨v, vs', b, tail, rfl, hb_enc, htail, rfl⟩ := go_cons_inv t ts' vs encoded hgo
    have ihs : ∀ t' ∈ ts', isDynamic t' = false → ∀ (v : ABIValue) (ev : ByteArray), encode t' v = Except.ok ev → ev.size = headSize t' := fun t' ht' => hsize t' (by simp [ht'])
    rw [List.foldl_cons, headSize_foldl_shift (0 + headSize t) ts']
    cases hd : isDynamic t with
    | false =>
      have hbeq : b.size = headSize t := hsize t hmemt hd v b hb_enc
      rw [tupleHeadsFrom_stat, ba_foldl_cons, ByteArray.size_append]
      have := ih ihs vs' tail off htail; omega
    | true =>
      rw [tupleHeadsFrom_dyn, ba_foldl_cons, ByteArray.size_append]
      have hge := uint256ToBytes_size_ge off
      have := ih ihs vs' tail (off + roundUp32 b.size) htail
      have h32 : headSize t = 32 := headSize_dynamic t hd
      omega


/-- Step lemma for the dynamic-tuple roundtrip: decoding the `tuplePack` region (interleaved
head area ++ tails, dynamic case) at `off` recovers the field values. Packages the heads/tails
split, the head-area sizing, and the `dtd_concat` induction — the tuple counterpart of
`decodeDynamicElems_pack_wf`. -/
theorem decodeTupleDynamic_pack_wf (ts : List ABIType) (data : ByteArray)
    (hrt : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 →
      encode t v = Except.ok ev → data.extract o (o + ev.size) = ev → decode t data o = Except.ok (v, o + ev.size))
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdvd : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size)
    (vs : List ABIValue) (encd : List (Bool × ByteArray)) (off : Nat)
    (hgo : instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd)
    (hany : (ts.map isDynamic).any id = true)
    (hsz : (tuplePack (ts.map headSize) (ts.map isDynamic) encd).size < 2^256)
    (hbd : off + ts.foldl (fun a t => a + headSize t) 0 + 32 ≤ data.size)
    (hslice : data.extract off (off + (tuplePack (ts.map headSize) (ts.map isDynamic) encd).size)
              = tuplePack (ts.map headSize) (ts.map isDynamic) encd) :
    decodeTupleDynamic (foldAll DecoderEntry ts) ts ts data off 0 []
        (off + ts.foldl (fun a t => a + headSize t) 0)
      = Except.ok (vs, off + (tuplePack (ts.map headSize) (ts.map isDynamic) encd).size) := by
  set HA := ts.foldl (fun a t => a + headSize t) 0 with hHAdef
  have hHAeq : (ts.map headSize).foldl (· + ·) 0 = HA := by rw [hHAdef, List.foldl_map]
  set heads := (tupleHeadsFrom HA encd).foldl (·++·) ByteArray.empty with hh
  set tails := tupleTails encd with ht
  have hpackht : tuplePack (ts.map headSize) (ts.map isDynamic) encd = heads ++ tails := by
    rw [tuplePack_dyn _ _ _ hany, hHAeq]
  have hpsz : (tuplePack (ts.map headSize) (ts.map isDynamic) encd).size = heads.size + tails.size := by
    rw [hpackht, ByteArray.size_append]
  have hge : HA ≤ heads.size := by rw [hh]; exact tupleHeadsFrom_size_ge ts hsize vs encd HA hgo
  have htb : HA + tails.size < 2^256 := by omega
  have hheadsz : heads.size = HA := by
    rw [hh]; exact tupleHeadsFrom_size ts hsize hdvd vs encd HA hgo (by rw [← ht]; omega)
  have hslice_all : data.extract off (off + (heads ++ tails).size) = heads ++ tails := by
    rw [← hpackht]; exact hslice
  have hslice_heads := extract_append_left_of_slice data off heads tails hslice_all
  have hslice_tails := extract_append_right_of_slice data off heads tails hslice_all
  have hdc := dtd_concat ts data off hbd hrt hsize hdvd (by omega) [] ts vs encd HA (off + HA) [] rfl hgo rfl (by rw [← ht]; omega)
    (by simpa [List.foldl_nil, Nat.add_zero] using hslice_heads)
    (by simpa [hheadsz] using hslice_tails)
  simp only [List.length_nil, List.reverse_nil, List.nil_append] at hdc
  rw [hdc, show off + HA + (tupleTails encd).size
        = off + (tuplePack (ts.map headSize) (ts.map isDynamic) encd).size from by rw [← ht]; omega]

theorem roundtrip_tuple_dyn_wf (ts : List ABIType) (data : ByteArray)
    (hrt : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 →
      encode t v = Except.ok ev → data.extract o (o + ev.size) = ev → decode t data o = Except.ok (v, o + ev.size))
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdvd : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size)
    (hdyn : ts.any isDynamic = true)
    (v : ABIValue) (enc : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256)
    (hbd : off + ts.foldl (fun a t => a + headSize t) 0 + 32 ≤ data.size)
    (henc : encode (.tuple ts) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.tuple ts) data off = Except.ok (v, off + enc.size) := by
  cases v with
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | array _ => badVal henc
  | tuple vs =>
    obtain ⟨encd, hgo, hpack⟩ := encode_tuple_inv ts vs enc henc
    have hany : (ts.map isDynamic).any id = true := by simpa using hdyn
    have hdc := decodeTupleDynamic_pack_wf ts data hrt hsize hdvd vs encd off hgo hany
      (by rw [← hpack]; exact hwf) hbd (by rw [← hpack]; exact hdata)
    openDec
    rw [hdyn]
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    rw [hdc]
    rw [show off + (tuplePack (ts.map headSize) (ts.map isDynamic) encd).size = off + enc.size from by rw [hpack]]
    rfl

/-! ### Tuple encoding is 32-byte aligned (szdvd_tuple), for composing tuples as fields/elements -/

theorem headSize_dvd_32 : (t : ABIType) → 32 ∣ headSize t
  | .uint _ => by simp [headSize, isDynamic]
  | .int _ => by simp [headSize, isDynamic]
  | .bool => by simp [headSize, isDynamic]
  | .address => by simp [headSize, isDynamic]
  | .bytes => by simp [headSize, isDynamic]
  | .fixedBytes _ => by simp [headSize, isDynamic]
  | .string => by simp [headSize, isDynamic]
  | .array _ => by simp [headSize, isDynamic]
  | .fixedArray n e => by
      rw [headSize]; split
      · rfl
      · exact (headSize_dvd_32 e).mul_left n
  | .tuple ts => by
      rw [headSize]; split
      · rfl
      · have h : ∀ n ∈ ts.map headSize, 32 ∣ n := by
          intro n hn
          obtain ⟨t, ht, h_eq⟩ := List.mem_map.mp hn
          rw [← h_eq]
          exact headSize_dvd_32 t
        exact List.dvd_sum h
  termination_by t => sizeOf t

theorem foldl_headSize_dvd : ∀ (ts : List ABIType) (init : Nat), 32 ∣ init →
    32 ∣ ts.foldl (fun a t => a + headSize t) init
  | [], init, h => h
  | t :: ts, init, h => by
      rw [List.foldl_cons]; exact foldl_headSize_dvd ts (init + headSize t) (Nat.dvd_add h (headSize_dvd_32 t))

theorem concat_pairs_dvd : ∀ (encd : List (Bool × ByteArray)), (∀ b ∈ encd, 32 ∣ b.2.size) →
    32 ∣ (encd.foldl (fun acc x => acc ++ x.2) ByteArray.empty).size := by
  intro encd
  suffices h : ∀ (acc : ByteArray), 32 ∣ acc.size → (∀ b ∈ encd, 32 ∣ b.2.size) →
      32 ∣ (encd.foldl (fun acc x => acc ++ x.2) acc).size by
    intro hall; exact h ByteArray.empty (by simp) hall
  induction encd with
  | nil => intro acc hacc _; exact hacc
  | cons x xs ih =>
    intro acc hacc hall
    rw [List.foldl_cons]
    exact ih (acc ++ x.2) (by rw [ByteArray.size_append]; exact Nat.dvd_add hacc (hall x (by simp)))
      (fun b hb => hall b (List.mem_cons_of_mem _ hb))

theorem tupleTails_size_dvd : ∀ (encd : List (Bool × ByteArray)), (∀ b ∈ encd, b.1 = true → 32 ∣ b.2.size) →
    32 ∣ (tupleTails encd).size := by
  intro encd
  induction encd with
  | nil => intro _; simp [tupleTails]
  | cons x xs ih =>
    intro hall
    obtain ⟨isDyn, enc⟩ := x
    rw [tupleTails, ByteArray.size_append]
    refine Nat.dvd_add ?_ (ih (fun b hb => hall b (List.mem_cons_of_mem _ hb)))
    cases isDyn with
    | true => simpa using hall (true, enc) (by simp) rfl
    | false => simp

theorem tupleTails_mem_le : ∀ (encd : List (Bool × ByteArray)) (b : Bool × ByteArray),
    b ∈ encd → b.1 = true → b.2.size ≤ (tupleTails encd).size := by
  intro encd
  induction encd with
  | nil => intro b hb _; simp at hb
  | cons x xs ih =>
    obtain ⟨d, e⟩ := x
    intro b hb hdyn
    rw [tupleTails, ByteArray.size_append]
    rcases List.mem_cons.mp hb with h | h
    · subst h
      have hd : d = true := hdyn
      rw [hd]; simp only [if_true]; omega
    · exact le_trans (ih b h hdyn) (by omega)

-- static tuple: every encoded field is 32-aligned (size = headSize, structurally divisible)
theorem tuple_entries_static_dvd (ts : List ABIType)
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t) :
    ∀ (vs : List ABIValue) (encd : List (Bool × ByteArray)),
      instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd →
      (∀ t ∈ ts, isDynamic t = false) → ∀ b ∈ encd, 32 ∣ b.2.size := by
  induction ts with
  | nil =>
    intro vs encd hgo _ b hb
    obtain ⟨rfl, rfl⟩ := go_nil_inv vs encd hgo
    simp at hb
  | cons t ts' ih =>
    intro vs encd hgo hstat b hb
    have hmemt : t ∈ (t :: ts') := by simp
    obtain ⟨v, vs', b0, tail, rfl, hb_enc, htail, rfl⟩ := go_cons_inv t ts' vs encd hgo
    have hstat_t : isDynamic t = false := hstat t hmemt
    have hb0sz : b0.size = headSize t := hsize t hmemt hstat_t v b0 hb_enc
    rcases List.mem_cons.mp hb with h | h
    · subst h; rw [hb0sz]; exact headSize_dvd_32 t
    · exact ih (fun t' ht' => hsize t' (by simp [ht'])) vs' tail htail (fun t' ht' => hstat t' (by simp [ht'])) b h

-- dynamic tuple: every dynamic encoded field is 32-aligned (via hdvd, under size bound)
theorem tuple_entries_dyn_dvd (ts : List ABIType)
    (hdvd : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size) :
    ∀ (vs : List ABIValue) (encd : List (Bool × ByteArray)),
      instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd →
      (∀ b ∈ encd, b.1 = true → b.2.size < 2^256) → ∀ b ∈ encd, b.1 = true → 32 ∣ b.2.size := by
  induction ts with
  | nil =>
    intro vs encd hgo _ b hb
    obtain ⟨rfl, rfl⟩ := go_nil_inv vs encd hgo
    simp at hb
  | cons t ts' ih =>
    intro vs encd hgo hbnd b hb hdynb
    have hmemt : t ∈ (t :: ts') := by simp
    obtain ⟨v, vs', b0, tail, rfl, hb_enc, htail, rfl⟩ := go_cons_inv t ts' vs encd hgo
    rcases List.mem_cons.mp hb with h | h
    · subst h
      exact hdvd t hmemt v b0 (hbnd (isDynamic t, b0) (by simp) hdynb) hb_enc
    · exact ih (fun t' ht' => hdvd t' (by simp [ht'])) vs' tail htail
        (fun b' hb' => hbnd b' (List.mem_cons_of_mem _ hb')) b h hdynb

-- 32-alignment of any tuple encoding, under the well-formedness bound
theorem szdvd_tuple (ts : List ABIType)
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdvd : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size)
    (v : ABIValue) (ev : ByteArray) (hsz : ev.size < 2^256) (henc : encode (.tuple ts) v = Except.ok ev) :
    32 ∣ ev.size := by
  cases v with
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | array _ => badVal henc
  | tuple vs =>
    obtain ⟨encd, hgo, hpack⟩ := encode_tuple_inv ts vs ev henc
    cases hdynb : (ts.map isDynamic).any id with
    | false =>
      rw [hpack, tuplePack_static _ _ _ hdynb]
      have hallstat : ∀ t ∈ ts, isDynamic t = false :=
        tuple_static_elems ts (by rw [← tuple_any_isDynamic ts]; exact hdynb)
      exact concat_pairs_dvd encd (tuple_entries_static_dvd ts hsize vs encd hgo hallstat)
    | true =>
      have hHAeq : (ts.map headSize).foldl (· + ·) 0 = ts.foldl (fun a t => a + headSize t) 0 := by
        rw [List.foldl_map]
      have hpackht : ev = (tupleHeadsFrom (ts.foldl (fun a t => a + headSize t) 0) encd).foldl (·++·) ByteArray.empty ++ tupleTails encd := by
        rw [hpack, tuplePack_dyn _ _ _ hdynb, hHAeq]
      have hpsz : ev.size = ((tupleHeadsFrom (ts.foldl (fun a t => a + headSize t) 0) encd).foldl (·++·) ByteArray.empty).size + (tupleTails encd).size := by
        rw [hpackht, ByteArray.size_append]
      have hge : ts.foldl (fun a t => a + headSize t) 0 ≤ ((tupleHeadsFrom (ts.foldl (fun a t => a + headSize t) 0) encd).foldl (·++·) ByteArray.empty).size :=
        tupleHeadsFrom_size_ge ts hsize vs encd _ hgo
      have hheadsz : ((tupleHeadsFrom (ts.foldl (fun a t => a + headSize t) 0) encd).foldl (·++·) ByteArray.empty).size = ts.foldl (fun a t => a + headSize t) 0 :=
        tupleHeadsFrom_size ts hsize hdvd vs encd _ hgo (by omega)
      have hbnd_dyn : ∀ b ∈ encd, b.1 = true → b.2.size < 2^256 := by
        intro b hb hd
        have := tupleTails_mem_le encd b hb hd
        omega
      have htails : 32 ∣ (tupleTails encd).size :=
        tupleTails_size_dvd encd (tuple_entries_dyn_dvd ts hdvd vs encd hgo hbnd_dyn)
      have hheads : 32 ∣ ((tupleHeadsFrom (ts.foldl (fun a t => a + headSize t) 0) encd).foldl (·++·) ByteArray.empty).size := by
        rw [hheadsz]; exact foldl_headSize_dvd ts 0 (by simp)
      rw [hpsz]; exact Nat.dvd_add hheads htails

/-! ### Unified tuple roundtrip under WF (static + dynamic dispatch) -/


theorem decodeTupleStatic_concat_wf (ts : List ABIType) (data : ByteArray)
    (hrt : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 →
      encode t v = Except.ok ev → data.extract o (o + ev.size) = ev → decode t data o = Except.ok (v, o + ev.size)) :
    ∀ (vs : List ABIValue) (encd : List (Bool × ByteArray)) (off : Nat) (acc : List ABIValue),
    instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd →
    (encd.foldl (fun a x => a ++ x.2) ByteArray.empty).size < 2^256 →
    data.extract off (off + (encd.foldl (fun a x => a ++ x.2) ByteArray.empty).size) = encd.foldl (fun a x => a ++ x.2) ByteArray.empty →
    decodeTupleStatic (foldAll DecoderEntry ts) data off acc = Except.ok (acc.reverse ++ vs, off + (encd.foldl (fun a x => a ++ x.2) ByteArray.empty).size) := by
  induction ts with
  | nil =>
    intro vs encd off acc hgo _ hslice
    obtain ⟨rfl, rfl⟩ := go_nil_inv vs encd hgo
    simp only [foldAll, List.foldl_nil, ByteArray.size_empty, Nat.add_zero, List.append_nil]
    rw [decodeTupleStatic_nil]
  | cons t ts' ih =>
    intro vs encd off acc hgo hbound hslice
    have hmemt : t ∈ (t :: ts') := by simp
    obtain ⟨v, vs', b, tail, rfl, hb_enc, htail, rfl⟩ := go_cons_inv t ts' vs encd hgo
    rw [ba_foldl_snd_cons] at hslice hbound ⊢
    simp only [] at hslice hbound ⊢
    -- freeze the tail fold to an atom so the generic slice helpers unify without
    -- whnf-ing the `fun a x => a ++ x.2` fold (which otherwise blows the heartbeat budget)
    set tl := tail.foldl (fun a x => a ++ x.2) ByteArray.empty with htl
    have hb_lt : b.size < 2^256 := by rw [ByteArray.size_append] at hbound; omega
    have hbound' : tl.size < 2^256 := by rw [ByteArray.size_append] at hbound; omega
    have hslice_b := extract_append_left_of_slice data off b tl hslice
    have hslice_tail := extract_append_right_of_slice data off b tl hslice
    have hdec_t : (foldABIType DecoderEntry t) data off = Except.ok (v, off + b.size) :=
      hrt t hmemt v b off hb_lt hb_enc hslice_b
    simp only [foldAll]
    rw [decodeTupleStatic_cons, hdec_t]
    show decodeTupleStatic (foldAll DecoderEntry ts') data (off + b.size) (v :: acc) = _
    rw [ih (fun t' ht' => hrt t' (List.mem_cons_of_mem t ht')) vs' tail (off + b.size) (v :: acc) htail hbound' hslice_tail]
    simp [add_assoc, ByteArray.size_append, htl]

-- static-tuple concat size = headSize (.tuple ts), from per-field size_eq (WF variant, no visitor)
theorem tuplePackStatic_size_wf (ts : List ABIType)
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hstat : ∀ t ∈ ts, isDynamic t = false) :
    ∀ (vs : List ABIValue) (encd : List (Bool × ByteArray)),
    instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd →
    (encd.foldl (fun acc x => acc ++ x.2) ByteArray.empty).size = headSize (.tuple ts) := by
  induction ts with
  | nil =>
    intro vs encd hgo
    obtain ⟨rfl, rfl⟩ := go_nil_inv vs encd hgo
    simp [headSize, isDynamic]
  | cons t ts' ih =>
    intro vs encd hgo
    obtain ⟨v, vs', b, tail, rfl, hb_enc, htail, rfl⟩ := go_cons_inv t ts' vs encd hgo
    rw [ba_foldl_snd_cons, ByteArray.size_append,
        hsize t (by simp) (hstat t (by simp)) v b hb_enc,
        ih (fun t' ht' => hsize t' (by simp [ht'])) (fun t' ht' => hstat t' (List.mem_cons_of_mem t ht')) vs' tail htail,
        headSize_tuple_cons t ts' (isDynamic_tuple_of_all_static (t :: ts') hstat)]

-- static tuple roundtrip under WF (per-field bounded rt + size_eq)
theorem roundtrip_tuple_stat_wf (ts : List ABIType) (data : ByteArray)
    (hrt : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 →
      encode t v = Except.ok ev → data.extract o (o + ev.size) = ev → decode t data o = Except.ok (v, o + ev.size))
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hstat_tuple : isDynamic (.tuple ts) = false)
    (v : ABIValue) (enc : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256)
    (henc : encode (.tuple ts) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.tuple ts) data off = Except.ok (v, off + enc.size) := by
  have hany : (ts.map isDynamic).any id = false := by rw [tuple_any_isDynamic]; exact hstat_tuple
  have hany_ts : ts.any isDynamic = false := by simpa [List.any_map] using hany
  have hstat_all : ∀ t ∈ ts, isDynamic t = false := tuple_static_elems ts hstat_tuple
  cases v with
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | array _ => badVal henc
  | tuple vs =>
    obtain ⟨encd, hgo, hpack⟩ := encode_tuple_inv ts vs enc henc
    have hconcat : enc = encd.foldl (fun a x => a ++ x.2) ByteArray.empty := by rw [hpack, tuplePack_static _ _ _ hany]
    have hsize_eq : enc.size = headSize (.tuple ts) := by rw [hconcat]; exact tuplePackStatic_size_wf ts hsize hstat_all vs encd hgo
    have hoff : ts.foldl (fun acc t => acc + headSize t) 0 = enc.size := by rw [hsize_eq]; exact headSize_tuple_foldl ts hstat_tuple
    have hslice : data.extract off (off + (encd.foldl (fun a x => a ++ x.2) ByteArray.empty).size) = encd.foldl (fun a x => a ++ x.2) ByteArray.empty := by rw [← hconcat]; exact hdata
    openDec
    rw [hany_ts]
    simp only [Bool.not_false, if_true]
    rw [decodeTupleStatic_concat_wf ts data hrt vs encd off [] hgo (by rw [← hconcat]; exact hwf) hslice]
    show Except.ok (ABIValue.tuple ([].reverse ++ vs), off + ts.foldl (fun acc t => acc + headSize t) 0) = Except.ok (ABIValue.tuple vs, off + enc.size)
    simp only [List.reverse_nil, List.nil_append, hoff]

-- unified tuple roundtrip under WF: dispatch static/dynamic
theorem roundtrip_tuple_wf (ts : List ABIType) (data : ByteArray)
    (hrt : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray) (o : Nat), ev.size < 2^256 →
      encode t v = Except.ok ev → data.extract o (o + ev.size) = ev → decode t data o = Except.ok (v, o + ev.size))
    (hsize : ∀ t ∈ ts, isDynamic t = false → ∀ (v : ABIValue) (ev : ByteArray), encode t v = Except.ok ev → ev.size = headSize t)
    (hdvd : ∀ t ∈ ts, ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode t v = Except.ok ev → 32 ∣ ev.size)
    (v : ABIValue) (enc : ByteArray) (off : Nat)
    (hwf : enc.size < 2^256)
    (hbd : off + ts.foldl (fun a t => a + headSize t) 0 + 32 ≤ data.size)
    (henc : encode (.tuple ts) v = Except.ok enc)
    (hdata : data.extract off (off + enc.size) = enc) :
    decode (.tuple ts) data off = Except.ok (v, off + enc.size) := by
  cases hdyn : ts.any isDynamic with
  | true => exact roundtrip_tuple_dyn_wf ts data hrt hsize hdvd hdyn v enc off hwf hbd henc hdata
  | false =>
    have hstat_tuple : isDynamic (.tuple ts) = false := by rw [← tuple_any_isDynamic]; simpa [List.any_map] using hdyn
    exact roundtrip_tuple_stat_wf ts data hrt hsize hstat_tuple v enc off hwf henc hdata

/-! ### fixedArray encoding is 32-byte aligned (szdvd_fixedArray) -/


-- 32-alignment of a fixedArray encoding (arrayPack, no length prefix), under the bound
theorem szdvd_fixedArray (n : Nat) (e : ABIType)
    (hdvd_e : ∀ (v : ABIValue) (ev : ByteArray), ev.size < 2^256 → encode e v = Except.ok ev → 32 ∣ ev.size)
    (v : ABIValue) (ev : ByteArray) (hsz : ev.size < 2^256) (henc : encode (.fixedArray n e) v = Except.ok ev) :
    32 ∣ ev.size := by
  cases v with
  | array vals =>
    obtain ⟨encd, hEL', hlen, hpack⟩ := encode_fixedArray_inv n e vals ev henc
    have halign : ∀ b ∈ encd, 32 ∣ b.size :=
      encodeListElems_align e hdvd_e vals encd (isDynamic e) hEL' (by rw [← hpack]; exact hsz)
    rw [hpack]
    exact arrayPack_size_dvd (isDynamic e) encd (by rw [← hpack]; exact hsz) halign
  | uint _ | int _ | bool _ | bytes _ | string _ | address _ | tuple _ => badArrVal henc e
