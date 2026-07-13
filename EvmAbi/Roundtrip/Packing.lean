import EvmAbi.Roundtrip.Basic
import EvmAbi.Roundtrip.Primitives

/-! Encoder characterization: arrayPack/tuplePack fold structure, static encoding size = headSize, and static tuple decode. -/

open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode
set_option autoImplicit false

/-! ## Array/tuple packing helpers -/

/-- The encoder's dynamic flag agrees with `isDynamic`. -/
theorem tuple_any_isDynamic (ts : List ABIType) : (ts.map isDynamic).any id = isDynamic (.tuple ts) := by
  simp

theorem enc_fst_eq_isDynamic (e : ABIType) : (foldABIType EncoderEntry e).1 = isDynamic e := by
  match e with
  | .uint s | .int s | .bool | .address | .bytes | .fixedBytes s | .string =>
    simp only [foldABIType]; delta instABIVisitorEncoderEntry; dsimp
  | .array e' =>
    simp only [foldABIType]; delta instABIVisitorEncoderEntry
    rcases foldABIType EncoderEntry e' with ⟨d, f⟩
    dsimp
  | .fixedArray n e' =>
    have ih := enc_fst_eq_isDynamic e'
    unfold foldABIType
    simp
    exact ih
  | .tuple ts =>
    simp only [foldABIType]; delta instABIVisitorEncoderEntry; dsimp
    exact tuple_any_isDynamic ts

/-- From a destructured encoder entry `foldABIType EncoderEntry t = (d, f)`, the dynamic flag `d`
equals `isDynamic t` — the reusable form of `enc_fst_eq_isDynamic` applied through a `⟨d, f⟩` split. -/
theorem entry_fst_isDynamic {t : ABIType} {d : Bool} {f : ABIValue → Except Error ByteArray}
    (hentry : foldABIType EncoderEntry t = (d, f)) : d = isDynamic t := by
  have := enc_fst_eq_isDynamic t; rwa [hentry] at this

/-- Companion to `entry_fst_isDynamic`: from `foldABIType EncoderEntry t = (d, f)`, the encoder
component `f` is `encode t`. Packages the recurring `unfold encode; rw [hentry]` step. -/
theorem entry_snd_eq_encode {t : ABIType} {d : Bool} {f : ABIValue → Except Error ByteArray}
    (hentry : foldABIType EncoderEntry t = (d, f)) : f = encode t := by
  unfold encode; rw [hentry]

/-- Invert a successful dynamic-array encode: the length fits, the elements encode, and the
result is the length prefix followed by the packed elements. -/
theorem encode_array_inv (e : ABIType) (vals : List ABIValue) (enc : ByteArray)
    (henc : encode (.array e) (.array vals) = Except.ok enc) :
    ∃ encd, encodeListElems (encode e) vals = Except.ok encd ∧ vals.length < 2^256 ∧
      enc = uint256ToBytes vals.length ++ arrayPack (isDynamic e) encd := by
  unfold encode foldABIType at henc
  delta instABIVisitorEncoderEntry at henc
  rcases hentry : foldABIType EncoderEntry e with ⟨elemDyn, elemEnc⟩
  rw [hentry] at henc; dsimp at henc
  split at henc
  · rename_i hlt
    obtain ⟨encd, hEL, henc⟩ := bind_ok_inv henc
    refine ⟨encd, by rw [← entry_snd_eq_encode hentry]; exact hEL, hlt, ?_⟩
    rw [← entry_fst_isDynamic hentry]
    exact (Except.ok.inj henc).symm
  · exact absurd (show Except.error (Error.arrayLengthOverflow vals.length) = Except.ok enc from henc) (by simp)

/-- Invert a successful fixed-array encode: the element count matches, the elements encode, and
the result is the packed elements (no length prefix). -/
theorem encode_fixedArray_inv (n : Nat) (e : ABIType) (vals : List ABIValue) (enc : ByteArray)
    (henc : encode (.fixedArray n e) (.array vals) = Except.ok enc) :
    ∃ encd, encodeListElems (encode e) vals = Except.ok encd ∧ vals.length = n ∧
      enc = arrayPack (isDynamic e) encd := by
  unfold encode foldABIType at henc
  delta instABIVisitorEncoderEntry at henc
  rcases hentry : foldABIType EncoderEntry e with ⟨elemDyn, elemEnc⟩
  rw [hentry] at henc; dsimp at henc
  by_cases hlen : vals.length = n
  · rw [if_neg (not_not_intro hlen)] at henc
    obtain ⟨encd, hEL, henc⟩ := bind_ok_inv henc
    refine ⟨encd, by rw [← entry_snd_eq_encode hentry]; exact hEL, hlen, ?_⟩
    rw [← entry_fst_isDynamic hentry]
    exact (Except.ok.inj henc).symm
  · rw [if_pos (by simpa using hlen)] at henc
    exact absurd (show Except.error (Error.arrayElemCount n vals.length) = Except.ok enc from henc) (by simp)

/-- Invert a successful tuple encode: the field-encoder loop succeeds and the result is the
`tuplePack` of the entries. -/
theorem encode_tuple_inv (ts : List ABIType) (vs : List ABIValue) (enc : ByteArray)
    (henc : encode (.tuple ts) (.tuple vs) = Except.ok enc) :
    ∃ encd, instABIVisitorEncoderEntry.go ts (foldAll EncoderEntry ts) vs = Except.ok encd ∧
      enc = tuplePack (ts.map headSize) (ts.map isDynamic) encd := by
  openEnc henc
  obtain ⟨encd, hgo, hpack⟩ := bind_ok_inv henc
  exact ⟨encd, hgo, (Except.ok.inj hpack).symm⟩

/-- Left fold of `++` with a nonempty seed factors the seed out to the front. -/
theorem ba_foldl_init (init : ByteArray) (xs : List ByteArray) :
    xs.foldl (·++·) init = init ++ xs.foldl (·++·) ByteArray.empty := by
  induction xs generalizing init with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, ByteArray.empty_append]
    rw [ih (init ++ y), ih y, ByteArray.append_assoc]

theorem ba_foldl_cons (x : ByteArray) (xs : List ByteArray) :
    (x :: xs).foldl (·++·) ByteArray.empty = x ++ xs.foldl (·++·) ByteArray.empty := by
  simp only [List.foldl_cons, ByteArray.empty_append]; exact ba_foldl_init x xs

/-- Invert a successful `encodeListElems` on a cons. -/
theorem encodeListElems_cons_ok (e : ABIType) (v : ABIValue) (rest : List ABIValue) (encd : List ByteArray)
    (henc : encodeListElems (encode e) (v :: rest) = Except.ok encd) :
    ∃ ev er, encode e v = .ok ev ∧ encodeListElems (encode e) rest = .ok er ∧ encd = ev :: er := by
  rw [encodeListElems] at henc
  obtain ⟨ev, hev, henc⟩ := bind_ok_inv henc
  obtain ⟨er, her, henc⟩ := bind_ok_inv henc
  exact ⟨ev, er, hev, her, (Except.ok.inj henc).symm⟩

/-! ## Static encoding size = headSize -/

theorem concat_size_uniform (encd : List ByteArray) (k : Nat) (h : ∀ b ∈ encd, b.size = k) :
    (encd.foldl (·++·) ByteArray.empty).size = encd.length * k := by
  induction encd with
  | nil => simp
  | cons x xs ih =>
    rw [ba_foldl_cons, ByteArray.size_append, h x (by simp),
        ih (fun b hb => h b (by simp [hb]))]
    grind

theorem encodeListElems_length (e : ABIType) (vals : List ABIValue) (encd : List ByteArray)
    (h : encodeListElems (encode e) vals = Except.ok encd) : encd.length = vals.length := by
  induction vals generalizing encd with
  | nil => simp only [encodeListElems, Except.ok.injEq] at h; subst h; simp
  | cons v rest ih =>
    obtain ⟨ev, er, hev, her, rfl⟩ := encodeListElems_cons_ok e v rest encd h
    simp [ih er her]

theorem encodeListElems_mem (e : ABIType) (vals : List ABIValue) (encd : List ByteArray)
    (h : encodeListElems (encode e) vals = Except.ok encd) (b : ByteArray) (hb : b ∈ encd) :
    ∃ v, encode e v = Except.ok b := by
  induction vals generalizing encd with
  | nil => simp only [encodeListElems, Except.ok.injEq] at h; subst h; simp at hb
  | cons v rest ih =>
    obtain ⟨ev, er, hev, her, rfl⟩ := encodeListElems_cons_ok e v rest encd h
    rcases List.mem_cons.mp hb with h1 | h2
    · exact ⟨v, by rw [h1]; exact hev⟩
    · exact ih er her h2

theorem size_eq_uint (s : ByteSize) (v : ABIValue) (ev : ByteArray) (henc : encode (.uint s) v = Except.ok ev) : ev.size = headSize (.uint s) := by
  cases v with
  | uint v' =>
    openEnc henc
    split at henc
    · rename_i hb
      have hev := Except.ok.inj henc
      have hv256 : v' < 2 ^ 256 := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (by have := s.h.right; omega))
      simp only [headSize, isDynamic]; rw [← hev]; exact uint256ToBytes_size v' (natToBytes_size_bound v' hv256)
    · badErr henc ev
  | _ => badVal henc

theorem size_eq_int (s : ByteSize) (v : ABIValue) (ev : ByteArray) (henc : encode (.int s) v = Except.ok ev) : ev.size = headSize (.int s) := by
  cases v with
  | int v' =>
    openEnc henc
    simp only [Bool.or_eq_true, decide_eq_true_eq] at henc
    split at henc
    · badErr henc ev
    · rename_i hcond
      have hev := Except.ok.inj henc
      push Not at hcond
      simp only [headSize, isDynamic]; rw [← hev]; exact intToBytes_size32 s v' ⟨by omega, by omega⟩
  | _ => badVal henc

theorem size_eq_bool (v : ABIValue) (ev : ByteArray) (henc : encode .bool v = Except.ok ev) : ev.size = headSize .bool := by
  cases v with
  | bool v' =>
    openEnc henc
    have hev := Except.ok.inj henc
    have hbits : (if v' then 1 else 0) < 2 ^ 256 := by split <;> omega
    simp only [headSize, isDynamic]; rw [← hev]; exact uint256ToBytes_size _ (natToBytes_size_bound _ hbits)
  | _ => badVal henc

theorem size_eq_address (v : ABIValue) (ev : ByteArray) (henc : encode .address v = Except.ok ev) : ev.size = headSize .address := by
  cases v with
  | address v' =>
    openEnc henc
    split at henc
    · rename_i h20
      have hev := Except.ok.inj henc
      simp only [headSize, isDynamic]; rw [← hev]; unfold padLeft; simp [h20, zeros_size]
    · badErr henc ev
  | _ => badVal henc

theorem size_eq_fixedBytes (s : ByteSize) (v : ABIValue) (ev : ByteArray) (henc : encode (.fixedBytes s) v = Except.ok ev) : ev.size = headSize (.fixedBytes s) := by
  cases v with
  | bytes v' =>
    openEnc henc
    split at henc
    · rename_i hsz
      have hev := Except.ok.inj henc
      simp only [headSize, isDynamic]; rw [← hev]; exact padRight_size_32 v' (by rw [hsz]; exact s.h.right)
    · badErr henc ev
  | _ => badVal henc

/-! ## Tuple encode (`go`) / `tuplePack` reduction helpers -/

theorem go_cons {t : ABIType} {ts' : List ABIType} (dyn : Bool) (enc : ABIValue → Except Error ByteArray)
    (rest : All EncoderEntry ts') (v : ABIValue) (vs' : List ABIValue) :
    instABIVisitorEncoderEntry.go (t :: ts') (All.cons (dyn, enc) rest) (v :: vs')
      = (enc v >>= fun bytes => instABIVisitorEncoderEntry.go ts' rest vs' >>= fun tail => Except.ok ((dyn, bytes) :: tail)) := rfl

theorem go_cons_ok {t : ABIType} {ts' : List ABIType} (dyn : Bool) (enc : ABIValue → Except Error ByteArray)
    (rest : All EncoderEntry ts') (vs : List ABIValue) (encd : List (Bool × ByteArray))
    (h : instABIVisitorEncoderEntry.go (t :: ts') (All.cons (dyn, enc) rest) vs = Except.ok encd) :
    ∃ v vs' b tail, vs = v :: vs' ∧ enc v = Except.ok b ∧
      instABIVisitorEncoderEntry.go ts' rest vs' = Except.ok tail ∧ encd = (dyn, b) :: tail := by
  cases vs with
  | nil => exact absurd (show Except.error Error.typeValueMismatch = Except.ok encd from h) (by simp)
  | cons v vs' =>
    rw [go_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok_inv h
    obtain ⟨tail, ht, h⟩ := bind_ok_inv h
    exact ⟨v, vs', b, tail, rfl, hb, ht, (Except.ok.inj h).symm⟩

/-- Invert one step of the tuple encoder loop, phrased directly in terms of `encode` and
`isDynamic` — call sites need no `foldABIType EncoderEntry` destructuring or
`entry_fst_isDynamic`/`entry_snd_eq_encode` plumbing. -/
theorem go_cons_inv (t : ABIType) (ts' : List ABIType) (vs : List ABIValue) (encd : List (Bool × ByteArray))
    (hgo : instABIVisitorEncoderEntry.go (t :: ts') (foldAll EncoderEntry (t :: ts')) vs = Except.ok encd) :
    ∃ v vs' b tail, vs = v :: vs' ∧ encode t v = Except.ok b ∧
      instABIVisitorEncoderEntry.go ts' (foldAll EncoderEntry ts') vs' = Except.ok tail ∧
      encd = (isDynamic t, b) :: tail := by
  rw [foldAll] at hgo
  rcases hentry : foldABIType EncoderEntry t with ⟨dyn, enc⟩
  rw [hentry] at hgo
  obtain ⟨v, vs', b, tail, rfl, hb, htail, rfl⟩ := go_cons_ok dyn enc (foldAll EncoderEntry ts') vs encd hgo
  exact ⟨v, vs', b, tail, rfl, by rw [← entry_snd_eq_encode hentry]; exact hb, htail,
         by rw [entry_fst_isDynamic hentry]⟩

/-- Invert the tuple encoder loop on `[]`: only `vs = []`, `encd = []` succeeds. -/
theorem go_nil_inv (vs : List ABIValue) (encd : List (Bool × ByteArray))
    (hgo : instABIVisitorEncoderEntry.go [] (foldAll EncoderEntry []) vs = Except.ok encd) :
    vs = [] ∧ encd = [] := by
  cases vs with
  | nil => exact ⟨rfl, (Except.ok.inj (show Except.ok [] = Except.ok encd from hgo)).symm⟩
  | cons v vs' => exact absurd (show Except.error Error.typeValueMismatch = Except.ok encd from hgo) (by simp)

theorem tuplePack_static (headSizes : List Nat) (dynamics : List Bool) (encd : List (Bool × ByteArray))
    (hd : dynamics.any id = false) :
    tuplePack headSizes dynamics encd = encd.foldl (fun acc x => acc ++ x.2) ByteArray.empty := by
  unfold tuplePack; simp only [hd, Bool.not_false, if_true]

theorem isDynamic_tuple_cons_split (t : ABIType) (ts : List ABIType) (h : isDynamic (.tuple (t :: ts)) = false) :
    isDynamic t = false ∧ isDynamic (.tuple ts) = false := by
  have he : isDynamic (.tuple (t :: ts)) = (isDynamic t || isDynamic (.tuple ts)) := by grind
  rw [he] at h
  cases ht : isDynamic t <;> cases hts : isDynamic (.tuple ts) <;> grind

theorem isDynamic_tuple_of_all_static (ts : List ABIType) (h : ∀ t ∈ ts, isDynamic t = false) :
    isDynamic (.tuple ts) = false := by
  grind

/-- Head size of a static tuple splits over the cons (false for dynamic tuples: their head is 32). -/
theorem headSize_tuple_cons (t : ABIType) (ts : List ABIType) (hstat : isDynamic (.tuple (t :: ts)) = false) :
    headSize (.tuple (t :: ts)) = headSize t + headSize (.tuple ts) := by
  grind

theorem ba_foldl_snd_init (init : ByteArray) (xs : List (Bool × ByteArray)) :
    xs.foldl (fun acc x => acc ++ x.2) init = init ++ xs.foldl (fun acc x => acc ++ x.2) ByteArray.empty := by
  induction xs generalizing init with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, ByteArray.empty_append]
    rw [ih (init ++ y.2), ih (y.2), ByteArray.append_assoc]

theorem ba_foldl_snd_cons (x : Bool × ByteArray) (xs : List (Bool × ByteArray)) :
    (x :: xs).foldl (fun acc x => acc ++ x.2) ByteArray.empty = x.2 ++ xs.foldl (fun acc x => acc ++ x.2) ByteArray.empty := by
  simp only [List.foldl_cons, ByteArray.empty_append]; exact ba_foldl_snd_init x.2 xs

/-- Static fixed-array encoding size = `headSize`, given the element size fact and staticity. -/
theorem size_eq_fixedArray_core (n : Nat) (e : ABIType)
    (hsize_e : ∀ v ev, encode e v = Except.ok ev → ev.size = headSize e)
    (hstat_e : isDynamic e = false)
    (v : ABIValue) (ev : ByteArray) (henc : encode (.fixedArray n e) v = Except.ok ev) :
    ev.size = headSize (.fixedArray n e) := by
  cases v with
  | array vals =>
    obtain ⟨encd, hEL', hlen, hpack⟩ := encode_fixedArray_inv n e vals ev henc
    rw [hstat_e] at hpack
    rw [show arrayPack false encd = encd.foldl (·++·) ByteArray.empty from by simp [arrayPack]] at hpack
    have hall : ∀ b ∈ encd, b.size = headSize e := fun b hb => by
      obtain ⟨w, hw⟩ := encodeListElems_mem e vals encd hEL' b hb
      exact hsize_e w b hw
    rw [hpack, concat_size_uniform encd (headSize e) hall,
        encodeListElems_length e vals encd hEL', hlen]
    simp only [headSize, isDynamic, hstat_e, Bool.false_eq_true, if_false]
  | _ => badArrVal henc e

/-- If a tuple type is static, every element type is static. -/
theorem tuple_static_elems (ts : List ABIType) (h : isDynamic (.tuple ts) = false) :
    ∀ t ∈ ts, isDynamic t = false := by
  have h2 : (ts.map isDynamic).any id = false := by rw [tuple_any_isDynamic]; exact h
  intro t ht
  have hmem : isDynamic t ∈ (ts.map isDynamic) := List.mem_map_of_mem ht
  by_contra hc
  have : (ts.map isDynamic).any id = true := by
    rw [List.any_eq_true]; exact ⟨isDynamic t, hmem, by simpa using hc⟩
  rw [this] at h2; simp at h2

/-! ## Static tuple decode + headSize helpers -/

theorem headSize_foldl_shift (init : Nat) (ts : List ABIType) :
    ts.foldl (fun acc t => acc + headSize t) init = init + ts.foldl (fun acc t => acc + headSize t) 0 := by
  induction ts generalizing init with
  | nil => simp
  | cons t ts ih => simp only [List.foldl_cons]; rw [ih (init + headSize t), ih (0 + headSize t)]; omega

theorem headSize_tuple_foldl (ts : List ABIType) (hstat : isDynamic (.tuple ts) = false) :
    ts.foldl (fun acc t => acc + headSize t) 0 = headSize (.tuple ts) := by
  rw [headSize, hstat]
  simp [List.foldl_map, List.sum_eq_foldl]

theorem decodeTupleStatic_nil (data : ByteArray) (off : Nat) (acc : List ABIValue) :
    decodeTupleStatic (All.nil : All DecoderEntry []) data off acc = Except.ok (acc.reverse, off) := rfl

theorem decodeTupleStatic_cons {t : ABIType} {ts' : List ABIType} (dec' : DecoderEntry t)
    (rest : All DecoderEntry ts') (data : ByteArray) (off : Nat) (acc : List ABIValue) :
    decodeTupleStatic (All.cons dec' rest) data off acc
      = (dec' data off >>= fun x => decodeTupleStatic rest data x.2 (x.1 :: acc)) := rfl
