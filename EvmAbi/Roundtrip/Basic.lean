import EvmAbi.LemmaUtils

/-! Tactic macros + ByteArray-slice read helpers shared by the roundtrip proofs. -/

open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode
set_option autoImplicit false

/-- Discharge a wrong-`ABIValue`-constructor case: the `encode … = ok` hypothesis is false. -/
macro "badVal" h:ident : tactic =>
  `(tactic| first
    | exact absurd $h (by simp)
    | exact absurd $h (by unfold encode foldABIType; simp)
    | exact absurd $h (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; dsimp; simp))

/-- Discharge a wrong-`ABIValue`-constructor case for a container over element `e`: the extra
`rcases` splits the element's encoder entry so the `encode … = ok` hypothesis reduces to false. -/
macro "badArrVal" h:ident e:ident : tactic =>
  `(tactic| exact absurd $h (by unfold encode foldABIType; delta instABIVisitorEncoderEntry; rcases foldABIType EncoderEntry $e with ⟨d, f⟩; dsimp; simp))

/-- Discharge a case where an element encoder erred but `h : … = Except.ok v` was assumed. -/
macro "badErr" h:ident v:ident : tactic =>
  `(tactic| exact absurd (show Except.error _ = Except.ok $v from $h) (by simp))

/-- Open the encoder definition at hypothesis `h`: `encode … = ok` becomes the concrete match. -/
macro "openEnc" h:ident : tactic =>
  `(tactic| unfold encode foldABIType at $h:ident <;> delta instABIVisitorEncoderEntry at $h:ident <;> dsimp at $h:ident)
/-- Open the decoder definition on the goal. -/
macro "openDec" : tactic =>
  `(tactic| unfold decode foldABIType <;> delta instABIVisitorDecoderEntry <;> dsimp)
/-- Open the encoder definition on the goal (the `openEnc` sibling that acts on the goal). -/
macro "openEncG" : tactic =>
  `(tactic| unfold encode foldABIType <;> delta instABIVisitorEncoderEntry <;> dsimp)

/-! ## Reading back an appended encoding from a `data` slice

When a `data` slice `[off, off + (a ++ b).size)` is known to equal `a ++ b`, its first `a.size`
bytes are `a` and its next `b.size` bytes are `b`. These recur throughout the roundtrip proofs
(length-prefix ++ payload, head-grid ++ tails, static field ++ rest). -/

/-- First `a.size` bytes of a slice equal to `a ++ b`. -/
theorem extract_append_left_of_slice (data : ByteArray) (off : Nat) (a b : ByteArray)
    (h : data.extract off (off + (a ++ b).size) = a ++ b) :
    data.extract off (off + a.size) = a := by
  have e0 : (data.extract off (off + (a ++ b).size)).extract 0 a.size = data.extract off (off + a.size) := by
    rw [ByteArray.extract_extract, Nat.add_zero,
        show min (off + a.size) (off + (a ++ b).size) = off + a.size from by rw [ByteArray.size_append]; omega]
  rw [← e0, h, ByteArray.extract_append_eq_left rfl]

/-- Next `b.size` bytes of a slice equal to `a ++ b`. -/
theorem extract_append_right_of_slice (data : ByteArray) (off : Nat) (a b : ByteArray)
    (h : data.extract off (off + (a ++ b).size) = a ++ b) :
    data.extract (off + a.size) (off + a.size + b.size) = b := by
  have e0 : (data.extract off (off + (a ++ b).size)).extract a.size (a.size + b.size)
          = data.extract (off + a.size) (off + a.size + b.size) := by
    rw [ByteArray.extract_extract,
        show min (off + (a.size + b.size)) (off + (a ++ b).size) = off + a.size + b.size from by rw [ByteArray.size_append]; omega]
  rw [← e0, h]; exact ByteArray.extract_append_eq_right rfl rfl

/-- Read the leading 32-byte word `p` off a slice `p ++ rest` whose extent `U` reaches at least
`off + 32`. Unlike `extract_append_left_of_slice`, the extent `U` is arbitrary (need not be the
`.size` of the append), so this covers head-pointer reads out of a `32·n` head grid. -/
theorem extract_head32 (data : ByteArray) (off U : Nat) (p rest : ByteArray)
    (hp : p.size = 32) (hU : off + 32 ≤ U) (h : data.extract off U = p ++ rest) :
    data.extract off (off + 32) = p := by
  have e0 : (data.extract off U).extract 0 32 = data.extract off (off + 32) := by
    rw [ByteArray.extract_extract, Nat.add_zero, show min (off + 32) U = off + 32 from by omega]
  rw [← e0, h, ← hp]; exact ByteArray.extract_append_eq_left rfl

/-- Read the `rest` payload after the leading 32-byte word off a slice `p ++ rest`
(extent `U ≥ off + 32 + rest.size`); the head-grid counterpart of `extract_append_right_of_slice`. -/
theorem extract_tail_after32 (data : ByteArray) (off U : Nat) (p rest : ByteArray)
    (hp : p.size = 32) (hU : off + 32 + rest.size ≤ U) (h : data.extract off U = p ++ rest) :
    data.extract (off + 32) (off + 32 + rest.size) = rest := by
  have e0 : (data.extract off U).extract 32 (32 + rest.size) = data.extract (off + 32) (off + 32 + rest.size) := by
    rw [ByteArray.extract_extract, show min (off + (32 + rest.size)) U = off + 32 + rest.size from by omega]
  rw [← e0, h]; exact ByteArray.extract_append_eq_right hp.symm (by rw [hp])

/-! ## Dynamic bytes/string helpers -/

lemma dynamicRoundtrip_preamble (b : ByteArray) (hb256 : b.size < 2 ^ 256) :
    (uint256ToBytes b.size).size = 32 ∧ (padRight b (roundUp32 b.size)).size = roundUp32 b.size ∧
    b.size ≤ roundUp32 b.size ∧ (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).size = 32 + roundUp32 b.size ∧
    bytesToNat ((uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 0 32) = b.size ∧
    (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 32 (32 + b.size) = b := by
  have ha_sz : (uint256ToBytes b.size).size = 32 := uint256ToBytes_size b.size (natToBytes_size_bound b.size hb256)
  have h_roundUp_ge : b.size ≤ roundUp32 b.size := by unfold roundUp32; omega
  have h_pad_sz : (padRight b (roundUp32 b.size)).size = roundUp32 b.size := by
    unfold padRight; split; omega; simp [zeros_size]; omega
  have h_size : (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).size = 32 + roundUp32 b.size := by simp [ha_sz, h_pad_sz]
  have h_len : bytesToNat ((uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 0 32) = b.size := by
    rw [← ha_sz, extract_first_n, bytesToNat_uint256ToBytes b.size]
  have h_extract_val : (uint256ToBytes b.size ++ padRight b (roundUp32 b.size)).extract 32 (32 + b.size) = b := roundtrip_bytes_val b hb256
  exact ⟨ha_sz, h_pad_sz, h_roundUp_ge, h_size, h_len, h_extract_val⟩

lemma decodeDynamicBytes_roundtrip (v' : ByteArray) (hv256 : v'.size < 2 ^ 256) (data : ByteArray)
    (hdata : data = uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size)) :
    decodeDynamicBytes data 0 = Except.ok (.bytes v', data.size) := by
  rw [hdata]; rcases dynamicRoundtrip_preamble v' hv256 with ⟨_, _, h_roundUp_ge, h_size, h_len, h_extract_val⟩
  unfold decodeDynamicBytes; simp [h_size, h_len, h_extract_val, h_roundUp_ge]

lemma decodeDynamicString_roundtrip (v' : String) (hv256 : v'.toUTF8.size < 2 ^ 256) (data : ByteArray)
    (hdata : data = uint256ToBytes v'.toUTF8.size ++ padRight v'.toUTF8 (roundUp32 v'.toUTF8.size)) :
    decodeDynamicString data 0 = Except.ok (.string v', data.size) := by
  rw [decodeDynamicString, decodeDynamicBytes_roundtrip v'.toUTF8 hv256 data hdata]
  simp [Except.map]; have h : v'.toByteArray = v'.toUTF8 := rfl; rw [h, fromUTF8!_toUTF8 v']
