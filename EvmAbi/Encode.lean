/-
# ABI Encoding
-/

import EvmAbi.ABI

open EvmAbi.ABI

namespace EvmAbi.ABI.Encode

theorem abiSize_pos (t : ABIType) : 0 < abiSize t := by
  unfold abiSize; split <;> omega

theorem tuple_foldl_lt (es : List ABIType) :
    es.foldl (fun acc t => acc + abiSize t) 0 < abiSize (.tuple es) := by
  simp [abiSize]

theorem list_foldl_lt_cons (t : ABIType) (rest : List (ABIType × ABIValue)) (v : ABIValue) :
    List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst rest) <
    List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst ((t, v) :: rest)) := by
  simp
  have hpos : 0 < abiSize t := abiSize_pos t
  have h_eq : List.foldl (fun acc t => acc + abiSize t) (abiSize t) (List.map Prod.fst rest) =
             abiSize t + List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst rest) :=
    foldl_add_eq (abiSize t) (List.map Prod.fst rest)
  rw [h_eq]
  omega

mutual

  def encode (type : ABIType) (value : ABIValue) : Except String ByteArray :=
    match type, value with
    | .uint bits, .uint v =>
      let b := bits.val
      if v ≥ 2 ^ b then Except.error s!"uint{b}: value {v} exceeds 2^{b}"
      else Except.ok (uint256ToBytes v)
    | .int bits, .int v =>
      let b := bits.val
      let half := 2 ^ (b - 1)
      if v < -(half : Int) || v ≥ (half : Int) then
        Except.error s!"int{b}: value {v} out of range [{-half}, {half - 1}]"
      else Except.ok (intToBytes v bits)
    | .bool, .bool v => Except.ok (uint256ToBytes (if v then 1 else 0))
    | .bytesM sz, .bytes v =>
      if v.size ≠ sz then Except.error s!"bytes{sz}: expected {sz} bytes, got {v.size}"
      else Except.ok (padRight v 32)
    | .address, .address v =>
      if v.size ≠ 20 then Except.error s!"address: expected 20 bytes, got {v.size}"
      else Except.ok (padLeft v 32)
    | .bytes, .bytes v => Except.ok (uint256ToBytes v.size ++ padRight v (roundUp32 v.size))
    | .string, .string v =>
      let utf8 := v.toUTF8
      Except.ok (uint256ToBytes utf8.size ++ padRight utf8 (roundUp32 utf8.size))
    | .array elemType _size, .array vals =>
      if !isDynamic elemType then encodeFixedArrayStatic elemType vals ByteArray.empty
      else encodeFixedArrayDynamic elemType vals
    | .tuple elems, .tuple vals =>
      if elems.length ≠ vals.length then
        Except.error s!"tuple length mismatch: types {elems.length} vs values {vals.length}"
      else encodeTupleElems (List.zip elems vals)
    | _, _ => Except.error s!"type/value mismatch"
    termination_by (abiSize type, 0, 0)
    decreasing_by
      · apply Prod.Lex.left; exact abiSize_lt_array elemType size
      · apply Prod.Lex.left; exact abiSize_lt_array elemType size
      · have h_map : List.map Prod.fst (List.zip elems vals) = elems :=
          List.map_fst_zip (by omega : elems.length ≤ vals.length)
        have h_lt : List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst (List.zip elems vals)) <
                    abiSize (.tuple elems) := by
          simp [h_map, abiSize]
        apply Prod.Lex.left; exact h_lt

  def encodeFixedArrayStatic (elemType : ABIType) (vals : List ABIValue) (acc : ByteArray) : Except String ByteArray :=
    match vals with
    | [] => Except.ok acc
    | v :: rest =>
      match encode elemType v with
      | Except.ok enc => encodeFixedArrayStatic elemType rest (acc ++ enc)
      | Except.error e => Except.error e
    termination_by (abiSize elemType, 1, vals.length)
    decreasing_by
      · apply Prod.Lex.right (a := abiSize elemType)
        apply Prod.Lex.left; omega
      · apply Prod.Lex.right (a := abiSize elemType)
        apply Prod.Lex.right (a := 1)
        simp

  def encodeFixedArrayDynamic (elemType : ABIType) (vals : List ABIValue) : Except String ByteArray :=
    let headAreaSize := if vals.length = 0 then 32 else vals.length * 32
    match encodeFixedArrayCollect elemType vals [] with
    | Except.ok tails =>
      let init : Nat × ByteArray × ByteArray := (headAreaSize, ByteArray.empty, ByteArray.empty)
      let (_, heads, tailsBytes) :=
        List.foldl (fun (acc : Nat × ByteArray × ByteArray) (i_tail : Nat × ByteArray) =>
          let (offset, heads, accTails) := acc
          let (_, tailEnc) := i_tail
          (offset + roundUp32 tailEnc.size, heads ++ uint256ToBytes offset, accTails ++ tailEnc)
        ) init (List.zip (List.range vals.length) tails)
      Except.ok (heads ++ tailsBytes)
    | Except.error e => Except.error e
    termination_by (abiSize elemType, 2, vals.length)
    decreasing_by
      · apply Prod.Lex.right (a := abiSize elemType)
        apply Prod.Lex.left; omega

  def encodeFixedArrayCollect (elemType : ABIType) (vals : List ABIValue) (acc : List ByteArray) : Except String (List ByteArray) :=
    match vals with
    | [] => Except.ok acc.reverse
    | v :: rest =>
      match encode elemType v with
      | Except.ok enc => encodeFixedArrayCollect elemType rest (enc :: acc)
      | Except.error e => Except.error e
    termination_by (abiSize elemType, 1, vals.length)
    decreasing_by
      · apply Prod.Lex.right (a := abiSize elemType)
        apply Prod.Lex.left; omega
      · apply Prod.Lex.right (a := abiSize elemType)
        apply Prod.Lex.right (a := 1)
        simp

  def encodeTupleElems (items : List (ABIType × ABIValue)) : Except String ByteArray :=
    let hasDynamic := items.any (fun (t, _) => isDynamic t)
    if !hasDynamic then encodeTupleElemsStatic items ByteArray.empty
    else encodeTupleElemsDynamic items
    termination_by (List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst items), 3, items.length)
    decreasing_by
      · apply Prod.Lex.right (a := List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst items))
        apply Prod.Lex.left; omega
      · apply Prod.Lex.right (a := List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst items))
        apply Prod.Lex.left; omega

  def encodeTupleElemsStatic (xs : List (ABIType × ABIValue)) (acc : ByteArray) : Except String ByteArray :=
    match xs with
    | [] => Except.ok acc
    | (t, v) :: rest =>
      match encode t v with
      | Except.ok enc => encodeTupleElemsStatic rest (acc ++ enc)
      | Except.error e => Except.error e
    termination_by (List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst xs), 1, xs.length)
    decreasing_by
      · let total := List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst ((t, v) :: rest))
        have h_total_eq : total = abiSize t + List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst rest) := by
          unfold total; simp; exact foldl_add_eq (abiSize t) (List.map Prod.fst rest)
        have h_sz_le : abiSize t ≤ total := by
          rw [h_total_eq]; exact Nat.le_add_right _ _
        by_cases h_lt : abiSize t < total
        · apply Prod.Lex.left; exact h_lt
        · have h_total_le : total ≤ abiSize t := Nat.le_of_not_lt h_lt
          have h_eq : abiSize t = total := Nat.le_antisymm h_sz_le h_total_le
          rw [h_eq]
          apply Prod.Lex.right (a := total)
          apply Prod.Lex.left; omega
      · apply Prod.Lex.left; exact list_foldl_lt_cons t rest v

  def encodeTupleElemsDynamic (items : List (ABIType × ABIValue)) : Except String ByteArray :=
    let headAreaSize := items.length * 32
    match encodeTupleElemsCollect items [] with
    | Except.ok processed =>
      let init : Nat × ByteArray × ByteArray := (headAreaSize, ByteArray.empty, ByteArray.empty)
      let (_, heads, tails) :=
        List.foldl (fun (acc : Nat × ByteArray × ByteArray) (elem : Bool × ByteArray) =>
          let (offset, heads, accTails) := acc
          let (isDyn, enc) := elem
          if isDyn then (offset + roundUp32 enc.size, heads ++ uint256ToBytes offset, accTails ++ enc)
          else (offset, heads ++ enc, accTails)
        ) init processed
      Except.ok (heads ++ tails)
    | Except.error e => Except.error e
    termination_by (List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst items), 2, items.length)
    decreasing_by
      · apply Prod.Lex.right (a := List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst items))
        apply Prod.Lex.left; omega

  def encodeTupleElemsCollect (xs : List (ABIType × ABIValue)) (acc : List (Bool × ByteArray)) : Except String (List (Bool × ByteArray)) :=
    match xs with
    | [] => Except.ok acc.reverse
    | (t, v) :: rest =>
      match encode t v with
      | Except.ok enc => encodeTupleElemsCollect rest ((isDynamic t, enc) :: acc)
      | Except.error e => Except.error e
    termination_by (List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst xs), 1, xs.length)
    decreasing_by
      · let total := List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst ((t, v) :: rest))
        have h_total_eq : total = abiSize t + List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst rest) := by
          unfold total; simp; exact foldl_add_eq (abiSize t) (List.map Prod.fst rest)
        have h_sz_le : abiSize t ≤ total := by
          rw [h_total_eq]; exact Nat.le_add_right _ _
        by_cases h_lt : abiSize t < total
        · apply Prod.Lex.left; exact h_lt
        · have h_total_le : total ≤ abiSize t := Nat.le_of_not_lt h_lt
          have h_eq : abiSize t = total := Nat.le_antisymm h_sz_le h_total_le
          rw [h_eq]
          apply Prod.Lex.right (a := total)
          apply Prod.Lex.left; omega
      · apply Prod.Lex.left; exact list_foldl_lt_cons t rest v

end

def encodeArgs (types : List ABIType) (values : List ABIValue) : Except String ByteArray :=
  if types.length ≠ values.length then
    Except.error s!"argument count mismatch: {types.length} types vs {values.length} values"
  else
    encodeTupleElems (List.zip types values)

def toHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def bytesToHex (b : ByteArray) : String :=
  "0x" ++ b.foldl (fun acc byte =>
    acc ++ String.ofList [toHexDigit (byte.toNat / 16), toHexDigit (byte.toNat % 16)]
  ) ""

end EvmAbi.ABI.Encode
