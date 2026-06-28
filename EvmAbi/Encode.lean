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

theorem list_foldl_lt_cons (t : ABIType) (rest : List (ABIType × ABIValue)) :
    List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst rest) <
    List.foldl (fun acc t => acc + abiSize t) 0 (t :: List.map Prod.fst rest) :=
  list_foldl_lt_cons_abi t (List.map Prod.fst rest)

mutual

  def encode (type : ABIType) (value : ABIValue) : Except Error ByteArray :=
    match type, value with
    | .uint s, .uint v =>
      let b := s.len * 8
      if v ≥ 2 ^ b then Except.error (.uintExceeds b v)
      else Except.ok (uint256ToBytes v)
    | .int s, .int v =>
      let b := s.len * 8
      let half := 2 ^ (b - 1)
      if v < -(half : Int) || v ≥ (half : Int) then
        Except.error (.intOutOfRange b v)
      else Except.ok (intToBytes v s.len)
    | .bool, .bool v => Except.ok (uint256ToBytes (if v then 1 else 0))
    | .bytesM s, .bytes v =>
      if v.size ≠ s.len then Except.error (.fixedBytesSize s.len v.size)
      else Except.ok (padRight v 32)
    | .address, .address v =>
      if v.size ≠ 20 then Except.error (.addressSize v.size)
      else Except.ok (padLeft v 32)
    | .bytes, .bytes v =>
      if _ : v.size < 2 ^ 256 then
        Except.ok (uint256ToBytes v.size ++ padRight v (roundUp32 v.size))
      else
        Except.error (.dataTooLong v.size)
    | .string, .string v =>
      let utf8 := v.toUTF8
      if _ : utf8.size < 2 ^ 256 then
        Except.ok (uint256ToBytes utf8.size ++ padRight utf8 (roundUp32 utf8.size))
      else
        Except.error (.dataTooLong utf8.size)
    | .array elemType sz, .array vals =>
      if !isDynamic elemType then
        match sz with
        | some n =>
          if vals.length ≠ n then
            Except.error (.arrayElemCount n vals.length)
          else
            match encodeFixedArrayStatic elemType vals ByteArray.empty with
            | Except.ok enc =>
              Except.ok enc
            | Except.error e => Except.error e
        | none =>
          if _ : vals.length < 2 ^ 256 then
            match encodeFixedArrayStatic elemType vals ByteArray.empty with
            | Except.ok enc =>
              Except.ok (uint256ToBytes vals.length ++ enc)
            | Except.error e => Except.error e
          else
            Except.error (.arrayLengthOverflow vals.length)
      else
        match encodeFixedArrayDynamic elemType vals with
        | Except.ok enc =>
          match sz with
          | none =>
            if _ : vals.length < 2 ^ 256 then
              Except.ok (uint256ToBytes vals.length ++ enc)
            else
              Except.error (.arrayLengthOverflow vals.length)
          | some _ => Except.ok enc
        | Except.error e => Except.error e
    | _, _ => Except.error .typeValueMismatch
    termination_by (abiSize type, 0, 0)
    decreasing_by
      all_goals
        first
        | apply Prod.Lex.left; exact abiSize_lt_array elemType sz
        | apply Prod.Lex.left; simp [abiSize]

  def encodeFixedArrayStatic (elemType : ABIType) (vals : List ABIValue) (acc : ByteArray) : Except Error ByteArray :=
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

  def encodeFixedArrayDynamic (elemType : ABIType) (vals : List ABIValue) : Except Error ByteArray :=
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

  def encodeFixedArrayCollect (elemType : ABIType) (vals : List ABIValue) (acc : List ByteArray) : Except Error (List ByteArray) :=
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

  def encodeTupleElems (items : List (ABIType × ABIValue)) : Except Error ByteArray :=
    let hasDynamic := items.any (fun (t, _) => isDynamic t)
    if !hasDynamic then encodeTupleElemsStatic items ByteArray.empty
    else encodeTupleElemsDynamic items

  def encodeTupleElemsStatic (xs : List (ABIType × ABIValue)) (acc : ByteArray) : Except Error ByteArray :=
    match xs with
    | [] => Except.ok acc
    | (t, v) :: rest =>
      match encode t v with
      | Except.ok enc => encodeTupleElemsStatic rest (acc ++ enc)
      | Except.error e => Except.error e
    termination_by (List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst xs), 1, xs.length)
    decreasing_by
      all_goals
        first
        | apply Prod.Lex.left; exact list_foldl_lt_cons t rest
        | apply Prod.Lex.right (a := List.foldl (fun acc t => acc + abiSize t) 0 (t :: List.map Prod.fst rest))
          apply Prod.Lex.left; omega
  def encodeTupleElemsDynamic (items : List (ABIType × ABIValue)) : Except Error ByteArray :=
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

  def encodeTupleElemsCollect (xs : List (ABIType × ABIValue)) (acc : List (Bool × ByteArray)) : Except Error (List (Bool × ByteArray)) :=
    match xs with
    | [] => Except.ok acc.reverse
    | (t, v) :: rest =>
      match encode t v with
      | Except.ok enc => encodeTupleElemsCollect rest ((isDynamic t, enc) :: acc)
      | Except.error e => Except.error e
    termination_by (List.foldl (fun acc t => acc + abiSize t) 0 (List.map Prod.fst xs), 1, xs.length)
    decreasing_by
      all_goals
        first
        | apply Prod.Lex.left; exact list_foldl_lt_cons t rest
        | apply Prod.Lex.right (a := List.foldl (fun acc t => acc + abiSize t) 0 (t :: List.map Prod.fst rest))
          apply Prod.Lex.left; omega
end


def encodeArgs (types : List ABIType) (values : List ABIValue) : Except Error ByteArray :=
  if types.length ≠ values.length then
    Except.error (.argCountMismatch types.length values.length)
  else
    encodeTupleElems (List.zip types values)

end EvmAbi.ABI.Encode
