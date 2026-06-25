/-
# ABI Decoding
-/

import EvmAbi.ABI

open EvmAbi.ABI

namespace EvmAbi.ABI.Decode

def decodeDynamicBytes (data : ByteArray) (offset : Nat) : Except String (ABIValue × Nat) :=
  if offset + 32 > data.size then
    Except.error s!"bytes: data too short for length at offset {offset}"
  else
    let len := bytesToNat (data.extract offset (offset + 32))
    let dataStart := offset + 32
    if dataStart + len > data.size then
      Except.error s!"bytes: data too short for {len} bytes at offset {dataStart}"
    else
      let val := data.extract dataStart (dataStart + len)
      let consumed := 32 + roundUp32 len
      Except.ok (.bytes val, offset + consumed)

def decodeDynamicString (data : ByteArray) (offset : Nat) : Except String (ABIValue × Nat) :=
  if offset + 32 > data.size then
    Except.error s!"string: data too short for length at offset {offset}"
  else
    let len := bytesToNat (data.extract offset (offset + 32))
    let dataStart := offset + 32
    if dataStart + len > data.size then
      Except.error s!"string: data too short for {len} bytes at offset {dataStart}"
    else
      let rawBytes := data.extract dataStart (dataStart + len)
      let s := String.fromUTF8! rawBytes
      let consumed := 32 + roundUp32 len
      Except.ok (.string s, offset + consumed)

def computeFixedArraySize (elemType : ABIType) (n : Nat) : Nat :=
  if !isDynamic elemType then n * 32 else n * 32

theorem list_foldl_lt_cons_abi (t : ABIType) (rest : List ABIType) :
    List.foldl (fun acc t => acc + abiSize t) 0 rest <
    List.foldl (fun acc t => acc + abiSize t) 0 (t :: rest) := by
  simp
  have hpos : 0 < abiSize t := by unfold abiSize; split <;> omega
  have h_eq : List.foldl (fun acc t => acc + abiSize t) (abiSize t) rest =
             abiSize t + List.foldl (fun acc t => acc + abiSize t) 0 rest :=
    foldl_add_eq (abiSize t) rest
  rw [h_eq]; omega

mutual

  def decode (type : ABIType) (data : ByteArray) (offset : Nat) : Except String (ABIValue × Nat) :=
    match type with
    | .uint bits =>
      let b := bits.val
      if offset + 32 > data.size then
        Except.error s!"uint{b}: data too short at offset {offset}"
      else
        let rawVal := bytesToNat (data.extract offset (offset + 32))
        if rawVal ≥ 2 ^ b then
          Except.error s!"uint{b}: decoded value {rawVal} exceeds 2^{b}"
        else Except.ok (.uint rawVal, offset + 32)
    | .int bits =>
      let b := bits.val
      if offset + 32 > data.size then
        Except.error s!"int{b}: data too short at offset {offset}"
      else
        let rawVal := bytesToNat (data.extract offset (offset + 32))
        let masked := rawVal % (2 ^ b)
        let half := 2 ^ (b - 1)
        if masked < half then Except.ok (.int (Int.ofNat masked), offset + 32)
        else Except.ok (.int (-(Int.ofNat (2 ^ b - masked))), offset + 32)
    | .bool =>
      if offset + 32 > data.size then
        Except.error s!"bool: data too short at offset {offset}"
      else
        let rawVal := bytesToNat (data.extract offset (offset + 32))
        if rawVal = 0 then Except.ok (.bool false, offset + 32)
        else if rawVal = 1 then Except.ok (.bool true, offset + 32)
        else Except.error s!"bool: invalid value {rawVal}, expected 0 or 1"
    | .bytesM sz =>
      if offset + 32 > data.size then
        Except.error s!"bytes{sz}: data too short at offset {offset}"
      else
        let val := data.extract offset (offset + sz)
        Except.ok (.bytes val, offset + 32)
    | .address =>
      if offset + 32 > data.size then
        Except.error s!"address: data too short at offset {offset}"
      else
        let val := data.extract (offset + 12) (offset + 32)
        Except.ok (.address val, offset + 32)
    | .bytes => decodeDynamicBytes data offset
    | .string => decodeDynamicString data offset
    | .array elemType _optSize =>
      match _optSize with
      | some size =>
        match decodeFixedArray elemType size data offset with
        | Except.ok (vals, _) =>
          Except.ok (.array vals, offset + computeFixedArraySize elemType size)
        | Except.error e => Except.error e
      | none => decodeDynamicArray elemType data offset
    | .tuple elems =>
      match decodeTupleElems elems data offset with
      | Except.ok (vals, endOff) => Except.ok (.tuple vals, endOff)
      | Except.error e => Except.error e
    termination_by (abiSize type, 0, 0)
    decreasing_by
      · apply Prod.Lex.left; apply abiSize_lt_array
      · apply Prod.Lex.left; apply abiSize_lt_array
      · have h_lt : List.foldl (fun acc t => acc + abiSize t) 0 elems < abiSize (.tuple elems) := by
          simp [abiSize]
        apply Prod.Lex.left; exact h_lt

  def decodeFixedArray (elemType : ABIType) (n : Nat) (data : ByteArray) (offset : Nat)
      : Except String (List ABIValue × Nat) :=
    if !isDynamic elemType then
      let rec goStatic (i : Nat) (off : Nat) (acc : List ABIValue) : Except String (List ABIValue × Nat) :=
        if i ≥ n then Except.ok (acc.reverse, off)
        else
          match decode elemType data off with
          | Except.ok (v, newOff) => goStatic (i + 1) newOff (v :: acc)
          | Except.error e => Except.error e
        termination_by (abiSize elemType, 1, n - i)
      goStatic 0 offset []
    else
      let headAreaSize := n * 32
      let rec goDynamic (i : Nat) (vals : List ABIValue) (maxEnd : Nat) : Except String (List ABIValue × Nat) :=
        if i ≥ n then Except.ok (vals.reverse, maxEnd)
        else
          let headOff := offset + i * 32
          if headOff + 32 > data.size then
            Except.error s!"array: data too short for head at offset {headOff}"
          else
            let rawOffset := bytesToNat (data.extract headOff (headOff + 32))
            let tailOff := offset + rawOffset
            match decode elemType data tailOff with
            | Except.ok (v, newOff) => goDynamic (i + 1) (v :: vals) (max newOff maxEnd)
            | Except.error e => Except.error e
          termination_by (abiSize elemType, 1, n - i)
      goDynamic 0 [] (offset + headAreaSize)
    termination_by (abiSize elemType, 2, n)

  def decodeDynamicArray (elemType : ABIType) (data : ByteArray) (offset : Nat)
      : Except String (ABIValue × Nat) :=
    if offset + 32 > data.size then
      Except.error s!"array[]: data too short for length at offset {offset}"
    else
      let len := bytesToNat (data.extract offset (offset + 32))
      let arrayOffset := offset + 32
      match decodeFixedArray elemType len data arrayOffset with
      | Except.ok (vals, _) =>
        let totalConsumed :=
          if !isDynamic elemType then 32 + len * 32
          else
            let headAreaSize := len * 32
            let init := arrayOffset + headAreaSize
            let rec calcEnd (i : Nat) (endPos : Nat) : Nat :=
              if i ≥ len then endPos
              else
                let headOff := arrayOffset + i * 32
                let rawOffset := bytesToNat (data.extract headOff (headOff + 32))
                let tailOff := arrayOffset + rawOffset
                match decode elemType data tailOff with
                | Except.ok (_, newOff) => calcEnd (i + 1) (max endPos newOff)
                | Except.error _ => calcEnd (i + 1) endPos
              termination_by (abiSize elemType, 1, len - i)
            calcEnd 0 init - offset
        Except.ok (.array vals, offset + totalConsumed)
      | Except.error e => Except.error e
    termination_by (abiSize elemType, 3, 0)

  def decodeTupleElems (types : List ABIType) (data : ByteArray) (offset : Nat)
      : Except String (List ABIValue × Nat) :=
    let hasDynamic := types.any isDynamic
    if !hasDynamic then
      let rec goStatic (ts : List ABIType) (off : Nat) (acc : List ABIValue) : Except String (List ABIValue × Nat) :=
        match ts with
        | [] => Except.ok (acc.reverse, off)
        | t :: rest =>
          match decode t data off with
          | Except.ok (v, newOff) => goStatic rest newOff (v :: acc)
          | Except.error e => Except.error e
        termination_by (List.foldl (fun acc t => acc + abiSize t) 0 ts, 1, ts.length)
        decreasing_by
          · let total_fs := List.foldl (fun acc t => acc + abiSize t) 0 (t :: rest)
            have hmem : t ∈ (t :: rest) := by simp
            have h_sz_le : abiSize t ≤ total_fs := mem_foldl_le t (t :: rest) hmem
            by_cases h_lt : abiSize t < total_fs
            · apply Prod.Lex.left; exact h_lt
            · have h_total_le : total_fs ≤ abiSize t := Nat.le_of_not_lt h_lt
              have h_eq : abiSize t = total_fs := Nat.le_antisymm h_sz_le h_total_le
              rw [h_eq]
              apply Prod.Lex.right (a := total_fs)
              apply Prod.Lex.left; omega
          · apply Prod.Lex.left; exact list_foldl_lt_cons_abi t rest
      goStatic types offset []
    else
      let headAreaSize := types.length * 32
      let rec goDynamic (i : Nat) (vals : List ABIValue) (maxEnd : Nat) : Except String (List ABIValue × Nat) :=
        if h : i ≥ types.length then Except.ok (vals.reverse, maxEnd)
        else
          let headOff := offset + i * 32
          if headOff + 32 > data.size then
            Except.error s!"tuple: data too short for head at offset {headOff}"
          else
            let hi : i < types.length := by omega
            let t := types.get ⟨i, hi⟩
            if isDynamic t then
              let rawOffset := bytesToNat (data.extract headOff (headOff + 32))
              let tailOff := offset + rawOffset
              match decode t data tailOff with
              | Except.ok (v, newOff) => goDynamic (i + 1) (v :: vals) (max maxEnd newOff)
              | Except.error e => Except.error e
            else
              match decode t data headOff with
              | Except.ok (v, _) => goDynamic (i + 1) (v :: vals) maxEnd
              | Except.error e => Except.error e
        termination_by (List.foldl (fun acc t => acc + abiSize t) 0 types, 1, types.length - i)
        decreasing_by
          all_goals
            first
            | let total := List.foldl (fun acc t => acc + abiSize t) 0 types
              have h_mem : types.get ⟨i, hi⟩ ∈ types := by
                have := List.getElem_mem (l := types) (n := i) (h := hi)
                simpa using this
              have h_sz_le : abiSize (types.get ⟨i, hi⟩) ≤ total :=
                mem_foldl_le (types.get ⟨i, hi⟩) types h_mem
              by_cases h_lt : abiSize (types.get ⟨i, hi⟩) < total
              · apply Prod.Lex.left; exact h_lt
              · have h_total_le : total ≤ abiSize (types.get ⟨i, hi⟩) := Nat.le_of_not_lt h_lt
                have h_eq : abiSize (types.get ⟨i, hi⟩) = total :=
                  Nat.le_antisymm h_sz_le h_total_le
                rw [h_eq]
                apply Prod.Lex.right (a := total)
                apply Prod.Lex.left; omega
            | apply Prod.Lex.right (a := List.foldl (fun acc t => acc + abiSize t) 0 types)
              apply Prod.Lex.right (a := 1)
              omega

      goDynamic 0 [] (offset + headAreaSize)
    termination_by (List.foldl (fun acc t => acc + abiSize t) 0 types, 3, types.length)

end

def decodeArgs (types : List ABIType) (data : ByteArray) (offset : Nat := 0) : Except String (List ABIValue) :=
  match decodeTupleElems types data offset with
  | Except.ok (vals, _) => Except.ok vals
  | Except.error e => Except.error e

end EvmAbi.ABI.Decode
