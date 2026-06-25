/-
# ABI Decoding

Implements Ethereum ABI decoding per the Solidity ABI specification.
This is the inverse of the encoding defined in `Encode.lean`.
-/

import EvmAbi.ABI

open EvmAbi.ABI

namespace EvmAbi.ABI.Decode

----------------------------------------------------------------------
-- Dynamic bytes (standalone, used by decode)
----------------------------------------------------------------------

/-- Decode dynamic bytes: offset starts at a uint256 length followed by the data.
    Returns (bytes value, next offset = start + 32 + roundUp32(len)). -/
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

/-- Decode dynamic string: same as bytes but decoded as UTF-8. -/
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

/-- Compute the byte size of a fixed-size array in encoding (for forward skip). -/
def computeFixedArraySize (elemType : ABIType) (n : Nat) : Nat :=
  if !isDynamic elemType then n * 32 else n * 32

----------------------------------------------------------------------
-- Mutually recursive decoding functions
----------------------------------------------------------------------

mutual

  /-- Decode a single ABI value from `data` starting at `offset`.
      Returns the decoded value and the next offset (one past the consumed bytes). -/
  partial def decode (type : ABIType) (data : ByteArray) (offset : Nat) : Except String (ABIValue × Nat) :=
    match type with
    | .uint bits =>
      if bits < 8 || bits % 8 ≠ 0 then
        Except.error s!"uint{bits}: bits must be a multiple of 8 and ≥ 8"
      else if offset + 32 > data.size then
        Except.error s!"uint{bits}: data too short at offset {offset}"
      else
        let rawVal := bytesToNat (data.extract offset (offset + 32))
        if rawVal ≥ 2 ^ bits then
          Except.error s!"uint{bits}: decoded value {rawVal} exceeds 2^{bits}"
        else
          Except.ok (.uint rawVal, offset + 32)

    | .int bits =>
      if bits < 8 || bits % 8 ≠ 0 then
        Except.error s!"int{bits}: bits must be a multiple of 8 and ≥ 8"
      else if offset + 32 > data.size then
        Except.error s!"int{bits}: data too short at offset {offset}"
      else
        let rawVal := bytesToNat (data.extract offset (offset + 32))
        let masked := rawVal % (2 ^ bits)  -- mask to bits bits for sign check
        let half := 2 ^ (bits - 1)
        if masked < half then
          Except.ok (.int (Int.ofNat masked), offset + 32)
        else
          Except.ok (.int (-(Int.ofNat (2 ^ bits - masked))), offset + 32)

    | .bool =>
      if offset + 32 > data.size then
        Except.error s!"bool: data too short at offset {offset}"
      else
        let rawVal := bytesToNat (data.extract offset (offset + 32))
        if rawVal = 0 then
          Except.ok (.bool false, offset + 32)
        else if rawVal = 1 then
          Except.ok (.bool true, offset + 32)
        else
          Except.error s!"bool: invalid value {rawVal}, expected 0 or 1"

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

    | .bytes =>
      decodeDynamicBytes data offset

    | .string =>
      decodeDynamicString data offset

    | .array elemType optSize =>
      match optSize with
      | some size =>
        match decodeFixedArray elemType size data offset with
        | Except.ok (vals, _) =>
          Except.ok (.array vals, offset + computeFixedArraySize elemType size)
        | Except.error e => Except.error e
      | none =>
        decodeDynamicArray elemType data offset

    | .tuple elems =>
      match decodeTupleElems elems data offset with
      | Except.ok (vals, endOff) => Except.ok (.tuple vals, endOff)
      | Except.error e => Except.error e
  /-- Decode a fixed-size array of `n` elements of type `elemType` from `data` at `offset`. -/
  partial def decodeFixedArray (elemType : ABIType) (n : Nat) (data : ByteArray) (offset : Nat)
      : Except String (List ABIValue × Nat) :=
    if !isDynamic elemType then
      let rec goStatic (i : Nat) (off : Nat) (acc : List ABIValue) : Except String (List ABIValue × Nat) :=
        if i ≥ n then
          Except.ok (acc.reverse, off)
        else
          match decode elemType data off with
          | Except.ok (v, newOff) => goStatic (i + 1) newOff (v :: acc)
          | Except.error e => Except.error e
      goStatic 0 offset []
    else
      let headAreaSize := n * 32
      let rec goDynamic (i : Nat) (vals : List ABIValue) (maxEnd : Nat) : Except String (List ABIValue × Nat) :=
        if i ≥ n then
          Except.ok (vals.reverse, maxEnd)
        else
          let headOff := offset + i * 32
          if headOff + 32 > data.size then
            Except.error s!"array: data too short for head at offset {headOff}"
          else
            let rawOffset := bytesToNat (data.extract headOff (headOff + 32))
            let tailOff := offset + rawOffset
            match decode elemType data tailOff with
            | Except.ok (v, newOff) =>
              goDynamic (i + 1) (v :: vals) (max newOff maxEnd)
            | Except.error e => Except.error e
      goDynamic 0 [] (offset + headAreaSize)

  /-- Decode a dynamic array: reads length then elements. -/
  partial def decodeDynamicArray (elemType : ABIType) (data : ByteArray) (offset : Nat)
      : Except String (ABIValue × Nat) :=
    if offset + 32 > data.size then
      Except.error s!"array[]: data too short for length at offset {offset}"
    else
      let len := bytesToNat (data.extract offset (offset + 32))
      let arrayOffset := offset + 32
      match decodeFixedArray elemType len data arrayOffset with
      | Except.ok (vals, _) =>
        let totalConsumed :=
          if !isDynamic elemType then
            32 + len * 32
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
            calcEnd 0 init - offset
        Except.ok (.array vals, offset + totalConsumed)
      | Except.error e => Except.error e

  /-- Decode a tuple with head/tail mechanism.
      Returns (list of values, next offset past the entire tuple). -/
  partial def decodeTupleElems (types : List ABIType) (data : ByteArray) (offset : Nat)
      : Except String (List ABIValue × Nat) :=
    let len := types.length
    let headAreaSize := len * 32
    let hasDynamic := types.any isDynamic

    if !hasDynamic then
      let rec goStatic (ts : List ABIType) (off : Nat) (acc : List ABIValue) : Except String (List ABIValue × Nat) :=
        match ts with
        | [] => Except.ok (acc.reverse, off)
        | t :: rest =>
          match decode t data off with
          | Except.ok (v, newOff) => goStatic rest newOff (v :: acc)
          | Except.error e => Except.error e
      goStatic types offset []
    else
      let rec goDynamic (i : Nat) (vals : List ABIValue) (maxEnd : Nat) : Except String (List ABIValue × Nat) :=
        if i ≥ len then
          Except.ok (vals.reverse, maxEnd)
        else
          match types[i]? with
          | none => Except.error "tuple: index out of range"
          | some t =>
            let headOff := offset + i * 32
            if headOff + 32 > data.size then
              Except.error s!"tuple: data too short for head at offset {headOff}"
            else if isDynamic t then
              let rawOffset := bytesToNat (data.extract headOff (headOff + 32))
              let tailOff := offset + rawOffset
              match decode t data tailOff with
              | Except.ok (v, newOff) =>
                goDynamic (i + 1) (v :: vals) (max maxEnd newOff)
              | Except.error e => Except.error e
            else
              match decode t data headOff with
              | Except.ok (v, _) => goDynamic (i + 1) (v :: vals) maxEnd
              | Except.error e => Except.error e
      goDynamic 0 [] (offset + headAreaSize)

end

----------------------------------------------------------------------
-- Convenience: decode a list of arguments from calldata
----------------------------------------------------------------------

/-- Decode a list of types from the data as a tuple of args.
    Equivalent to `decode (.tuple types) data offset`. -/
def decodeArgs (types : List ABIType) (data : ByteArray) (offset : Nat := 0) : Except String (List ABIValue) :=
  match decodeTupleElems types data offset with
  | Except.ok (vals, _) => Except.ok vals
  | Except.error e => Except.error e

end EvmAbi.ABI.Decode
