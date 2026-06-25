/-
# ABI Encoding

Implements Ethereum ABI encoding per the Solidity ABI specification.
https://docs.soliditylang.org/en/latest/abi-spec.html
-/

import EvmAbi.ABI

open EvmAbi.ABI

namespace EvmAbi.ABI.Encode

mutual

  /-- Encode a single ABI value according to its type.
      For dynamic types (bytes, string, dynamic arrays, dynamic tuples),
      this returns the full encoding including length prefixes. -/
  partial def encode (type : ABIType) (value : ABIValue) : Except String ByteArray :=
    match type, value with
    | .uint bits, .uint v =>
      if bits < 8 || bits % 8 ≠ 0 then
        Except.error s!"uint{bits}: bits must be a multiple of 8 and ≥ 8"
      else if v ≥ 2 ^ bits then
        Except.error s!"uint{bits}: value {v} exceeds 2^{bits}"
      else
        Except.ok (uint256ToBytes v)

    | .int bits, .int v =>
      if bits < 8 || bits % 8 ≠ 0 then
        Except.error s!"int{bits}: bits must be a multiple of 8 and ≥ 8"
      else
        let half := 2 ^ (bits - 1)
        if v < -(half : Int) || v ≥ (half : Int) then
          Except.error s!"int{bits}: value {v} out of range [{-half}, {half - 1}]"
        else
          Except.ok (intToBytes v bits)

    | .bool, .bool v =>
      Except.ok (uint256ToBytes (if v then 1 else 0))

    | .bytesM sz, .bytes v =>
      if v.size ≠ sz then
        Except.error s!"bytes{sz}: expected {sz} bytes, got {v.size}"
      else
        Except.ok (padRight v 32)

    | .address, .address v =>
      if v.size ≠ 20 then
        Except.error s!"address: expected 20 bytes, got {v.size}"
      else
        Except.ok (padLeft v 32)

    | .bytes, .bytes v =>
      Except.ok (uint256ToBytes v.size ++ padRight v (roundUp32 v.size))

    | .string, .string v =>
      let utf8 := v.toUTF8
      Except.ok (uint256ToBytes utf8.size ++ padRight utf8 (roundUp32 utf8.size))

    | .array elemType (some _), .array vals =>
      encodeFixedArray elemType vals

    | .array elemType none, .array vals =>
      match encodeFixedArray elemType vals with
      | Except.ok elemsEnc =>
        Except.ok (uint256ToBytes vals.length ++ elemsEnc)
      | Except.error e => Except.error e

    | .tuple elems, .tuple vals =>
      if elems.length ≠ vals.length then
        Except.error s!"tuple length mismatch: types {elems.length} vs values {vals.length}"
      else
        encodeTupleElems (List.zip elems vals)

    | _, _ =>
      Except.error s!"type/value mismatch"

  /-- Encode list of values all sharing the same element type.
      Uses head/tail encoding if the element type is dynamic. -/
  partial def encodeFixedArray (elemType : ABIType) (vals : List ABIValue) : Except String ByteArray :=
    if !isDynamic elemType then
      let rec goArray (vs : List ABIValue) (acc : ByteArray) : Except String ByteArray :=
        match vs with
        | [] => Except.ok acc
        | v :: rest =>
          match encode elemType v with
          | Except.ok enc => goArray rest (acc ++ enc)
          | Except.error e => Except.error e
      goArray vals ByteArray.empty
    else
      let len := vals.length
      let headAreaSize := len * 32
      let rec collectTails (vs : List ABIValue) (accTails : List ByteArray) : Except String (List ByteArray) :=
        match vs with
        | [] => Except.ok accTails.reverse
        | v :: rest =>
          match encode elemType v with
          | Except.ok tailEnc => collectTails rest (tailEnc :: accTails)
          | Except.error e => Except.error e
      match collectTails vals [] with
      | Except.ok tails =>
        let init : Nat × ByteArray × ByteArray := (headAreaSize, ByteArray.empty, ByteArray.empty)
        let (_, heads, tailsBytes) :=
          tails.foldl (fun (acc : Nat × ByteArray × ByteArray) (tailEnc : ByteArray) =>
            let (offset, heads, accTails) := acc
            (offset + roundUp32 tailEnc.size,
             heads ++ uint256ToBytes offset,
             accTails ++ tailEnc)
          ) init
        Except.ok (heads ++ tailsBytes)
      | Except.error e => Except.error e

  /-- Encode a list of (type, value) pairs as a tuple using ABI head/tail encoding.
      If all types are static, this is just the concat of their encodings.
      If any type is dynamic, uses offset-based head/tail. -/
  partial def encodeTupleElems (items : List (ABIType × ABIValue)) : Except String ByteArray :=
    let len := items.length
    let hasDynamic := items.any (fun (t, _) => isDynamic t)

    if !hasDynamic then
      let rec goTuple (xs : List (ABIType × ABIValue)) (acc : ByteArray) : Except String ByteArray :=
        match xs with
        | [] => Except.ok acc
        | (t, v) :: rest =>
          match encode t v with
          | Except.ok enc => goTuple rest (acc ++ enc)
          | Except.error e => Except.error e
      goTuple items ByteArray.empty
    else
      let headAreaSize := len * 32
      let rec classify (xs : List (ABIType × ABIValue))
          (acc : List (Bool × ByteArray × ByteArray)) : Except String (List (Bool × ByteArray × ByteArray)) :=
        match xs with
        | [] => Except.ok acc.reverse
        | (t, v) :: rest =>
          if isDynamic t then
            match encode t v with
            | Except.ok tailEnc => classify rest ((true, ByteArray.empty, tailEnc) :: acc)
            | Except.error e => Except.error e
          else
            match encode t v with
            | Except.ok headEnc => classify rest ((false, headEnc, ByteArray.empty) :: acc)
            | Except.error e => Except.error e
      match classify items [] with
      | Except.ok processed =>
        let init : Nat × ByteArray × ByteArray := (headAreaSize, ByteArray.empty, ByteArray.empty)
        let (_, heads, tails) :=
          processed.foldl (fun (acc : Nat × ByteArray × ByteArray) (elem : Bool × ByteArray × ByteArray) =>
            let (isDyn, head, tail) := elem
            let (offset, heads, tails) := acc
            if isDyn then
              (offset + roundUp32 tail.size,
               heads ++ uint256ToBytes offset,
               tails ++ tail)
            else
              (offset, heads ++ head, tails)
          ) init
        Except.ok (heads ++ tails)
      | Except.error e => Except.error e

end

----------------------------------------------------------------------
-- Convenience: encode a list of arguments matching a function signature
----------------------------------------------------------------------

/-- Encode a list of types and values as the calldata arguments.
    This is equivalent to encoding a tuple of the arguments. -/
def encodeArgs (types : List ABIType) (values : List ABIValue) : Except String ByteArray :=
  if types.length ≠ values.length then
    Except.error s!"argument count mismatch: {types.length} types vs {values.length} values"
  else
    encodeTupleElems (List.zip types values)

----------------------------------------------------------------------
-- Pretty-printing helpers
----------------------------------------------------------------------

/-- Format a byte as a hex character -/
def toHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Format bytes as a hex string with 0x prefix -/
def bytesToHex (b : ByteArray) : String :=
  "0x" ++ b.foldl (fun acc byte =>
    acc ++ String.ofList [toHexDigit (byte.toNat / 16), toHexDigit (byte.toNat % 16)]
  ) ""

end EvmAbi.ABI.Encode
