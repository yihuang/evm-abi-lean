/-
# ABI Decoding via ABIVisitor
-/

import EvmAbi.ABI

open EvmAbi.ABI

namespace EvmAbi.ABI.Decode

/-- DecoderEntry t = decoder function for type t. -/
def DecoderEntry (_t : ABIType) : Type := ByteArray → Nat → Except Error (ABIValue × Nat)

/-- Decode dynamic bytes. -/
def decodeDynamicBytes (data : ByteArray) (offset : Nat) : Except Error (ABIValue × Nat) :=
  if offset + 32 > data.size then .error (.dataTooShortForLen offset)
  else
    let len := bytesToNat (data.extract offset (offset + 32))
    let dataStart := offset + 32
    if dataStart + len > data.size then .error (.dataTooShortForBytes dataStart len)
    else
      let val := data.extract dataStart (dataStart + len)
      let consumed := 32 + roundUp32 len
      .ok (.bytes val, offset + consumed)

/-- Decode dynamic string. -/
def decodeDynamicString (data : ByteArray) (offset : Nat) : Except Error (ABIValue × Nat) :=
  (decodeDynamicBytes data offset).map (λ (v, off) =>
    match v with
    | .bytes b => (.string (String.fromUTF8! b), off)
    | v => (v, off))

/-- Decode static array elements: sequential decode at advancing offsets.
    Inner loop with explicit termination on (n - i). -/
def decodeStaticElemsGo (dec : ByteArray → Nat → Except Error (ABIValue × Nat))
    (n : Nat) (i : Nat) (pos : Nat) (data : ByteArray) (acc : List ABIValue)
    : Except Error (List ABIValue × Nat) :=
  if _ : i < n then
    dec data pos >>= λ (v, newPos) =>
    decodeStaticElemsGo dec n (i + 1) newPos data (v :: acc)
  else .ok (acc.reverse, pos)
termination_by n - i
decreasing_by omega

def decodeStaticElems (dec : ByteArray → Nat → Except Error (ABIValue × Nat))
    (n : Nat) (data : ByteArray) (off : Nat) : Except Error (List ABIValue × Nat) :=
  decodeStaticElemsGo dec n 0 off data []

/-- Decode dynamic array elements: read head pointers, decode from tails.
    Inner loop with explicit termination on (n - i). -/
def decodeDynamicElemsGo (dec : ByteArray → Nat → Except Error (ABIValue × Nat))
    (n : Nat) (i : Nat) (off : Nat) (data : ByteArray) (vals : List ABIValue) (maxEnd : Nat)
    : Except Error (List ABIValue × Nat) :=
  if _ : i < n then
    let headOff := off + i * 32
    if headOff + 32 > data.size then .error (.dataTooShortForHead headOff)
    else
      let rawOffset := bytesToNat (data.extract headOff (headOff + 32))
      let tailOff := off + rawOffset
      dec data tailOff >>= λ (v, newOff) =>
      decodeDynamicElemsGo dec n (i + 1) off data (v :: vals) (max newOff maxEnd)
  else .ok (vals.reverse, maxEnd)
termination_by n - i
decreasing_by omega

def decodeDynamicElems (dec : ByteArray → Nat → Except Error (ABIValue × Nat))
    (n : Nat) (data : ByteArray) (off : Nat) : Except Error (List ABIValue × Nat) :=
  decodeDynamicElemsGo dec n 0 off data [] (off + n * 32)

/-- Decode array elements, dispatching on dynamic/static. -/
def decodeArrayElems (dec : ByteArray → Nat → Except Error (ABIValue × Nat))
    (isDyn : Bool) (n : Nat) (data : ByteArray) (off : Nat) : Except Error (List ABIValue × Nat) :=
  if isDyn then decodeDynamicElems dec n data off
  else decodeStaticElems dec n data off

/-- Decode all-static tuple: sequential decode. -/
def decodeTupleStatic (all : All DecoderEntry ts') (data : ByteArray) (off : Nat) (acc : List ABIValue)
    : Except Error (List ABIValue × Nat) :=
  match all with
  | All.nil => .ok (acc.reverse, off)
  | All.cons dec' rest =>
    dec' data off >>= λ (v, newOff) =>
    decodeTupleStatic rest data newOff (v :: acc)

/-- Decode mixed dynamic/static tuple: read heads, resolve tails. -/
def decodeTupleDynamic (all : All DecoderEntry ts') (fullTs : List ABIType) (ts : List ABIType) (data : ByteArray)
    (offset : Nat) (i : Nat) (acc : List ABIValue) (maxEnd : Nat)
    : Except Error (List ABIValue × Nat) :=
  match all, ts with
  | All.nil, [] => .ok (acc.reverse, maxEnd)
  | All.cons dec' rest, (t :: ts'') =>
    let headOff := offset + (fullTs.take i).foldl (λ acc t => acc + headSize t) 0
    if headOff + 32 > data.size then .error (.dataTooShortForHead headOff)
    else
      if isDynamic t then
        let rawOffset := bytesToNat (data.extract headOff (headOff + 32))
        let tailOff := offset + rawOffset
        dec' data tailOff >>= λ (v, newOff) =>
        decodeTupleDynamic rest fullTs ts'' data offset (i + 1) (v :: acc) (max maxEnd newOff)
      else
        dec' data headOff >>= λ (v, _) =>
        decodeTupleDynamic rest fullTs ts'' data offset (i + 1) (v :: acc) maxEnd
  | _, _ => .error .typeValueMismatch

/-- The ABIVisitor instance for decoding. -/
@[simp] instance instABIVisitorDecoderEntry: ABIVisitor DecoderEntry where
  onUint s := λ data offset =>
    if offset + 32 > data.size then .error (.dataTooShort "uint" offset)
    else
      let rawVal := bytesToNat (data.extract offset (offset + 32))
      let b := s.len * 8
      if rawVal ≥ 2 ^ b then .error (.uintDecodedExceeds b rawVal)
      else .ok (.uint rawVal, offset + 32)

  onInt s := λ data offset =>
    if offset + 32 > data.size then .error (.dataTooShort "int" offset)
    else
      let rawVal := bytesToNat (data.extract offset (offset + 32))
      let b := s.len * 8
      let masked := rawVal % (2 ^ b)
      let half := 2 ^ (b - 1)
      if masked < half then .ok (.int (Int.ofNat masked), offset + 32)
      else .ok (.int (-(Int.ofNat (2 ^ b - masked))), offset + 32)

  onBool := λ data offset =>
    if offset + 32 > data.size then .error (.dataTooShort "bool" offset)
    else
      let rawVal := bytesToNat (data.extract offset (offset + 32))
      if rawVal = 0 then .ok (.bool false, offset + 32)
      else if rawVal = 1 then .ok (.bool true, offset + 32)
      else .error (.boolInvalidValue rawVal)

  onAddress := λ data offset =>
    if offset + 32 > data.size then .error (.dataTooShort "address" offset)
    else
      let val := data.extract (offset + 12) (offset + 32)
      .ok (.address val, offset + 32)

  onFixedBytes s := λ data offset =>
    if offset + 32 > data.size then .error (.dataTooShort "bytes" offset)
    else
      let val := data.extract offset (offset + s.len)
      .ok (.bytes val, offset + 32)

  onBytes := decodeDynamicBytes
  onString := decodeDynamicString

  onArray {e} (dec : DecoderEntry e) : DecoderEntry (.array e) :=
    λ data offset =>
    if offset + 32 > data.size then .error (.dataTooShortForArrayLen offset)
    else
      let len := bytesToNat (data.extract offset (offset + 32))
      let arrayOffset := offset + 32
      decodeArrayElems dec (isDynamic e) len data arrayOffset >>= λ (vals, endOff) =>
      .ok (.array vals, endOff)

  onFixedArray n {e} (dec : DecoderEntry e) : DecoderEntry (.fixedArray n e) :=
    λ data offset =>
    decodeArrayElems dec (isDynamic e) n data offset >>= λ (vals, endOff) =>
    .ok (.array vals, endOff)

  onTuple {ts} (all : All DecoderEntry ts) : DecoderEntry (.tuple ts) :=
    λ data offset =>
    if !(ts.any isDynamic) then
      decodeTupleStatic all data offset [] >>= λ (vals, _) =>
      .ok (.tuple vals, offset + ts.foldl (λ acc t => acc + headSize t) 0)
    else
      let totalHeadSize := ts.foldl (λ acc t => acc + headSize t) 0
      decodeTupleDynamic all ts ts data offset 0 [] (offset + totalHeadSize) >>= λ (vals, endOff) =>
      .ok (.tuple vals, endOff)

/-- Decode any ABI value from bytes. -/
def decode (t : ABIType) (data : ByteArray) (offset : Nat := 0) : Except Error (ABIValue × Nat) :=
  foldABIType DecoderEntry t data offset

/-- Decode function arguments from a tuple encoding. -/
def decodeArgs (types : List ABIType) (data : ByteArray) (offset : Nat := 0) : Except Error (List ABIValue) :=
  decode (.tuple types) data offset >>= λ (v, _) =>
  match v with
  | .tuple vs => .ok vs
  | _ => .error .typeValueMismatch

end EvmAbi.ABI.Decode
