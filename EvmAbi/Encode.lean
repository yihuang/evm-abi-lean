/-
# ABI Encoding via ABIVisitor
-/

import EvmAbi.ABI

open EvmAbi.ABI

namespace EvmAbi.ABI.Encode

/-- EncoderEntry t = (isDynamic, encoder function) for type t. -/
def EncoderEntry (_t : ABIType) : Type := Bool × (ABIValue → Except Error ByteArray)

/-- Pack encoded array elements. -/
def arrayPack (elemDynamic : Bool) (encoded : List ByteArray) : ByteArray :=
  if !elemDynamic then
    encoded.foldl (· ++ ·) ByteArray.empty
  else
    let headAreaSize := if encoded.length = 0 then 32 else encoded.length * 32
    let init : Nat × ByteArray × ByteArray := (headAreaSize, ByteArray.empty, ByteArray.empty)
    let (_, heads, tails) :=
      List.foldl (λ (acc : Nat × ByteArray × ByteArray) (enc : ByteArray) =>
        let (offset, heads, accTails) := acc
        (offset + roundUp32 enc.size, heads ++ uint256ToBytes offset, accTails ++ enc)
      ) init encoded
    heads ++ tails

/-- Pack tuple elements. -/
def tuplePack (headSizes : List Nat) (dynamics : List Bool) (encoded : List (Bool × ByteArray)) : ByteArray :=
  if !(dynamics.any id) then
    encoded.foldl (λ acc (_, enc) => acc ++ enc) ByteArray.empty
  else
    let headAreaSize := headSizes.foldl (· + ·) 0
    let init : Nat × ByteArray × ByteArray := (headAreaSize, ByteArray.empty, ByteArray.empty)
    let (_, heads, tails) :=
      List.foldl (λ (acc : Nat × ByteArray × ByteArray) ((isDyn, enc) : Bool × ByteArray) =>
        let (offset, heads, accTails) := acc
        if isDyn then (offset + roundUp32 enc.size, heads ++ uint256ToBytes offset, accTails ++ enc)
        else (offset, heads ++ enc, accTails)
      ) init encoded
    heads ++ tails

/-- The ABIVisitor instance for encoding. -/
instance : ABIVisitor EncoderEntry where
  onUint s := (false, λ v => match v with
    | .uint v' =>
      let b := s.len * 8
      if v' < 2 ^ b then .ok (uint256ToBytes v')
      else .error (.uintExceeds b v')
    | _ => .error .typeValueMismatch)

  onInt s := (false, λ v => match v with
    | .int v' =>
      let b := s.len * 8
      let half := 2 ^ (b - 1)
      if v' < -(half : Int) || v' ≥ (half : Int) then
        .error (.intOutOfRange b v')
      else .ok (intToBytes v' s.len)
    | _ => .error .typeValueMismatch)

  onBool := (false, λ v => match v with
    | .bool v' => .ok (uint256ToBytes (if v' then 1 else 0))
    | _ => .error .typeValueMismatch)

  onAddress := (false, λ v => match v with
    | .address v' =>
      if v'.size = 20 then .ok (padLeft v' 32)
      else .error (.addressSize v'.size)
    | _ => .error .typeValueMismatch)

  onFixedBytes s := (false, λ v => match v with
    | .bytes v' =>
      if v'.size = s.len then .ok (padRight v' 32)
      else .error (.fixedBytesSize s.len v'.size)
    | _ => .error .typeValueMismatch)

  onBytes := (true, λ v => match v with
    | .bytes v' =>
      if v'.size < 2 ^ 256 then
        .ok (uint256ToBytes v'.size ++ padRight v' (roundUp32 v'.size))
      else .error (.dataTooLong v'.size)
    | _ => .error .typeValueMismatch)

  onString := (true, λ v => match v with
    | .string v' =>
      let utf8 := v'.toUTF8
      if utf8.size < 2 ^ 256 then
        .ok (uint256ToBytes utf8.size ++ padRight utf8 (roundUp32 utf8.size))
      else .error (.dataTooLong utf8.size)
    | _ => .error .typeValueMismatch)

  onArray {e} (entry : EncoderEntry e) : EncoderEntry (.array e) :=
    let (elemDyn, elemEnc) := entry
    (true, λ v => match v with
    | .array vals =>
      if _ : vals.length < 2 ^ 256 then
        let encoded : Except Error (List ByteArray) :=
          vals.foldr (λ v acc => (elemEnc v) >>= λ encd => acc >>= λ rest => .ok (encd :: rest)) (.ok [])
        encoded >>= λ encd =>
        let packed := arrayPack elemDyn encd
        .ok (uint256ToBytes vals.length ++ packed)
      else .error (.arrayLengthOverflow vals.length)
    | _ => .error .typeValueMismatch)

  onFixedArray n {e} (entry : EncoderEntry e) : EncoderEntry (.fixedArray n e) :=
    let (elemDyn, elemEnc) := entry
    (elemDyn, λ v => match v with
    | .array vals =>
      if vals.length ≠ n then .error (.arrayElemCount n vals.length)
      else
        let encoded : Except Error (List ByteArray) :=
          vals.foldr (λ v acc => (elemEnc v) >>= λ encd => acc >>= λ rest => .ok (encd :: rest)) (.ok [])
        encoded >>= λ encd =>
        .ok (arrayPack elemDyn encd)
    | _ => .error .typeValueMismatch)

  onTuple {ts} (all : All EncoderEntry ts) : EncoderEntry (.tuple ts) :=
    let headSizes := ts.map headSize
    let dynamics := ts.map isDynamic
    let hasDynamic := dynamics.any id
    (hasDynamic, λ v => match v with
    | .tuple vs =>
      let rec go (types' : List ABIType) (all' : All EncoderEntry types') (vals : List ABIValue)
          : Except Error (List (Bool × ByteArray)) :=
        match types', all', vals with
        | [], All.nil, [] => .ok []
        | (_ :: ts''), All.cons (dyn, enc) rest, v :: vs' =>
          (enc v) >>= λ bytes =>
          go ts'' rest vs' >>= λ tail => .ok ((dyn, bytes) :: tail)
        | _, _, _ => .error .typeValueMismatch
      go ts all vs >>= λ encd =>
      .ok (tuplePack headSizes dynamics encd)
    | _ => .error .typeValueMismatch)

/-- Encode any ABI value given its type. -/
def encode (t : ABIType) (v : ABIValue) : Except Error ByteArray :=
  (foldABIType EncoderEntry t).2 v

/-- Encode function arguments as a tuple. -/
def encodeArgs (types : List ABIType) (values : List ABIValue) : Except Error ByteArray :=
  if types.length ≠ values.length then
    .error (.argCountMismatch types.length values.length)
  else
    encode (.tuple types) (.tuple values)

end EvmAbi.ABI.Encode
