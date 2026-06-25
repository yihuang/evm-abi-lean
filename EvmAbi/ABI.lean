/-
# ABI (Application Binary Interface) Core Types

This module defines the core types for Ethereum ABI encoding and decoding,
following the Solidity ABI Specification:
https://docs.soliditylang.org/en/latest/abi-spec.html
-/

namespace EvmAbi.ABI

open Nat

/-- ABI type description -/
inductive ABIType : Type where
  | uint (bits : Nat)       -- uint<N>, N ∈ {8,16,…,256}, N % 8 = 0
  | int (bits : Nat)        -- int<N>, same constraints
  | bool
  | bytesM (size : Nat)     -- bytes<M>, M ∈ [1,32]
  | address
  | bytes                   -- dynamic bytes
  | string
  | array (elem : ABIType) (size : Option Nat)  -- some n = fixed[n], none = dynamic[]
  | tuple (elems : List ABIType)
  deriving Repr, BEq

/-- ABI value — type info supplied separately to encode/decode -/
inductive ABIValue : Type where
  | uint (v : Nat)
  | int (v : Int)
  | bool (v : Bool)
  | bytes (v : ByteArray)
  | string (v : String)
  | address (v : ByteArray)
  | array (vals : List ABIValue)
  | tuple (vals : List ABIValue)
  deriving BEq

/-- ToString for ABIType -/
instance : ToString ABIType where
  toString t := (repr t).pretty 0

/-- Format a byte as a hex character -/
def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Format a ByteArray as a short hex string -/
def hexBytes (b : ByteArray) : String :=
  "0x" ++ b.foldl (fun acc byte =>
    acc ++ String.ofList [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]
  ) ""

/-- Recursive formatter for ABIValue (avoids Repr circularity) -/
partial def formatABIValue (v : ABIValue) : String :=
  match v with
  | .uint n => s!"uint({n})"
  | .int n => s!"int({n})"
  | .bool b => s!"bool({b})"
  | .bytes b => s!"bytes({hexBytes b})"
  | .string s => s!"string(\"{s}\")"
  | .address b => s!"address({hexBytes b})"
  | .array vs => "[" ++ String.join (List.intersperse ", " (vs.map formatABIValue)) ++ "]"
  | .tuple vs => "(" ++ String.join (List.intersperse ", " (vs.map formatABIValue)) ++ ")"

/-- Custom Repr for ABIValue to handle ByteArray hex display -/
instance : Repr ABIValue where
  reprPrec v _ := Std.format (formatABIValue v)

/-- Custom ToString for ABIValue -/
instance : ToString ABIValue where
  toString v := formatABIValue v
/-- Round `n` up to the nearest multiple of 32 -/
def roundUp32 (n : Nat) : Nat :=
  ((n + 31) / 32) * 32

/-- A zero byte -/
def zeroByte : UInt8 := 0

/-- Create a ByteArray filled with `n` zero bytes -/
def zeros (n : Nat) : ByteArray :=
  ByteArray.mk (Array.mk (List.replicate n zeroByte))

/-- Left-pad `b` to `n` bytes with zero bytes -/
def padLeft (b : ByteArray) (n : Nat) : ByteArray :=
  if h : n ≤ b.size then b else zeros (n - b.size) ++ b

/-- Right-pad `b` to `n` bytes with zero bytes -/
def padRight (b : ByteArray) (n : Nat) : ByteArray :=
  if h : n ≤ b.size then b else b ++ zeros (n - b.size)

/-- Encode a `Nat` as big-endian bytes (minimal representation, 0 → `#[0]`) -/
def natToBytes (v : Nat) : ByteArray :=
  if v = 0 then ByteArray.mk (Array.mk [zeroByte]) else
    let rec go (n : Nat) (acc : ByteArray) : ByteArray :=
      if n = 0 then acc else
        go (n / 256) (ByteArray.mk (Array.mk [((n % 256).toUInt8)]) ++ acc)
    go v ByteArray.empty

/-- Encode a `Nat` as a 32-byte big-endian uint256 -/
def uint256ToBytes (v : Nat) : ByteArray :=
  padLeft (natToBytes v) 32

/-- Encode a signed `Int` with `bits` bits as a 32-byte big-endian two's complement -/
def intToBytes (v : Int) (bits : Nat) : ByteArray :=
  if bits = 0 then zeros 32 else
    let pow2 := 2 ^ bits
    let unsigned : Nat :=
      if h : v ≥ 0 then v.toNat
      else ((pow2 : Int) + v).toNat
    padLeft (natToBytes unsigned) 32

/-- Decode big-endian bytes to a `Nat` -/
def bytesToNat (b : ByteArray) : Nat :=
  b.foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- Decode a signed integer from big-endian bytes with `bits` bits -/
def bytesToInt (b : ByteArray) (bits : Nat) : Except String Int :=
  if bits = 0 then
    Except.ok 0
  else
    let unsigned := bytesToNat b
    let pow2_m1 := 2 ^ (bits - 1)
    let pow2 := 2 ^ bits
    if unsigned < pow2_m1 then
      Except.ok (Int.ofNat unsigned)
    else if unsigned ≤ pow2 then
      Except.ok (-(Int.ofNat (pow2 - unsigned)))
    else
      Except.error s!"bytesToInt: value {unsigned} exceeds 2^{bits}"

/-- Check if an ABI type is dynamically sized -/
def isDynamic : ABIType → Bool
  | .bytes | .string => true
  | .array _ none => true
  | .array elem (some _) => isDynamic elem
  | .tuple [] => false
  | .tuple (e :: es) => isDynamic e || isDynamic (.tuple es)
  | _ => false

/-- Check if an ABI type is a tuple (for head/tail encoding) -/
def isTuple : ABIType → Bool
  | .tuple _ => true
  | _ => false

----------------------------------------------------------------------
-- Structural helpers
----------------------------------------------------------------------

/-- Size of the static head for a type when used in tuple/array context.
    For static types this is the encoded size; for dynamic types it's 32 (the offset word). -/
def headSize (type : ABIType) : Nat :=
  if isDynamic type then 32 else
    match type with
    | .uint _ | .int _ | .bool | .address => 32
    | .bytesM _ => 32
    | .array elem (some n) => n * headSize elem
    | .tuple [] => 0
    | .tuple (e :: es) => headSize e + headSize (.tuple es)
    | _ => 0

end EvmAbi.ABI
