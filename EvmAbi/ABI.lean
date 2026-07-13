/-
# ABI (Application Binary Interface) Core Types

Uses the ABIVisitor catamorphism (structural fold) pattern.
-/

namespace EvmAbi.ABI

open Nat

/-- Structured error type for ABI encoding/decoding operations. -/
inductive Error : Type where
  | uintExceeds (bits : Nat) (value : Nat)
  | intOutOfRange (bits : Nat) (value : Int)
  | fixedBytesSize (expected : Nat) (actual : Nat)
  | addressSize (actual : Nat)
  | dataTooLong (size : Nat)
  | arrayElemCount (expected : Nat) (actual : Nat)
  | arrayLengthOverflow (length : Nat)
  | typeValueMismatch
  | argCountMismatch (types : Nat) (values : Nat)
  | dataTooShortForLen (offset : Nat)
  | dataTooShortForBytes (offset : Nat) (len : Nat)
  | dataTooShort (ty : String) (offset : Nat)
  | uintDecodedExceeds (bits : Nat) (value : Nat)
  | boolInvalidValue (value : Nat)
  | dataTooShortForHead (offset : Nat)
  | dataTooShortForArrayLen (offset : Nat)
  | bytesToIntOverflow (value : Nat) (bits : Nat)
  deriving Repr

instance : ToString Error where
  toString
    | .uintExceeds bits v => s!"uint{bits}: value {v} exceeds 2^{bits}"
    | .intOutOfRange bits v => s!"int{bits}: value {v} out of range"
    | .fixedBytesSize exp act => s!"bytes{exp}: expected {exp} bytes, got {act}"
    | .addressSize act => s!"address: expected 20 bytes, got {act}"
    | .dataTooLong sz => s!"data too long ({sz} bytes)"
    | .arrayElemCount exp act => s!"array: expected {exp} elements, got {act}"
    | .arrayLengthOverflow len => s!"array[]: length {len} exceeds 2^256"
    | .typeValueMismatch => "type/value mismatch"
    | .argCountMismatch nt nv => s!"argument count mismatch: {nt} types vs {nv} values"
    | .dataTooShortForLen off => s!"bytes: data too short for length at offset {off}"
    | .dataTooShortForBytes off len => s!"bytes: data too short for {len} bytes at offset {off}"
    | .dataTooShort ty off => s!"{ty}: data too short at offset {off}"
    | .uintDecodedExceeds bits v => s!"uint{bits}: decoded value {v} exceeds 2^{bits}"
    | .boolInvalidValue v => s!"bool: invalid value {v}, expected 0 or 1"
    | .dataTooShortForHead off => s!"array/tuple: data too short for head at offset {off}"
    | .dataTooShortForArrayLen off => s!"array[]: data too short for length at offset {off}"
    | .bytesToIntOverflow v bits => s!"bytesToInt: value {v} exceeds 2^{bits}"

/-- A validated byte-length in the range (0, 32]. -/
structure ByteSize where
  len : Nat
  h : 0 < len ∧ len ≤ 32
  deriving Repr, BEq

namespace ByteSize
def ofLen (n : Nat) (h : 0 < n ∧ n ≤ 32) : ByteSize :=
  { len := n, h := h }
end ByteSize

/-- ABI type with ByteSize for uint/int/bytes widths. -/
inductive ABIType : Type where
  | uint         (s : ByteSize)
  | int          (s : ByteSize)
  | bool
  | address
  | bytes                     -- dynamic bytes
  | fixedBytes   (s : ByteSize)  -- fixed bytes N
  | string
  | array        (elem : ABIType)             -- dynamic T[]
  | fixedArray   (n : Nat) (elem : ABIType)   -- fixed T[n]
  | tuple        (elems : List ABIType)
  deriving Repr, BEq

/-- ABI value. -/
inductive ABIValue : Type where
  | uint    (v : Nat)
  | int     (v : Int)
  | bool    (v : Bool)
  | bytes   (v : ByteArray)
  | string  (v : String)
  | address (v : ByteArray)
  | array   (vals : List ABIValue)
  | tuple   (vals : List ABIValue)
  deriving BEq

/-! ## All — heterogeneous list for ABIVisitor, helper for ABIVisitor -/

inductive All (φ : ABIType → Type) : List ABIType → Type where
  | nil  : All φ []
  | cons : φ t → All φ ts → All φ (t :: ts)

/-! ## ABIVisitor — catamorphism over ABIType -/

class ABIVisitor (φ : ABIType → Type) where
  onUint         : (s : ByteSize) → φ (.uint s)
  onInt          : (s : ByteSize) → φ (.int s)
  onBool         : φ .bool
  onAddress      : φ .address
  onBytes        : φ .bytes
  onFixedBytes   : (s : ByteSize) → φ (.fixedBytes s)
  onString       : φ .string
  onArray        : {e : ABIType} → φ e → φ (.array e)
  onFixedArray   : (n : Nat) → {e : ABIType} → φ e → φ (.fixedArray n e)
  onTuple        : {ts : List ABIType} → All φ ts → φ (.tuple ts)

/-! ## Simple properties -/

mutual

  -- same as List.any isDynamic, but defined recursively for termination checking
  def isDynamicList : List ABIType → Bool
    | [] => false
    | e :: es => isDynamic e || isDynamicList es

  @[simp, grind =] def isDynamic : ABIType → Bool
    | .bytes | .string | .array _ => true
    | .fixedArray _ e => isDynamic e
    | .tuple es       => isDynamicList es
    | _ => false

end

@[simp, grind =] theorem isDynamicList_eq_any (ts : List ABIType) :
    isDynamicList ts = ts.any isDynamic := by
  induction ts with
  | nil => simp [isDynamicList]
  | cons t ts ih => grind [isDynamicList]

/-- ABI "head" size of a type when it appears as a tuple/array element: a dynamic
    type always occupies a 32-byte offset pointer in the head; a static type occupies
    its full (static) encoding size. -/
@[simp, grind =] def headSize (t : ABIType) : Nat :=
  if isDynamic t then 32 else
    match t with
    | .fixedArray n e => n * headSize e
    | .tuple []       => 0
    | .tuple (t'::ts) => headSize t' + headSize (.tuple ts)
    | _               => 32

/-! ## Termination lemmas for foldABIType (using sizeOf) -/

mutual

  @[simp] def foldABIType (φ : ABIType → Type) [inst : ABIVisitor φ] (t : ABIType) : φ t :=
    match t with
    | .uint s         => inst.onUint s
    | .int s          => inst.onInt s
    | .bool           => inst.onBool
    | .address        => inst.onAddress
    | .bytes         => inst.onBytes
    | .fixedBytes s  => inst.onFixedBytes s
    | .string         => inst.onString
    | .array e        => inst.onArray (foldABIType φ e)
    | .fixedArray n e => inst.onFixedArray n (foldABIType φ e)
    | .tuple ts       => inst.onTuple (foldAll φ ts)

  def foldAll (φ : ABIType → Type) [inst : ABIVisitor φ] (types : List ABIType) : All φ types :=
    match types with
    | []    => All.nil
    | t::ts => All.cons (foldABIType φ t) (foldAll φ ts)

end

/-! ## Byte helpers -/

def roundUp32 (n : Nat) : Nat := ((n + 31) / 32) * 32

def zeroByte : UInt8 := 0
def zeros (n : Nat) : ByteArray :=
  ByteArray.mk (Array.mk (List.replicate n zeroByte))

def padLeft (b : ByteArray) (n : Nat) : ByteArray :=
  if n ≤ b.size then b else zeros (n - b.size) ++ b

def padRight (b : ByteArray) (n : Nat) : ByteArray :=
  if n ≤ b.size then b else b ++ zeros (n - b.size)

def natToBytes (v : Nat) : ByteArray :=
  if v = 0 then ByteArray.mk (Array.mk [zeroByte]) else
    let rec go (n : Nat) (acc : ByteArray) : ByteArray :=
      if n = 0 then acc else
        go (n / 256) (ByteArray.mk (Array.mk [((n % 256).toUInt8)]) ++ acc)
    go v ByteArray.empty

def uint256ToBytes (v : Nat) : ByteArray := padLeft (natToBytes v) 32

def intToBytes (v : Int) (byteLen : Nat) : ByteArray :=
  let b := byteLen * 8
  let pow2 := 2 ^ b
  let unsigned : Nat :=
    if v ≥ 0 then v.toNat
    else ((pow2 : Int) + v).toNat
  if v ≥ 0 then padLeft (natToBytes unsigned) 32
  else ByteArray.mk (Array.mk (List.replicate (32 - (natToBytes unsigned).size) 0xFF)) ++ natToBytes unsigned

def bytesToNat_list : List UInt8 → Nat :=
  List.foldl (λ acc b => acc * 256 + b.toNat) 0

def bytesToNat (b : ByteArray) : Nat := bytesToNat_list b.data.toList

def bytesToInt (b : ByteArray) (byteLen : Nat) : Except Error Int :=
  let bv := byteLen * 8
  let unsigned := bytesToNat b
  let pow2_m1 := 2 ^ (bv - 1)
  let pow2 := 2 ^ bv
  if unsigned < pow2_m1 then .ok (Int.ofNat unsigned)
  else if unsigned ≤ pow2 then .ok (-(Int.ofNat (pow2 - unsigned)))
  else .error (.bytesToIntOverflow unsigned bv)

/-! ## Formatting -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hexBytes (b : ByteArray) : String :=
  "0x" ++ b.foldl (fun acc byte =>
    acc ++ String.ofList [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]
  ) ""

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

instance : Repr ABIValue where
  reprPrec v _ := Std.format (formatABIValue v)

instance : ToString ABIValue where
  toString v := formatABIValue v

end EvmAbi.ABI
