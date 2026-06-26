/-
# ABI (Application Binary Interface) Core Types
-/

namespace EvmAbi.ABI

open Nat


/-- A validated byte-length in the range (0, 32]. -/
structure ByteSize where
  len : Nat
  h : 0 < len ∧ len ≤ 32
  deriving Repr, BEq

namespace ByteSize

/-- Smart constructor: call with e.g. `ByteSize.ofLen 32 (by omega)`. -/
def ofLen (n : Nat) (h : 0 < n ∧ n ≤ 32) : ByteSize :=
  { len := n, h := h }

end ByteSize

inductive ABIType : Type where
  | uint (s : ByteSize)
  | int (s : ByteSize)
  | bool
  | bytesM (s : ByteSize)
  | address
  | bytes
  | string
  | array (elem : ABIType) (size : Option Nat)
  | tuple (elems : List ABIType)
  deriving Repr, BEq

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

instance : ToString ABIType where
  toString t := (repr t).pretty 0

def abiSize : ABIType → Nat
  | .uint _ => 1
  | .int _ => 1
  | .bool => 1
  | .bytesM _ => 1
  | .address => 1
  | .bytes => 1
  | .string => 1
  | .array e _ => 1 + abiSize e
  | .tuple es => 1 + es.foldl (fun acc t => acc + abiSize t) 0

theorem foldl_add_eq (a : Nat) : ∀ (xs : List ABIType),
    xs.foldl (fun acc t => acc + abiSize t) a = a + xs.foldl (fun acc t => acc + abiSize t) 0
  | [] => by simp
  | x :: xs => by
    simp
    rw [foldl_add_eq (a + abiSize x) xs, foldl_add_eq (abiSize x) xs]
    omega

theorem le_foldl_add (a : Nat) : ∀ (xs : List ABIType), a ≤ xs.foldl (fun acc t => acc + abiSize t) a
  | [] => Nat.le_refl a
  | x :: xs => by
    simp
    have h' : a + abiSize x ≤ xs.foldl (fun acc t => acc + abiSize t) (a + abiSize x) :=
      le_foldl_add (a + abiSize x) xs
    exact Nat.le_trans (Nat.le_add_right a (abiSize x)) h'

theorem mem_foldl_le (t : ABIType) (ts : List ABIType) (h : t ∈ ts) :
    abiSize t ≤ ts.foldl (fun acc t => acc + abiSize t) 0 := by
  induction ts with
  | nil => simp at h
  | cons x xs ih =>
    simp at h
    cases h with
    | inl h_eq =>
      rw [h_eq]
      simp
      exact le_foldl_add (abiSize x) xs
    | inr h_mem =>
      have h_ih := ih h_mem
      refine Nat.le_trans h_ih ?_
      simp
      rw [foldl_add_eq (abiSize x) xs, foldl_add_eq 0 xs]
      omega

theorem abiSize_lt_array (e : ABIType) (s : Option Nat) : abiSize e < abiSize (.array e s) := by
  simp [abiSize]

theorem abiSize_lt_tuple (t : ABIType) (ts : List ABIType) (h : t ∈ ts) : abiSize t < abiSize (.tuple ts) := by
  simp [abiSize]
  have hle : abiSize t ≤ ts.foldl (fun acc t => acc + abiSize t) 0 :=
    mem_foldl_le t ts h
  apply Nat.lt_of_le_of_lt hle
  omega

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

def uint256ToBytes (v : Nat) : ByteArray :=
  padLeft (natToBytes v) 32

def intToBytes (v : Int) (byteLen : Nat) : ByteArray :=
  let b := byteLen * 8
  let pow2 := 2 ^ b
  let unsigned : Nat :=
    if v ≥ 0 then v.toNat
    else ((pow2 : Int) + v).toNat
  if v ≥ 0 then
    padLeft (natToBytes unsigned) 32
  else
    let raw := natToBytes unsigned
    ByteArray.mk (Array.mk (List.replicate (32 - raw.size) 0xFF)) ++ raw

def bytesToNat_list : List UInt8 → Nat :=
  List.foldl (λ acc b => acc * 256 + b.toNat) 0

def bytesToNat (b : ByteArray) : Nat :=
  bytesToNat_list b.data.toList

def bytesToInt (b : ByteArray) (byteLen : Nat) : Except String Int :=
  let bv := byteLen * 8
  let unsigned := bytesToNat b
  let pow2_m1 := 2 ^ (bv - 1)
  let pow2 := 2 ^ bv
  if unsigned < pow2_m1 then
    Except.ok (Int.ofNat unsigned)
  else if unsigned ≤ pow2 then
    Except.ok (-(Int.ofNat (pow2 - unsigned)))
  else
    Except.error s!"bytesToInt: value {unsigned} exceeds 2^{bv}"

def isDynamic : ABIType → Bool
  | .bytes | .string => true
  | .array _ none => true
  | .array elem (some _) => isDynamic elem
  | .tuple [] => false
  | .tuple (e :: es) => isDynamic e || isDynamic (.tuple es)
  | _ => false

def isTuple : ABIType → Bool
  | .tuple _ => true
  | _ => false

def isAtomic : ABIType → Bool
  | .array _ _ | .tuple _ | .bytes | .string => false
  | _ => true

def headSize (type : ABIType) : Nat :=
  if isDynamic type then 32 else
    match type with
    | .uint _ | .int _ | .bool | .address => 32
    | .bytesM _ => 32
    | .array elem (some n) => n * headSize elem
    | .tuple [] => 0
    | .tuple (e :: es) => headSize e + headSize (.tuple es)
    | _ => 0

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
