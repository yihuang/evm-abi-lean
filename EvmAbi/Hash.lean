/-
# Keccak-256 and the Ethereum Function Selector

Provides a pure Lean Keccak-256 hash implementation based on
FIPS PUB 202 (SHA-3) and the original Keccak specification.

The function selector is the first 4 bytes of Keccak-256(signature).
-/

import EvmAbi.ABI

namespace EvmAbi.Hash
open EvmAbi.ABI


----------------------------------------------------------------------
-- Keccak-f[1600] permutation
----------------------------------------------------------------------

/-- Round constants for Keccak-f[1600] (64-bit lanes, 24 rounds) -/
def roundConstants : List UInt64 := [
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
  0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
  0x8000000080008081, 0x8000000000008009, 0x000000000000008A,
  0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
  0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
  0x000000000000800A, 0x800000008000000A, 0x8000000080008081,
  0x8000000000008080, 0x0000000080000001, 0x8000000080008008
]

/-- Rotation offsets ρ[x][y] for 64-bit lane widths (from FIPS 202) -/
def rhoOffsets : List (Nat × Nat × Nat) := [
  (0,0, 0), (1,0, 1), (2,0,190), (3,0, 28), (4,0, 91),
  (0,1,36), (1,1,300), (2,1, 6), (3,1, 55), (4,1,276),
  (0,2, 3), (1,2, 10), (2,2,171), (3,2,153), (4,2,231),
  (0,3,105),(1,3, 45), (2,3, 15), (3,3, 21), (4,3,136),
  (0,4,210),(1,4, 66), (2,4,253), (3,4,120), (4,4, 78)
]

/-- Rotate a 64-bit word left by `n` bits (handles n ≥ 64 by taking n % 64) -/
def rotL (x : UInt64) (n : Nat) : UInt64 :=
  let n' := n % 64
  (x <<< n'.toUInt64) ||| (x >>> (64 - n').toUInt64)

/-- Build an Array UInt64 of size 25 filled with zeros -/
def emptyState : Array UInt64 :=
  Array.mk (List.replicate 25 0)

/-- θ step: diffusion -/
def keccakTheta (st : Array UInt64) : Array UInt64 :=
  let C : Array UInt64 := Array.mk <| List.range 5 |>.map fun x =>
    st[0*5 + x]! ^^^ st[1*5 + x]! ^^^ st[2*5 + x]! ^^^ st[3*5 + x]! ^^^ st[4*5 + x]!
  let D : Array UInt64 := Array.mk <| List.range 5 |>.map fun x =>
    C[(x + 4) % 5]! ^^^ rotL C[(x + 1) % 5]! 1
  Array.mk <| List.range 25 |>.map fun i =>
    st[i]! ^^^ D[i % 5]!

/-- ρ + π steps: rotation and rearrangement -/
def keccakRhoPi (st : Array UInt64) : Array UInt64 :=
  let init := emptyState
  rhoOffsets.foldl (fun (acc : Array UInt64) ((x, y, rot) : Nat × Nat × Nat) =>
    let idx := x + 5 * y
    let val := st[idx]!
    let rotated := rotL val rot
    -- π: B[(2x+3y)%5, x] = ROT(A[x][y], r[x][y]) per FIPS 202
    -- flat index: dest = y + 5*((2x+3y)%5)
    let newIdx := y + 5 * ((2 * x + 3 * y) % 5)
    acc.set! newIdx rotated
  ) init

/-- χ step: non-linear layer -/
def keccakChi (st : Array UInt64) : Array UInt64 :=
  Array.mk <| List.range 5 |>.flatMap fun y =>
    List.range 5 |>.map fun x =>
      let a := st[x + 5 * y]!
      let b1 := st[((x + 1) % 5) + 5 * y]!
      let b2 := st[((x + 2) % 5) + 5 * y]!
      a ^^^ ((~~~b1) &&& b2)

/-- ι step: add round constant -/
def keccakIota (st : Array UInt64) (round : Nat) : Array UInt64 :=
  match roundConstants[round]? with
  | some rc => st.set! 0 (st[0]! ^^^ rc)
  | none => st

/-- Single round of Keccak-f[1600] -/
def keccakRound (st : Array UInt64) (round : Nat) : Array UInt64 :=
  st |> keccakTheta |> keccakRhoPi |> keccakChi |> (fun s => keccakIota s round)

/-- Full Keccak-f[1600] permutation (24 rounds) -/
def keccakF1600 (st : Array UInt64) : Array UInt64 :=
  List.foldl (fun s r => keccakRound s r) st (List.range 24)

----------------------------------------------------------------------
-- Keccak sponge construction for 256-bit output
----------------------------------------------------------------------

/-- Rate (absorbed bytes per block) for Keccak-256: 1088 bits = 136 bytes -/
def rateBytes : Nat := 136

/-- Output size in bytes: 256 bits = 32 bytes -/
def outputBytes : Nat := 32

/-- Convert a ByteArray to an array of 25 UInt64 lanes (little-endian). -/
def bytesToLanes (b : ByteArray) : Array UInt64 :=
  let laneCount := Nat.min 25 ((b.size + 7) / 8)
  let lanesArray : Array UInt64 := Array.mk (List.replicate 25 0)
  List.range laneCount |>.foldl (fun (acc : Array UInt64) (i : Nat) =>
    let byteOff := i * 8
    let rec decodeLane (j : Nat) (laneVal : UInt64) : UInt64 :=
      if j ≥ 8 then laneVal
      else
        let byteIdx := byteOff + j
        if h : byteIdx < b.size then
          decodeLane (j + 1) (laneVal ||| ((b[byteIdx]!.toUInt64) <<< (8 * j).toUInt64))
        else
          decodeLane (j + 1) laneVal
    acc.set! i (decodeLane 0 0)
  ) lanesArray

/-- Convert an array of 25 UInt64 lanes to a ByteArray (little-endian). -/
def lanesToBytes (lanes : Array UInt64) : ByteArray :=
  let u8s : List UInt8 := List.range 25 |>.flatMap fun i =>
    let lane := lanes[i]!
    List.range 8 |>.map fun j =>
      ((lane >>> (8 * j).toUInt64) &&& 0xFF).toUInt8
  ByteArray.mk (Array.mk u8s)

/-- Compute Keccak-256 hash of `input` bytes. -/
def keccak256 (input : ByteArray) : ByteArray :=
  let padByte1 : UInt8 := 0x01
  let padByte2 : UInt8 := 0x80

  let totalLen := input.size + 2
  let blockCount := (totalLen + rateBytes - 1) / rateBytes
  let paddedSize := blockCount * rateBytes

  let state0 : Array UInt64 := emptyState

  let processBlock (st : Array UInt64) (blockIdx : Nat) : Array UInt64 :=
    let blockStart := blockIdx * rateBytes
    let blockBytes : ByteArray := ByteArray.mk <| Array.mk <| List.range rateBytes |>.map fun j =>
      let bytePos := blockStart + j
      if bytePos < input.size then
        input[bytePos]!
      else if bytePos = input.size then
        padByte1
      else if bytePos = paddedSize - 1 then
        padByte2
      else
        0
    let lanes := bytesToLanes blockBytes
    let newSt := Array.mk <| List.range 25 |>.map fun i =>
      st[i]! ^^^ lanes[i]!
    keccakF1600 newSt

  let afterAbsorb :=
    List.foldl (fun s bi => processBlock s bi) state0 (List.range blockCount)

  let stateBytes := lanesToBytes afterAbsorb
  stateBytes.extract 0 outputBytes

----------------------------------------------------------------------
-- Function Selector
----------------------------------------------------------------------

/-- Compute the 4-byte Ethereum function selector for a function signature.
    `signature` should be like `"transfer(address,uint256)"`. -/
def functionSelector (signature : String) : ByteArray :=
  let sigBytes := signature.toUTF8
  let hash := keccak256 sigBytes
  hash.extract 0 4

/- Format a function selector as a hex string -/
def selectorHex (sig : String) : String :=
  let sel := functionSelector sig
  "0x" ++ sel.foldl (fun acc byte =>
    acc ++ String.ofList [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]
  ) ""


end EvmAbi.Hash
