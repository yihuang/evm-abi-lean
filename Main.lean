import EvmAbi

open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode
open EvmAbi.Hash

/-- Helper: create ByteArray from a list of UInt8 -/
def bytes (xs : List UInt8) : ByteArray :=
  ByteArray.mk (Array.mk xs)

/-- Encode and print a single value -/
partial def tryEncode (t : ABIType) (v : ABIValue) : IO Unit :=
  match encode t v with
  | Except.ok enc => do
    IO.println s!"  {repr t} = {v}"
    IO.println s!"  → {bytesToHex enc} ({enc.size} bytes)"
  | Except.error e =>
    IO.println s!"  ERROR: {e}"

/-- Decode and print -/
partial def tryDecode (t : ABIType) (desc : String) (data : ByteArray) : IO Unit :=
  match decode t data 0 with
  | Except.ok (v, _) => do
    IO.println s!"  {desc}: decoded = {v}"
  | Except.error e =>
    IO.println s!"  ERROR: {e}"

def main : IO Unit := do
  IO.println "=== ABILean: EVM ABI Encode/Decode ===\n"

  -- ── Static types ──
  IO.println "1) Static uint256 encoding:"
  tryEncode (.uint .w256) (.uint 42)

  IO.println "\n2) Bool encoding:"
  tryEncode .bool (.bool true)

  IO.println "\n3) Address encoding:"
  tryEncode .address (.address (bytes (List.replicate 20 0x42)))

  -- ── Dynamic types ──
  IO.println "\n4) Dynamic bytes encoding:"
  tryEncode .bytes (.bytes (bytes (List.range 5 |>.map fun i => (i + 1).toUInt8)))

  IO.println "\n5) String encoding:"
  tryEncode .string (.string "hello")

  -- ── Arrays ──
  IO.println "\n6) Fixed array uint256[3]:"
  tryEncode (.array (.uint .w256) (some 3))
    (.array [.uint 1, .uint 2, .uint 3])

  IO.println "\n7) Dynamic array uint256[]:"
  tryEncode (.array (.uint .w256) none)
    (.array [.uint 10, .uint 20])

  -- ── Tuples ──
  IO.println "\n8) Tuple (uint256, address, bool):"
  tryEncode (.tuple [.uint .w256, .address, .bool])
    (.tuple [.uint 123, .address (bytes (List.replicate 20 0xAB)), .bool false])

  -- ── Roundtrip: encode then decode ──
  IO.println "\n9) Roundtrip uint256(42):"
  match encode (.uint .w256) (.uint 42) with
  | Except.ok encoded =>
    IO.println s!"  encoded = {bytesToHex encoded}"
    match decode (.uint .w256) encoded 0 with
    | Except.ok (decoded, _) =>
      IO.println s!"  decoded = {decoded}"
    | Except.error e => IO.println s!"  decode error: {e}"
  | Except.error e => IO.println s!"  encode error: {e}"

  IO.println "\n10) Roundtrip tuple (uint256, bytes):"
  let tupleType := .tuple [.uint .w256, .bytes]
  let tupleVal := .tuple [.uint 999, .bytes (bytes [0xDE, 0xAD, 0xBE, 0xEF])]
  match encode tupleType tupleVal with
  | Except.ok enc2 =>
    IO.println s!"  encoded = {bytesToHex enc2} ({enc2.size} bytes)"
    match decode tupleType enc2 0 with
    | Except.ok (dec2, _) =>
      IO.println s!"  decoded = {dec2}"
    | Except.error e => IO.println s!"  decode error: {e}"
  | Except.error e => IO.println s!"  encode error: {e}"

  -- ── Function selector ──
  IO.println "\n11) Function selectors:"
  IO.println s!"  transfer(address,uint256): {selectorHex "transfer(address,uint256)"}"
  IO.println s!"  balanceOf(address):       {selectorHex "balanceOf(address)"}"
  IO.println s!"  approve(address,uint256): {selectorHex "approve(address,uint256)"}"

  IO.println "\n=== All done! ==="
