/-
# ABI Test Suite

Tests for EVM ABI encoding/decoding based on the Solidity ABI Specification:
https://docs.soliditylang.org/en/latest/abi-spec.html

Covers all test vectors and properties from the official spec.
-/

import EvmAbi
open EvmAbi.ABI
open EvmAbi.ABI.Encode
open EvmAbi.ABI.Decode
open EvmAbi.Hash

----------------------------------------------------------------------
-- Helpers
----------------------------------------------------------------------

/-- Parse a hex string like "0xabcd" into a ByteArray. Character-by-character. -/
def parseHex (s : String) : ByteArray :=
  let clean := (if s.startsWith "0x" then (s.drop 2).toString else s)
  let chars := clean.toList
  let rec go (cs : List Char) (acc : List UInt8) : ByteArray :=
    match cs with
    | [] => ByteArray.mk (Array.mk acc.reverse)
    | h :: t :: rest =>
      let hiVal := if h ≥ 'a' then h.toNat - 87 else if h ≥ 'A' then h.toNat - 55 else h.toNat - 48
      let loVal := if t ≥ 'a' then t.toNat - 87 else if t ≥ 'A' then t.toNat - 55 else t.toNat - 48
      go rest (((hiVal * 16) + loVal).toUInt8 :: acc)
    | _ => ByteArray.mk (Array.mk acc.reverse)
  go chars []

/-- Make ByteArray from a list -/
def bytes (xs : List UInt8) : ByteArray := ByteArray.mk (Array.mk xs)

/-- ABI type shorthands so test literals read like their Solidity signatures. -/
def u256 : ABIType := .uint (ByteSize.ofLen 32 (by omega))
def u32 : ABIType := .uint (ByteSize.ofLen 4 (by omega))
def u8 : ABIType := .uint (ByteSize.ofLen 1 (by omega))
def i256 : ABIType := .int (ByteSize.ofLen 32 (by omega))
def i8 : ABIType := .int (ByteSize.ofLen 1 (by omega))
def bytes1Ty : ABIType := .fixedBytes (ByteSize.ofLen 1 (by omega))
def bytes3Ty : ABIType := .fixedBytes (ByteSize.ofLen 3 (by omega))
def bytes4Ty : ABIType := .fixedBytes (ByteSize.ofLen 4 (by omega))
def bytes10Ty : ABIType := .fixedBytes (ByteSize.ofLen 10 (by omega))
def bytes32Ty : ABIType := .fixedBytes (ByteSize.ofLen 32 (by omega))

/-- A test result -/
inductive TestResult where
  | pass (label : String)
  | fail (label : String) (msg : String)
  deriving Repr

instance : ToString TestResult where
  toString
    | .pass l => s!"  ✓ {l}"
    | .fail l m => s!"  ✗ {l}: {m}"

/-- Count passed tests -/
def countPassed (results : List TestResult) : Nat :=
  (results.filter (fun r => match r with | .pass _ => true | _ => false)).length

/-- Encode a value, handling tuple encoding correctly -/
def encodeTest (t : ABIType) (v : ABIValue) : Except Error ByteArray :=
  match t with
  | .tuple es => encodeArgs es (match v with | .tuple vs => vs | _ => [])
  | _ => encode t v

/-- Assert that encode produces the expected hex string -/
def assertEncodes (label : String) (t : ABIType) (v : ABIValue) (expectedHex : String) : IO TestResult := do
  let enc := encodeTest t v
  match enc with
  | Except.ok enc =>
    let expected := parseHex expectedHex
    if enc == expected then
      pure (.pass label)
    else
      pure (.fail label s!"got {hexBytes enc}, expected {expectedHex}")
  | Except.error e =>
    pure (.fail label s!"encode error: {e}")

/-- Assert that encode-decode roundtrip preserves the value -/
def assertRoundtrip (label : String) (t : ABIType) (v : ABIValue) : IO TestResult := do
  let enc := encodeTest t v
  match enc with
  | Except.ok enc =>
    match decode t enc 0 with
    | Except.ok (v', _) =>
      if v' == v then pure (.pass label)
      else pure (.fail label s!"value mismatch: {v} ≠ {v'}")
    | Except.error e =>
      pure (.fail label s!"decode error: {e}")
  | Except.error e =>
    pure (.fail label s!"encode error: {e}")

/-- Assert both encode-to-hex and encode/decode roundtrip for one `t`/`v`,
writing the (often multi-line) type and value literal exactly once. -/
def assertEncDecRT (label : String) (t : ABIType) (v : ABIValue) (expectedHex : String) : List (IO TestResult) :=
  [assertEncodes s!"{label} encode" t v expectedHex, assertRoundtrip s!"{label} roundtrip" t v]

/-- Assert selector matches -/
def assertSelector (label : String) (sig : String) (expectedHex : String) : IO TestResult := do
  let sel := functionSelector sig
  let expected := parseHex expectedHex
  if sel == expected then
    pure (.pass label)
  else
    pure (.fail label s!"got {hexBytes sel}, expected {expectedHex}")

/-- Assert decode produces the expected value -/
def assertDecodes (label : String) (t : ABIType) (dataHex : String) (expected : ABIValue) : IO TestResult := do
  let data := parseHex dataHex
  match decode t data 0 with
  | Except.ok (v, _) =>
    if v == expected then pure (.pass label)
    else pure (.fail label s!"got {v}, expected {expected}")
  | Except.error e =>
    pure (.fail label s!"decode error: {e}")

/-- Assert encode returns an error -/
def assertEncodeError (label : String) (t : ABIType) (v : ABIValue) : IO TestResult := do
  match encode t v with
  | Except.ok _ => pure (.fail label "expected error, got success")
  | Except.error _ => pure (.pass label)

/-- Assert decode returns an error -/
def assertDecodeError (label : String) (t : ABIType) (data : ByteArray) : IO TestResult := do
  match decode t data 0 with
  | Except.ok _ => pure (.fail label "expected error, got success")
  | Except.error _ => pure (.pass label)

/-- Run a group of tests -/
def runGroup (name : String) (tests : List (IO TestResult)) : IO Nat := do
  IO.println s!"\n=== {name} ==="
  let results ← tests.mapM id
  let passed := countPassed results
  let total := results.length
  for r in results do
    IO.println (toString r)
  IO.println s!"  [{passed}/{total} passed]"
  pure (total - passed)

----------------------------------------------------------------------
-- Test lists — each group returns a List (IO TestResult)
----------------------------------------------------------------------

def testFunctionSelectors : List (IO TestResult) := [
  assertSelector "bar(bytes3[2])"          "bar(bytes3[2])"          "0xfce353f6",
  assertSelector "baz(uint32,bool)"         "baz(uint32,bool)"        "0xcdcd77c0",
  assertSelector "sam(bytes,bool,uint256[])" "sam(bytes,bool,uint256[])" "0xa5643bf2",
  assertSelector "f(uint256,uint32[],bytes10,bytes)" "f(uint256,uint32[],bytes10,bytes)" "0x8be65246",
  assertSelector "g(uint256[][],string[])"  "g(uint256[][],string[])" "0x2289b18c",
  assertSelector "transfer(address,uint256)" "transfer(address,uint256)" "0xa9059cbb",
  assertSelector "balanceOf(address)"        "balanceOf(address)"      "0x70a08231",
  assertSelector "approve(address,uint256)"  "approve(address,uint256)" "0x095ea7b3",
  assertSelector "totalSupply()"             "totalSupply()"           "0x18160ddd",
  assertSelector "transferFrom(address,address,uint256)" "transferFrom(address,address,uint256)" "0x23b872dd",
  assertSelector "allowance(address,address)" "allowance(address,address)" "0xdd62ed3e",
  assertSelector "safeTransferFrom(address,address,uint256)" "safeTransferFrom(address,address,uint256)" "0x42842e0e",
]

def testStaticTypes : List (IO TestResult) := [
  assertEncodes "uint256(0)" u256 ((.uint 0)) "0x0000000000000000000000000000000000000000000000000000000000000000",
  assertEncodes "uint256(1)" u256 ((.uint 1)) "0x0000000000000000000000000000000000000000000000000000000000000001",
  assertEncodes "uint256(42)" u256 ((.uint 42)) "0x000000000000000000000000000000000000000000000000000000000000002a",
  assertEncodes "uint256(max)" u256 (.uint (2^256 - 1)) "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
  assertEncodes "uint8(255)" u8 ((.uint 255)) "0x00000000000000000000000000000000000000000000000000000000000000ff",
  assertEncodes "int256(0)" i256 ((.int 0)) "0x0000000000000000000000000000000000000000000000000000000000000000",
  assertEncodes "int256(-1)" i256 (.int (-1)) "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
  assertEncodes "int256(1)" i256 ((.int 1)) "0x0000000000000000000000000000000000000000000000000000000000000001",
  assertEncodes "int8(-128)" i8 (.int (-128)) "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80",
  assertEncodes "int8(127)" i8 ((.int 127)) "0x000000000000000000000000000000000000000000000000000000000000007f",
  assertEncodes "bool(false)" .bool (.bool false) "0x0000000000000000000000000000000000000000000000000000000000000000",
  assertEncodes "bool(true)" .bool (.bool true) "0x0000000000000000000000000000000000000000000000000000000000000001",
  assertEncodes "address" .address (.address (bytes (List.replicate 20 0x42))) "0x0000000000000000000000004242424242424242424242424242424242424242",
  assertEncodes "bytes1(0xff)" bytes1Ty (.bytes (bytes [0xff])) "0xff00000000000000000000000000000000000000000000000000000000000000",
  assertEncodes "bytes32(all 0x42)" bytes32Ty (.bytes (bytes (List.replicate 32 0x42))) "0x4242424242424242424242424242424242424242424242424242424242424242",
]

def testStaticRoundtrips : List (IO TestResult) := [
  assertRoundtrip "uint256(0) roundtrip" u256 ((.uint 0)),
  assertRoundtrip "uint256(1) roundtrip" u256 ((.uint 1)),
  assertRoundtrip "uint256(2^128) roundtrip" u256 (.uint (2^128)),
  assertRoundtrip "uint8(0) roundtrip" u8 ((.uint 0)),
  assertRoundtrip "uint8(255) roundtrip" u8 ((.uint 255)),
  assertRoundtrip "int256(0) roundtrip" i256 ((.int 0)),
  assertRoundtrip "int256(-1) roundtrip" i256 (.int (-1)),
  assertRoundtrip "int256(-2^255) roundtrip" i256 (.int (-(2^255))),
  assertRoundtrip "int256(2^255-1) roundtrip" i256 (.int (2^255 - 1)),
  assertRoundtrip "bool(true) roundtrip" .bool (.bool true),
  assertRoundtrip "bool(false) roundtrip" .bool (.bool false),
  assertRoundtrip "address roundtrip" .address (.address (bytes (List.replicate 20 0xAB))),
  assertRoundtrip "bytes1 roundtrip" bytes1Ty (.bytes (bytes [0x01])),
  assertRoundtrip "bytes32 roundtrip" bytes32Ty (.bytes (bytes (List.replicate 32 0xFF))),
]

def testDynamicTypes : List (IO TestResult) := [
  assertEncodes "bytes(empty)" .bytes (.bytes (bytes [])) "0x0000000000000000000000000000000000000000000000000000000000000000",
  assertEncodes "bytes(0xab)" .bytes (.bytes (bytes [0xab]))
    "0x0000000000000000000000000000000000000000000000000000000000000001ab00000000000000000000000000000000000000000000000000000000000000",
  assertRoundtrip "bytes(empty) roundtrip" .bytes (.bytes (bytes [])),
  assertRoundtrip "bytes(0xab) roundtrip" .bytes (.bytes (bytes [0xab])),
  assertRoundtrip "bytes(32x42) roundtrip" .bytes (.bytes (bytes (List.replicate 32 0x42))),
  assertRoundtrip "bytes(33x42) roundtrip" .bytes (.bytes (bytes (List.replicate 33 0x42))),
  assertEncodes "string(empty)" .string (.string "") "0x0000000000000000000000000000000000000000000000000000000000000000",
  assertEncodes "string(hello)" .string (.string "hello")
    "0x000000000000000000000000000000000000000000000000000000000000000568656c6c6f000000000000000000000000000000000000000000000000000000",
  assertRoundtrip "string(hello) roundtrip" .string (.string "hello"),
  assertRoundtrip "string(empty) roundtrip" .string (.string ""),
]

def testArrays : List (IO TestResult) := [
  assertEncodes "uint256[3]([1,2,3])" (.fixedArray 3 u256)
    (.array [.uint 1, (.uint 2), .uint 3])
    "0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003",
  assertRoundtrip "uint256[3]([1,2,3]) roundtrip" (.fixedArray 3 u256)
    (.array [.uint 1, (.uint 2), .uint 3]),
  assertEncodes "uint256[]([10,20])" (.array u256)
    (.array [(.uint 10), .uint 20])
    "0x0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000014",
  assertRoundtrip "uint256[]([10,20]) roundtrip" (.array u256)
    (.array [(.uint 10), .uint 20]),
  assertEncodes "uint256[](empty)" (.array u256) (.array [])
    "0x0000000000000000000000000000000000000000000000000000000000000000",
  assertRoundtrip "uint256[](empty) roundtrip" (.array u256) (.array []),
]

def testTuples : List (IO TestResult) := [
  assertRoundtrip "(uint256,address,bool) roundtrip"
    (.tuple [u256, .address, .bool])
    (.tuple [(.uint 123), .address (bytes (List.replicate 20 0xAB)), .bool false]),
  assertRoundtrip "(uint256,bytes) roundtrip"
    (.tuple [u256, .bytes])
    (.tuple [(.uint 999), .bytes (bytes [0xDE, 0xAD, 0xBE, 0xEF])]),
  assertRoundtrip "(uint256,string,bool) roundtrip"
    (.tuple [u256, .string, .bool])
    (.tuple [(.uint 42), .string "hello", .bool true]),
  assertEncodes "() empty tuple" (.tuple []) (.tuple []) "0x",
  assertRoundtrip "() empty tuple roundtrip" (.tuple []) (.tuple []),
]

def testComplexHeadSize : List (IO TestResult) := [
  assertEncodes "(uint256[3],bytes) encode" (.tuple [
    (.fixedArray 3 u256),
    .bytes
  ]) (.tuple [
    (.array [.uint 1, .uint 2, .uint 3]),
    .bytes (bytes [0x68, 0x65, 0x6c, 0x6c, 0x6f])
  ])
    ("0x0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002" ++
    "0000000000000000000000000000000000000000000000000000000000000003" ++
    "0000000000000000000000000000000000000000000000000000000000000080" ++
    "0000000000000000000000000000000000000000000000000000000000000005" ++
    "68656c6c6f000000000000000000000000000000000000000000000000000000"),
  assertRoundtrip "(uint256[3],bytes) roundtrip" (.tuple [
    (.fixedArray 3 u256),
    .bytes
  ]) (.tuple [
    (.array [.uint 1, .uint 2, .uint 3]),
    .bytes (bytes [0x68, 0x65, 0x6c, 0x6c, 0x6f])
  ]),
  assertEncodes "(uint256,bytes,uint256[3]) encode" (.tuple [
    u256,
    .bytes,
    (.fixedArray 3 u256)
  ]) (.tuple [
    .uint 42,
    .bytes (bytes [0x68, 0x65, 0x6c, 0x6c, 0x6f]),
    (.array [.uint 1, .uint 2, .uint 3])
  ])
    ("0x000000000000000000000000000000000000000000000000000000000000002a" ++
    "00000000000000000000000000000000000000000000000000000000000000a0" ++
    "0000000000000000000000000000000000000000000000000000000000000001" ++
    "0000000000000000000000000000000000000000000000000000000000000002" ++
    "0000000000000000000000000000000000000000000000000000000000000003" ++
    "0000000000000000000000000000000000000000000000000000000000000005" ++
    "68656c6c6f000000000000000000000000000000000000000000000000000000"),
  assertRoundtrip "(uint256,bytes,uint256[3]) roundtrip" (.tuple [
    u256,
    .bytes,
    (.fixedArray 3 u256)
  ]) (.tuple [
    .uint 42,
    .bytes (bytes [0x68, 0x65, 0x6c, 0x6c, 0x6f]),
    (.array [.uint 1, .uint 2, .uint 3])
  ]),
]

def testBazExample : List (IO TestResult) := [
  assertEncodes "baz(uint32,bool) encode" (.tuple [u32, .bool])
    (.tuple [(.uint 69), .bool true])
    "0x00000000000000000000000000000000000000000000000000000000000000450000000000000000000000000000000000000000000000000000000000000001",
  assertRoundtrip "baz(uint32,bool) roundtrip" (.tuple [u32, .bool])
    (.tuple [(.uint 69), .bool true]),
  assertDecodes "baz(uint32,bool) decode" (.tuple [u32, .bool])
    "0x00000000000000000000000000000000000000000000000000000000000000450000000000000000000000000000000000000000000000000000000000000001"
    (.tuple [(.uint 69), .bool true]),
]

def testBarExample : List (IO TestResult) :=
  assertEncDecRT "bar(bytes3[2])" (.tuple [.fixedArray 2 bytes3Ty])
    (.tuple [.array [
      .bytes (bytes [0x61, 0x62, 0x63]),
      .bytes (bytes [0x64, 0x65, 0x66])
    ]])
    "0x61626300000000000000000000000000000000000000000000000000000000006465660000000000000000000000000000000000000000000000000000000000"

def testSamExample : List (IO TestResult) :=
  assertEncDecRT "sam(bytes,bool,uint256[])" (.tuple [.bytes, .bool, .array u256])
    (.tuple [.bytes (bytes [0x64, 0x61, 0x76, 0x65]), .bool true, .array [.uint 1, (.uint 2), .uint 3]])
    "0x0000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000464617665000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003"

def testFExample : List (IO TestResult) :=
  assertEncDecRT "f(uint256,uint32[],bytes10,bytes)"
    (.tuple [u256, .array u32, bytes10Ty, .bytes])
    (.tuple [
      .uint 0x123,
      .array [.uint 0x456, .uint 0x789],
      .bytes (bytes [0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x30]),
      .bytes (bytes [0x48,0x65,0x6c,0x6c,0x6f,0x2c,0x20,0x77,0x6f,0x72,0x6c,0x64,0x21])
    ])
    "0x00000000000000000000000000000000000000000000000000000000000001230000000000000000000000000000000000000000000000000000000000000080313233343536373839300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000004560000000000000000000000000000000000000000000000000000000000000789000000000000000000000000000000000000000000000000000000000000000d48656c6c6f2c20776f726c642100000000000000000000000000000000000000"

def testGExample : List (IO TestResult) :=
  assertEncDecRT "g(uint256[][],string[])"
    (.tuple [.array (.array u256), .array .string])
    (.tuple [
      .array [.array [(.uint 1), .uint 2], .array [.uint 3]],
      .array [.string "one", .string "two", .string "three"]
    ])
    "0x000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000001400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000036f6e650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000374776f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000057468726565000000000000000000000000000000000000000000000000000000"

def testErrors : List (IO TestResult) := [
  assertEncodeError "uint8 overflow" u8 (.uint 256),
  assertEncodeError "uint8 overflow (2)" u8 ((.uint 300)),
  assertEncodeError "address wrong size" .address (.address (bytes [0x01])),
  assertEncodeError "bytesM size mismatch" bytes4Ty (.bytes (bytes [0x01, 0x02])),
]

def testDecodeErrors : List (IO TestResult) := [
  assertDecodeError "uint8: data too short" u8 (bytes []),
  assertDecodeError "uint8: truncated data" u8 (bytes [0x00, 0x01]),
  assertDecodeError "bool: invalid value 2" .bool (parseHex "0x0000000000000000000000000000000000000000000000000000000000000002"),
  assertDecodeError "bytes: truncated data" .bytes (parseHex "0x0000000000000000000000000000000000000000000000000000000000000001"),
]

----------------------------------------------------------------------
-- Main test runner
----------------------------------------------------------------------

def main : IO Unit := do
  IO.println "========================================="
  IO.println "  EvmAbi — ABI Encode/Decode Test Suite"
  IO.println "  Solidity ABI Specification v0.8.x"
  IO.println "========================================="

  let groups : List (String × List (IO TestResult)) := [
    ("Function Selectors", testFunctionSelectors),
    ("Static Type Encoding", testStaticTypes),
    ("Static Type Roundtrips", testStaticRoundtrips),
    ("Dynamic Types (bytes, string)", testDynamicTypes),
    ("Arrays (fixed & dynamic)", testArrays),
    ("Tuples", testTuples),
    ("Spec Example: baz(uint32,bool)", testBazExample),
    ("Complex Head Sizes", testComplexHeadSize),
    ("Spec Example: bar(bytes3[2])", testBarExample),
    ("Spec Example: sam(bytes,bool,uint256[])", testSamExample),
    ("Spec Example: f(uint256,uint32[],bytes10,bytes)", testFExample),
    ("Spec Example: g(uint256[][],string[])", testGExample),
    ("Error Handling: Encode", testErrors),
    ("Error Handling: Decode", testDecodeErrors),
  ]

  let totalFails ← groups.foldlM (fun acc (name, tests) => do
    let fails ← runGroup name tests
    pure (acc + fails)
  ) 0

  IO.println "\n========================================="
  if totalFails = 0 then
    IO.println "  All tests passed! ✓"
  else
    IO.println s!"  {totalFails} test(s) FAILED ✗"
  IO.println "========================================="
