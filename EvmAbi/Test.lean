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
def byteArraysEq (a b : ByteArray) : Bool :=
  if a.size ≠ b.size then false else
    List.range a.size |>.all (fun i => a[i]! = b[i]!)

/-- Make ByteArray from a list -/
def bytes (xs : List UInt8) : ByteArray := ByteArray.mk (Array.mk xs)

/-- Concatenate two hex strings for use in test vectors -/
def hex (s : String) : String := s
def hexCat (a b : String) : String := a ++ b

/-- A test result -/
inductive TestResult where
  | pass (label : String)
  | fail (label : String) (msg : String)
  deriving Repr

instance : ToString TestResult where
  toString
    | .pass l => s!"  ✓ {l}"
    | .fail l m => s!"  ✗ {l}: {m}"

/-- Run a list of IO TestResult tests, return results -/
def collectTests (tests : List (IO TestResult)) : IO (List TestResult) :=
  tests.mapM id

/-- Count passed tests -/
def countPassed (results : List TestResult) : Nat :=
  (results.filter (fun r => match r with | .pass _ => true | _ => false)).length

/-- Assert that encode produces the expected hex string -/
def assertEncodes (label : String) (t : ABIType) (v : ABIValue) (expectedHex : String) : IO TestResult := do
  let enc :=
    match t with
    | .tuple _ => encodeArgs (match t with | .tuple es => es | _ => []) (match v with | .tuple vs => vs | _ => [])
    | _ => encode t v
  match enc with
  | Except.ok enc =>
    let expected := parseHex expectedHex
    if byteArraysEq enc expected then
      pure (.pass label)
    else
      pure (.fail label s!"got {hexBytes enc}, expected {expectedHex}")
  | Except.error e =>
    pure (.fail label s!"encode error: {e}")

/-- Assert that encode-decode roundtrip preserves the value -/
def assertRoundtrip (label : String) (t : ABIType) (v : ABIValue) : IO TestResult := do
  let enc :=
    match t with
    | .tuple _ => encodeArgs (match t with | .tuple es => es | _ => []) (match v with | .tuple vs => vs | _ => [])
    | _ => encode t v
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

/-- Assert selector matches -/
def assertSelector (label : String) (sig : String) (expectedHex : String) : IO TestResult := do
  let sel := functionSelector sig
  let expected := parseHex expectedHex
  if byteArraysEq sel expected then
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
  let results ← collectTests tests
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
  assertEncodes "uint256(0)" ((.uint (ByteSize.ofLen 32 (by omega)))) ((.uint 0)) "0x0000000000000000000000000000000000000000000000000000000000000000",
  assertEncodes "uint256(1)" ((.uint (ByteSize.ofLen 32 (by omega)))) ((.uint 1)) "0x0000000000000000000000000000000000000000000000000000000000000001",
  assertEncodes "uint256(42)" ((.uint (ByteSize.ofLen 32 (by omega)))) ((.uint 42)) "0x000000000000000000000000000000000000000000000000000000000000002a",
  assertEncodes "uint256(max)" ((.uint (ByteSize.ofLen 32 (by omega)))) (.uint (2^256 - 1)) "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
  assertEncodes "uint8(255)" ((.uint (ByteSize.ofLen 1 (by omega)))) ((.uint 255)) "0x00000000000000000000000000000000000000000000000000000000000000ff",
  assertEncodes "int256(0)" ((.int (ByteSize.ofLen 32 (by omega)))) ((.int 0)) "0x0000000000000000000000000000000000000000000000000000000000000000",
  assertEncodes "int256(-1)" ((.int (ByteSize.ofLen 32 (by omega)))) (.int (-1)) "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
  assertEncodes "int256(1)" ((.int (ByteSize.ofLen 32 (by omega)))) ((.int 1)) "0x0000000000000000000000000000000000000000000000000000000000000001",
  assertEncodes "int8(-128)" ((.int (ByteSize.ofLen 1 (by omega)))) (.int (-128)) "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80",
  assertEncodes "int8(127)" ((.int (ByteSize.ofLen 1 (by omega)))) ((.int 127)) "0x000000000000000000000000000000000000000000000000000000000000007f",
  assertEncodes "bool(false)" .bool (.bool false) "0x0000000000000000000000000000000000000000000000000000000000000000",
  assertEncodes "bool(true)" .bool (.bool true) "0x0000000000000000000000000000000000000000000000000000000000000001",
  assertEncodes "address" .address (.address (bytes (List.replicate 20 0x42))) "0x0000000000000000000000004242424242424242424242424242424242424242",
  assertEncodes "bytes1(0xff)" ((.bytesM (ByteSize.ofLen 1 (by omega)))) (.bytes (bytes [0xff])) "0xff00000000000000000000000000000000000000000000000000000000000000",
  assertEncodes "bytes32(all 0x42)" ((.bytesM (ByteSize.ofLen 32 (by omega)))) (.bytes (bytes (List.replicate 32 0x42))) "0x4242424242424242424242424242424242424242424242424242424242424242",
]

def testStaticRoundtrips : List (IO TestResult) := [
  assertRoundtrip "uint256(0) roundtrip" ((.uint (ByteSize.ofLen 32 (by omega)))) ((.uint 0)),
  assertRoundtrip "uint256(1) roundtrip" ((.uint (ByteSize.ofLen 32 (by omega)))) ((.uint 1)),
  assertRoundtrip "uint256(2^128) roundtrip" ((.uint (ByteSize.ofLen 32 (by omega)))) (.uint (2^128)),
  assertRoundtrip "uint8(0) roundtrip" ((.uint (ByteSize.ofLen 1 (by omega)))) ((.uint 0)),
  assertRoundtrip "uint8(255) roundtrip" ((.uint (ByteSize.ofLen 1 (by omega)))) ((.uint 255)),
  assertRoundtrip "int256(0) roundtrip" ((.int (ByteSize.ofLen 32 (by omega)))) ((.int 0)),
  assertRoundtrip "int256(-1) roundtrip" ((.int (ByteSize.ofLen 32 (by omega)))) (.int (-1)),
  assertRoundtrip "int256(-2^255) roundtrip" ((.int (ByteSize.ofLen 32 (by omega)))) (.int (-(2^255))),
  assertRoundtrip "int256(2^255-1) roundtrip" ((.int (ByteSize.ofLen 32 (by omega)))) (.int (2^255 - 1)),
  assertRoundtrip "bool(true) roundtrip" .bool (.bool true),
  assertRoundtrip "bool(false) roundtrip" .bool (.bool false),
  assertRoundtrip "address roundtrip" .address (.address (bytes (List.replicate 20 0xAB))),
  assertRoundtrip "bytes1 roundtrip" ((.bytesM (ByteSize.ofLen 1 (by omega)))) (.bytes (bytes [0x01])),
  assertRoundtrip "bytes32 roundtrip" ((.bytesM (ByteSize.ofLen 32 (by omega)))) (.bytes (bytes (List.replicate 32 0xFF))),
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
  assertEncodes "uint256[3]([1,2,3])" (.array ((.uint (ByteSize.ofLen 32 (by omega)))) (some 3))
    (.array [.uint 1, (.uint 2), .uint 3])
    "0x000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003",
  assertRoundtrip "uint256[3]([1,2,3]) roundtrip" (.array ((.uint (ByteSize.ofLen 32 (by omega)))) (some 3))
    (.array [.uint 1, (.uint 2), .uint 3]),
  assertEncodes "uint256[]([10,20])" (.array ((.uint (ByteSize.ofLen 32 (by omega)))) none)
    (.array [(.uint 10), .uint 20])
    "0x0000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000014",
  assertRoundtrip "uint256[]([10,20]) roundtrip" (.array ((.uint (ByteSize.ofLen 32 (by omega)))) none)
    (.array [(.uint 10), .uint 20]),
  assertEncodes "uint256[](empty)" (.array ((.uint (ByteSize.ofLen 32 (by omega)))) none) (.array [])
    "0x0000000000000000000000000000000000000000000000000000000000000000",
  assertRoundtrip "uint256[](empty) roundtrip" (.array ((.uint (ByteSize.ofLen 32 (by omega)))) none) (.array []),
]

def testTuples : List (IO TestResult) := [
  assertRoundtrip "(uint256,address,bool) roundtrip"
    (.tuple [(.uint (ByteSize.ofLen 32 (by omega))), .address, .bool])
    (.tuple [(.uint 123), .address (bytes (List.replicate 20 0xAB)), .bool false]),
  assertRoundtrip "(uint256,bytes) roundtrip"
    (.tuple [(.uint (ByteSize.ofLen 32 (by omega))), .bytes])
    (.tuple [(.uint 999), .bytes (bytes [0xDE, 0xAD, 0xBE, 0xEF])]),
  assertRoundtrip "(uint256,string,bool) roundtrip"
    (.tuple [(.uint (ByteSize.ofLen 32 (by omega))), .string, .bool])
    (.tuple [(.uint 42), .string "hello", .bool true]),
  assertEncodes "() empty tuple" (.tuple []) (.tuple []) "0x",
  assertRoundtrip "() empty tuple roundtrip" (.tuple []) (.tuple []),
]

def testComplexHeadSize : List (IO TestResult) := [
  assertEncodes "(uint256[3],bytes) encode" (.tuple [
    (.array (.uint (ByteSize.ofLen 32 (by omega))) (some 3)),
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
    (.array (.uint (ByteSize.ofLen 32 (by omega))) (some 3)),
    .bytes
  ]) (.tuple [
    (.array [.uint 1, .uint 2, .uint 3]),
    .bytes (bytes [0x68, 0x65, 0x6c, 0x6c, 0x6f])
  ]),
  assertEncodes "(uint256,bytes,uint256[3]) encode" (.tuple [
    (.uint (ByteSize.ofLen 32 (by omega))),
    .bytes,
    (.array (.uint (ByteSize.ofLen 32 (by omega))) (some 3))
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
    (.uint (ByteSize.ofLen 32 (by omega))),
    .bytes,
    (.array (.uint (ByteSize.ofLen 32 (by omega))) (some 3))
  ]) (.tuple [
    .uint 42,
    .bytes (bytes [0x68, 0x65, 0x6c, 0x6c, 0x6f]),
    (.array [.uint 1, .uint 2, .uint 3])
  ]),
]

def testBazExample : List (IO TestResult) := [
  assertEncodes "baz(uint32,bool) encode" (.tuple [(.uint (ByteSize.ofLen 4 (by omega))), .bool])
    (.tuple [(.uint 69), .bool true])
    "0x00000000000000000000000000000000000000000000000000000000000000450000000000000000000000000000000000000000000000000000000000000001",
  assertRoundtrip "baz(uint32,bool) roundtrip" (.tuple [(.uint (ByteSize.ofLen 4 (by omega))), .bool])
    (.tuple [(.uint 69), .bool true]),
  assertDecodes "baz(uint32,bool) decode" (.tuple [(.uint (ByteSize.ofLen 4 (by omega))), .bool])
    "0x00000000000000000000000000000000000000000000000000000000000000450000000000000000000000000000000000000000000000000000000000000001"
    (.tuple [(.uint 69), .bool true]),
]

def testBarExample : List (IO TestResult) := [
  assertEncodes "bar(bytes3[2]) encode" (.tuple [.array ((.bytesM (ByteSize.ofLen 3 (by omega)))) (some 2)])
    (.tuple [.array [
      .bytes (bytes [0x61, 0x62, 0x63]),
      .bytes (bytes [0x64, 0x65, 0x66])
    ]])
    "0x61626300000000000000000000000000000000000000000000000000000000006465660000000000000000000000000000000000000000000000000000000000",
  assertRoundtrip "bar(bytes3[2]) roundtrip" (.tuple [.array ((.bytesM (ByteSize.ofLen 3 (by omega)))) (some 2)])
    (.tuple [.array [
      .bytes (bytes [0x61, 0x62, 0x63]),
      .bytes (bytes [0x64, 0x65, 0x66])
    ]]),
]

def testSamExample : List (IO TestResult) := [
  assertEncodes "sam(bytes,bool,uint256[]) encode" (.tuple [.bytes, .bool, .array ((.uint (ByteSize.ofLen 32 (by omega)))) none])
    (.tuple [.bytes (bytes [0x64, 0x61, 0x76, 0x65]), .bool true, .array [.uint 1, (.uint 2), .uint 3]])
    "0x0000000000000000000000000000000000000000000000000000000000000060000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000464617665000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000003",
  assertRoundtrip "sam(bytes,bool,uint256[]) roundtrip" (.tuple [.bytes, .bool, .array ((.uint (ByteSize.ofLen 32 (by omega)))) none])
    (.tuple [.bytes (bytes [0x64, 0x61, 0x76, 0x65]), .bool true, .array [.uint 1, (.uint 2), .uint 3]]),
]

def testFExample : List (IO TestResult) := [
  assertEncodes "f(uint256,uint32[],bytes10,bytes) encode"
    (.tuple [(.uint (ByteSize.ofLen 32 (by omega))), .array ((.uint (ByteSize.ofLen 4 (by omega)))) none, (.bytesM (ByteSize.ofLen 10 (by omega))), .bytes])
    (.tuple [
      .uint 0x123,
      .array [.uint 0x456, .uint 0x789],
      .bytes (bytes [0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x30]),
      .bytes (bytes [0x48,0x65,0x6c,0x6c,0x6f,0x2c,0x20,0x77,0x6f,0x72,0x6c,0x64,0x21])
    ])
    "0x00000000000000000000000000000000000000000000000000000000000001230000000000000000000000000000000000000000000000000000000000000080313233343536373839300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000004560000000000000000000000000000000000000000000000000000000000000789000000000000000000000000000000000000000000000000000000000000000d48656c6c6f2c20776f726c642100000000000000000000000000000000000000",
  assertRoundtrip "f(uint256,uint32[],bytes10,bytes) roundtrip"
    (.tuple [(.uint (ByteSize.ofLen 32 (by omega))), .array ((.uint (ByteSize.ofLen 4 (by omega)))) none, (.bytesM (ByteSize.ofLen 10 (by omega))), .bytes])
    (.tuple [
      .uint 0x123,
      .array [.uint 0x456, .uint 0x789],
      .bytes (bytes [0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x30]),
      .bytes (bytes [0x48,0x65,0x6c,0x6c,0x6f,0x2c,0x20,0x77,0x6f,0x72,0x6c,0x64,0x21])
    ]),
]

def testGExample : List (IO TestResult) := [
  assertEncodes "g(uint256[][],string[]) encode"
    (.tuple [.array (.array ((.uint (ByteSize.ofLen 32 (by omega)))) none) none, .array .string none])
    (.tuple [
      .array [.array [(.uint 1), .uint 2], .array [.uint 3]],
      .array [.string "one", .string "two", .string "three"]
    ])
    "0x000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000001400000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000a0000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000030000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000000e000000000000000000000000000000000000000000000000000000000000000036f6e650000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000374776f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000057468726565000000000000000000000000000000000000000000000000000000",
  assertRoundtrip "g(uint256[][],string[]) roundtrip"
    (.tuple [.array (.array ((.uint (ByteSize.ofLen 32 (by omega)))) none) none, .array .string none])
    (.tuple [
      .array [.array [(.uint 1), .uint 2], .array [.uint 3]],
      .array [.string "one", .string "two", .string "three"]
    ]),
]

def testErrors : List (IO TestResult) := [
  assertEncodeError "uint8 overflow" ((.uint (ByteSize.ofLen 1 (by omega)))) (.uint 256),
  assertEncodeError "uint8 overflow (2)" ((.uint (ByteSize.ofLen 1 (by omega)))) ((.uint 300)),
  assertEncodeError "address wrong size" .address (.address (bytes [0x01])),
  assertEncodeError "bytesM size mismatch" ((.bytesM (ByteSize.ofLen 4 (by omega)))) (.bytes (bytes [0x01, 0x02])),
]

def testDecodeErrors : List (IO TestResult) := [
  assertDecodeError "uint8: data too short" ((.uint (ByteSize.ofLen 1 (by omega)))) (bytes []),
  assertDecodeError "uint8: truncated data" ((.uint (ByteSize.ofLen 1 (by omega)))) (bytes [0x00, 0x01]),
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
