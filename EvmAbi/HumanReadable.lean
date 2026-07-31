import EvmAbi.Ty

/-!
# EvmAbi.HumanReadable

Parser for the Solidity human-readable ABI format, implemented in pure
Lean so it can be called at elaboration time (`elab`) for compile-time
expansion into `Ty` / `AbiItem` expressions.

## Supported signatures

Types are the grammar of the mapping table below.  Array suffixes apply to
tuples too, so `(address,uint256)[]` is the human-readable form of a Solidity
`struct[]`.  Widths outside the range the specification allows (`uint7`,
`bytes33`, ...) are rejected, so a successful parse always yields a `Ty.Valid`
type.

```
ABI items:
  function name(params) modifiers? returns (outputs)?
  event name(params)
  error name(params)
  constructor(params) modifiers?
  fallback() modifiers?
  receive() modifiers?

Modifiers:
  view | pure | payable | nonpayable            — at most one, recorded as the mutability
  external | public | internal | private        — accepted and dropped
  virtual | override                            — accepted and dropped

Params:
  type (indexed | calldata | memory | storage)* name?
  type, type, ...         — unnamed params
```

Whitespace between tokens is skipped but never required, so
`'function name()returns(string)'` parses the same as its spaced form.  Two
adjacent word tokens still need a separator: `'uint256 a'` names a parameter,
whereas `'uint256a'` is a single (invalid) identifier.

## Mapping to EvmAbi.Ty

| Human-readable    | Ty                |
|-------------------|-------------------|
| `uint<N>`         | `.uint N`         |
| `int<N>`          | `.int N`          |
| `uint` / `int`    | `.uint 256` / `.int 256` |
| `address`         | `.address`        |
| `address payable` | `.address`        |
| `bool`            | `.bool`           |
| `bytes`           | `.bytes`          |
| `bytes<N>`        | `.bytesN N`       |
| `string`          | `.string`         |
| `T[]`             | `.array T`        |
| `T[N]`            | `.fixedArray T N` |
| `(T₁, ..., Tₙ)`   | `.tuple [T₁,…,Tₙ]` |
-/

namespace EvmAbi

open Ty

/-! ## AbiItem: structured representation of a parsed ABI item -/

/-- Solidity state mutability. -/
inductive StateMutability where
  | pure | view | nonpayable | payable
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A single ABI parameter: type, optional name, and `indexed` flag (for events). -/
structure AbiParam where
  ty : Ty
  name : Option String
  indexed : Bool
  deriving Repr

/-- A parsed ABI item. -/
inductive AbiItem where
  | function (name : String) (inputs : List AbiParam) (outputs : List AbiParam)
      (stateMutability : StateMutability)
  | event (name : String) (inputs : List AbiParam)
  | error (name : String) (inputs : List AbiParam)
  | constructor (inputs : List AbiParam) (stateMutability : StateMutability)
  | fallback (stateMutability : StateMutability)
  | receive
  deriving Repr, Inhabited

namespace AbiItem

/-- Extract the input types as a tuple `Ty`: exactly the argument block of the
call data.  The tuple is never collapsed, not even for a single argument —
`f(bytes)` encodes as `offset ‖ length ‖ payload`, whereas the bare `bytes`
encoding would drop the offset word. -/
def inputsTy (item : AbiItem) : Ty :=
  match item with
  | function _ inputs _ _ | event _ inputs | error _ inputs | constructor inputs _ =>
      .tuple (inputs.map (·.ty))
  | fallback _ | receive => .tuple []

/-- Extract the output types as a tuple `Ty`, with the same no-collapse rule as
`inputsTy`.  `none` for items that have no return values at all. -/
def outputsTy (item : AbiItem) : Option Ty :=
  match item with
  | function _ _ outputs _ => some (.tuple (outputs.map (·.ty)))
  | _ => none

end AbiItem


/-! ## Character-level parsing utilities -/

section CharParsing

/-- Skip whitespace characters. -/
def skipWS : List Char → List Char
  | ' ' :: cs  => skipWS cs
  | '\t' :: cs => skipWS cs
  | '\n' :: cs => skipWS cs
  | '\r' :: cs => skipWS cs
  | cs => cs

/-- Parse a decimal number, returning the number and remaining input. -/
def parseNat (cs : List Char) : Option (Nat × List Char) :=
  let rec go (acc : Nat) : List Char → Option (Nat × List Char)
    | c :: cs' =>
      if '0' ≤ c ∧ c ≤ '9' then
        go (acc * 10 + (c.toNat - '0'.toNat)) cs'
      else
        some (acc, c :: cs')
    | [] => some (acc, [])
  match cs with
  | c :: _ =>
    if '0' ≤ c ∧ c ≤ '9' then go 0 cs
    else none
  | [] => none

/-- Parse an identifier: starts with letter or underscore, continues with
alphanumeric or underscore.  Skips leading whitespace. -/
def parseIdent (cs : List Char) : Option (String × List Char) :=
  let cs' := skipWS cs
  let rec go (acc : List Char) : List Char → Option (String × List Char)
    | c :: rest =>
      if ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ ('0' ≤ c ∧ c ≤ '9') ∨ c = '_' then
        go (c :: acc) rest
      else
        some (String.ofList (acc.reverse), c :: rest)
    | [] => some (String.ofList (acc.reverse), [])
  match cs' with
  | c :: _ =>
    if ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ c = '_' then
      go [c] (cs'.tailD [])
    else none
  | [] => none

/-- Consume an exact string literal, skipping leading whitespace. -/
def parseLit (s : String) (cs : List Char) : Option (List Char) :=
  let chars := s.toList
  let cs' := skipWS cs
  if cs'.take chars.length = chars then
    some (cs'.drop chars.length)
  else
    none

/-- Consume an exact Char, skipping leading whitespace. -/
def parseChar (c : Char) (cs : List Char) : Option (List Char) :=
  let cs' := skipWS cs
  match cs' with
  | d :: rest => if c = d then some rest else none
  | [] => none

end CharParsing


/-! ## Type parser -/

section TypeParser

/-- Helper: read `name` as `pref` followed by a width, e.g. `"uint256"`.  Widths
outside the range the specification allows are rejected (`Ty.Valid`), so `uint7`,
`uint999`, `bytes0` and `bytes33` fail to parse rather than producing a type no
codec theorem applies to. -/
def tryPrefix (name : String) (pref : String) (mkTy : Nat → Ty) (rest : List Char) :
    Option (Ty × List Char) := do
  let ty := mkTy (← (← name.dropPrefix? pref).toNat?)
  if ty.Valid then some (ty, rest) else none

/-- Base types named outright, including the bare `uint`/`int` aliases for the
256-bit widths. -/
def baseTypeOf : String → Option Ty
  | "address" => some .address
  | "bool"    => some .bool
  | "string"  => some .string
  | "bytes"   => some .bytes
  | "uint"    => some (.uint 256)
  | "int"     => some (.int 256)
  | _         => none

/-- `address payable` is a Solidity type; the ABI knows only `address`, so the
`payable` is consumed and dropped.  Taking it here rather than at the parameter
layer is what makes `(address payable, uint256)` and `address payable[]` work. -/
def dropPayable (cs : List Char) : List Char :=
  match parseIdent cs with
  | some ("payable", rest) => rest
  | _ => cs

/-- One or more `p`s separated by commas.  Every comma must be followed by
another `p`, so a trailing comma is a parse error. -/
partial def sepBy1 {α : Type} (p : List Char → Option (α × List Char)) (cs : List Char) :
    Option (List α × List Char) := do
  let (x, rest) ← p cs
  let rest' := skipWS rest
  match rest' with
  | ',' :: rest2 => do
    let (xs, rest3) ← sepBy1 p rest2
    some (x :: xs, rest3)
  | _ => some ([x], rest')

mutual
/-- Parse a single ABI type (e.g. `uint256`, `address`, `bytes32`, `(uint,bool)`,
`uint256[]`, `uint256[5]`).  Returns the `Ty` and the remaining input. -/
partial def parseType (cs : List Char) : Option (Ty × List Char) :=
  -- try tuple first: (...)
  parseTupleType cs <|> parseElementaryType cs

/-- Parse an elementary type (non-tuple): uint, int, address, bool, bytes, string,
optionally followed by `[]` or `[N]`. -/
partial def parseElementaryType (cs : List Char) : Option (Ty × List Char) := do
  let cs' := skipWS cs
  let (baseTy, rest) ← parseBaseType cs'
  parseArraySuffix baseTy rest

/-- Parse the base type identifier: `uint<N>`, `int<N>`, `address`, `bool`,
`bytes<N?>`, `string`.  Since `parseIdent` also consumes digits, the
identifier may embed the bit width (e.g., `"uint256"`), so the named types are
tried first and the width-bearing ones as prefixes. -/
partial def parseBaseType (cs : List Char) : Option (Ty × List Char) := do
  let (name, rest) ← parseIdent cs
  match baseTypeOf name with
  | some .address => some (.address, dropPayable rest)
  | some ty => some (ty, rest)
  | none =>
    tryPrefix name "uint" Ty.uint rest
      <|> tryPrefix name "int" Ty.int rest
      <|> tryPrefix name "bytes" Ty.bytesN rest

/-- Parse tuple type `(T1, T2, ..., Tn)`, with an optional array suffix:
`(address,uint256)[]` and `(address,uint256)[2]` are tuple arrays. -/
partial def parseTupleType (cs : List Char) : Option (Ty × List Char) := do
  let rest ← parseChar '(' cs
  match skipWS rest with
  -- empty tuple ()
  | ')' :: rest' => parseArraySuffix (.tuple []) rest'
  | rest' => do
    let (tys, rest1) ← sepBy1 parseType rest'
    let rest2 ← parseChar ')' rest1
    parseArraySuffix (.tuple tys) rest2

/-- Parse optional array suffix: `[]` (dynamic) or `[N]` (fixed), or none.

The dynamic case rechecks `Ty.Valid`: a dynamic array needs an element
type that occupies head bytes, so `()[]` and `uint8[0][]` are rejected
here even though `()` and `uint8[0]` parse on their own.  Without the
check a successful parse could yield an invalid type, which no codec
theorem covers. -/
partial def parseArraySuffix (ty : Ty) (cs : List Char) : Option (Ty × List Char) :=
  let cs' := skipWS cs
  match cs' with
  | '[' :: rest =>
    let rest' := skipWS rest
    match rest' with
    | ']' :: rest'' =>
      -- dynamic array: T[]
      if (Ty.array ty).Valid then parseArraySuffix (.array ty) rest'' else none
    | _ =>
      match parseNat rest' with
      | some (n, restNum) =>
        (parseChar ']' restNum).bind fun restPost =>
          parseArraySuffix (.fixedArray ty n) restPost
      | none => none
  | _ =>
    some (ty, cs')

end

/-- Top-level entry point: parse a string into a `Ty`. -/
def parseTypeFromString (s : String) : Option Ty :=
  match parseType (s.toList) with
  | some (ty, rest) => if (skipWS rest).isEmpty then some ty else none
  | none => none

end TypeParser


/-! ## Solidity keywords

The three places that have to recognise a keyword — the modifier run after a
signature, the keyword run after a parameter type, and the guard that stops a
modifier being taken for a parameter name — all read from these tables. -/

section Keywords

/-- The state-mutability keywords, the only modifiers the ABI records. -/
def mutabilityOf : String → Option StateMutability
  | "view"       => some .view
  | "pure"       => some .pure
  | "payable"    => some .payable
  | "nonpayable" => some .nonpayable
  | _            => none

/-- Visibility and inheritance keywords: Solidity source syntax with no ABI
counterpart, accepted and dropped. -/
def isVisibility (kw : String) : Bool :=
  kw == "external" || kw == "public" || kw == "internal" || kw == "private" ||
    kw == "virtual" || kw == "override"

/-- Data-location keywords, likewise accepted and dropped. -/
def isDataLocation (kw : String) : Bool :=
  kw == "calldata" || kw == "memory" || kw == "storage"

/-- Consume a run of keywords, folding each into an accumulator.  `step` returns
`none` for the first keyword it does not recognise, and the input is handed back
positioned at that keyword. -/
partial def eatKeywords {α : Type} [Inhabited α] (step : String → α → Option α) (a : α)
    (cs : List Char) : α × List Char :=
  let cs' := skipWS cs
  match parseIdent cs' with
  | some (kw, rest) =>
      match step kw a with
      | some a' => eatKeywords step a' rest
      | none => (a, cs')
  | none => (a, cs')

end Keywords


/-! ## Parameter parser -/

section ParamParser

/-- Consume the keywords between a parameter's type and its name, returning the
`indexed` flag.  Data locations are dropped: only `indexed` reaches the ABI. -/
partial def parseParamKeywords (cs : List Char) : Bool × List Char :=
  eatKeywords (fun kw indexed =>
    if kw = "indexed" then some true
    else if isDataLocation kw then some indexed
    else none) false cs

/-- Parse a single ABI parameter: `type (indexed | location)* name?`. -/
partial def parseParam (cs : List Char) : Option (AbiParam × List Char) := do
  let (baseTy, rest0) ← parseType cs
  let (indexed, rest1) := parseParamKeywords rest0
  -- check for parameter name (identifier that isn't a keyword)
  let (name, rest2) :=
    match parseIdent rest1 with
    | some (ident, r) =>
      -- a modifier or `returns` here belongs to the enclosing signature
      if ident = "returns" || (mutabilityOf ident).isSome || isVisibility ident then
        (none, rest1)
      else
        (some ident, r)
    | none => (none, rest1)
  pure ({ ty := baseTy, name := name, indexed := indexed }, rest2)

/-- Parse a comma-separated list of parameters, optionally empty. -/
partial def parseParams (cs : List Char) : Option (List AbiParam × List Char) :=
  let cs' := skipWS cs
  match cs' with
  | [] => some ([], cs')
  | ')' :: _ => some ([], cs')  -- empty param list (already inside parens)
  | _ => sepBy1 parseParam cs'

end ParamParser


/-! ## ABI item parser (function, event, error, constructor, fallback, receive) -/

section AbiItemParser

/-- Consume a run of modifier keywords in any order, returning the state
mutability they declare (`nonpayable` if none does).  Visibility is dropped.
A second mutability keyword — conflicting or merely repeated — is left
unconsumed, which the caller's trailing-input check turns into a parse error.
Stops at anything else, `returns` in particular. -/
partial def parseModifiers (cs : List Char) : StateMutability × List Char :=
  let (sm?, rest) := eatKeywords (fun kw sm? =>
    match mutabilityOf kw with
    | some m => if sm?.isSome then none else some (some m)
    | none => if isVisibility kw then some sm? else none) none cs
  (sm?.getD .nonpayable, rest)

/-- Parse `returns (T1, T2, ...)` clause of a function signature. -/
partial def parseReturns (cs : List Char) : Option (List AbiParam × List Char) := do
  let rest0 ← parseLit "returns" cs
  let rest1 ← parseChar '(' rest0
  let (outputs, rest2) ← parseParams rest1
  let rest3 ← parseChar ')' rest2
  some (outputs, rest3)

/-- Parse a function signature:
`function name ( params? ) modifiers? returns ( outputs? )?` -/
partial def parseFunction (cs : List Char) : Option (AbiItem × List Char) := do
  let rest0 ← parseLit "function" cs
  let (name, rest1) ← parseIdent rest0
  let rest2 ← parseChar '(' rest1
  let (inputs, rest3) ← parseParams rest2
  let rest4 ← parseChar ')' rest3
  -- optional modifiers
  let (mutability, rest5) := parseModifiers rest4
  -- try `returns`
  let rest5' := skipWS rest5
  match parseIdent rest5' with
  | some ("returns", _) => do
    let (outputs, rest6) ← parseReturns rest5
    pure (.function name inputs outputs mutability, rest6)
  | _ =>
    pure (.function name inputs [] mutability, rest5)

/-- Parse an event signature:
`event name ( params? )` -/
partial def parseEvent (cs : List Char) : Option (AbiItem × List Char) := do
  let rest0 ← parseLit "event" cs
  let (name, rest1) ← parseIdent rest0
  let rest2 ← parseChar '(' rest1
  let (inputs, rest3) ← parseParams rest2
  let rest4 ← parseChar ')' rest3
  pure (.event name inputs, rest4)

/-- Parse an error signature:
`error name ( params? )` -/
partial def parseError (cs : List Char) : Option (AbiItem × List Char) := do
  let rest0 ← parseLit "error" cs
  let (name, rest1) ← parseIdent rest0
  let rest2 ← parseChar '(' rest1
  let (inputs, rest3) ← parseParams rest2
  let rest4 ← parseChar ')' rest3
  pure (.error name inputs, rest4)

/-- Parse a constructor signature:
`constructor ( params? ) modifiers?` -/
partial def parseConstructor (cs : List Char) : Option (AbiItem × List Char) := do
  let rest0 ← parseLit "constructor" cs
  let rest1 ← parseChar '(' rest0
  let (inputs, rest2) ← parseParams rest1
  let rest3 ← parseChar ')' rest2
  let (mutability, rest4) := parseModifiers rest3
  pure (.constructor inputs mutability, rest4)

/-- Parse a fallback signature:
`fallback ( ) modifiers?` -/
partial def parseFallback (cs : List Char) : Option (AbiItem × List Char) := do
  let rest0 ← parseLit "fallback" cs
  let rest1 ← parseChar '(' rest0
  let rest2 ← parseChar ')' rest1
  let (mutability, rest3) := parseModifiers rest2
  pure (.fallback mutability, rest3)

/-- Parse a receive signature:
`receive ( ) modifiers?` -/
partial def parseReceive (cs : List Char) : Option (AbiItem × List Char) := do
  let rest0 ← parseLit "receive" cs
  let rest1 ← parseChar '(' rest0
  let rest2 ← parseChar ')' rest1
  -- `receive` is always payable, so its modifiers carry no information
  let (_, rest3) := parseModifiers rest2
  pure (.receive, rest3)

/-- Parse a single ABI item from the beginning of the input.
Dispatches based on the keyword. -/
partial def parseAbiItemRaw (cs : List Char) : Option (AbiItem × List Char) :=
  let cs' := skipWS cs
  match cs' with
  | [] => none
  | _ =>
    match parseIdent cs' with
    | some (kw, _) =>
      if kw = "function" then parseFunction cs'
      else if kw = "event" then parseEvent cs'
      else if kw = "error" then parseError cs'
      else if kw = "constructor" then parseConstructor cs'
      else if kw = "fallback" then parseFallback cs'
      else if kw = "receive" then parseReceive cs'
      else none
    | none => none

/-- Top-level: parse a full ABI item string. -/
partial def parseAbiItem (s : String) : Option AbiItem := do
  let (item, rest) ← parseAbiItemRaw (s.toList)
  let rest' := skipWS rest
  if rest' = [] then some item else none

/-- Parse a list of ABI items from a multi-line string: one item per line,
blank lines skipped.  Any other separator (a semicolon, say) is part of the
line and makes it fail to parse. -/
partial def parseAbi (s : String) : Option (List AbiItem) :=
  -- Split on newlines and parse each non-empty line
  let lines := s.splitOn "\n"
  let rec go (acc : List AbiItem) : List String → Option (List AbiItem)
    | [] => some acc.reverse
    | line :: rest =>
      let trimmed := line.trimAscii
      let trimmedStr := trimmed.toString
      if trimmedStr.isEmpty then go acc rest
      else match parseAbiItem trimmedStr with
        | some item => go (item :: acc) rest
        | none => none
  go [] lines

end AbiItemParser

/-! ## Short idiomatic names -/

/-- Parse a human-readable type string into a `Ty`.  Alias for `parseTypeFromString`. -/
def Ty.parse (s : String) : Option Ty := parseTypeFromString s

/-- Parse a human-readable ABI item signature into an `AbiItem`.  Alias for `parseAbiItem`. -/
def AbiItem.parse (s : String) : Option AbiItem := parseAbiItem s

/-- Parse a human-readable parameter list into `List AbiParam`.
Alias for `parseParams` on `String` input. -/
def AbiParam.parseList (s : String) : Option (List AbiParam) :=
  parseParams (s.toList) >>= fun (ps, rest) =>
    if (skipWS rest).isEmpty then some ps else none

end EvmAbi
