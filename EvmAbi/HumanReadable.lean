import EvmAbi.Ty

/-!
# EvmAbi.HumanReadable

Parser for the Solidity human-readable ABI format, implemented in pure
Lean so it can be called at elaboration time (`elab`) for compile-time
expansion into `Ty` / `AbiItem` expressions.

## Supported signatures

```
Ty strings:
  uint256 | int128 | address | bool | bytes | bytes32 | string
  (T1, T2, ...)            — tuple
  T[]                       — dynamic array
  T[N]                      — fixed-size array

ABI items:
  function name(params) modifiers? returns (outputs)?
  event name(params)
  error name(params)
  constructor(params) modifiers?
  fallback() modifiers?
  receive() modifiers?

Params:
  type indexed? name?     — name and indexed are optional
  type, type, ...         — unnamed params
```

Whitespace is required between tokens per the canonical human-readable spec
(`abitype.dev`): `'function name() returns (string)'` is valid, but
`'function name()returns(string)'` is not.

## Mapping to EvmAbi.Ty

| Human-readable    | Ty                |
|-------------------|-------------------|
| `uint<N>`         | `.uint N`         |
| `int<N>`          | `.int N`          |
| `address`         | `.address`        |
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
  deriving Repr, Inhabited

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

/-- Extract the input types as a tuple `Ty` (or a single type if only one input).
Useful for encoding function call data. -/
def inputsTy (item : AbiItem) : Ty :=
  match item with
  | function _ inputs _ _ | event _ inputs | error _ inputs | constructor inputs _ =>
      match inputs.map (·.ty) with
      | [] => .tuple []
      | [t] => t
      | ts => .tuple ts
  | fallback _ | receive => .tuple []

/-- Extract the output types as a tuple `Ty`. -/
def outputsTy (item : AbiItem) : Option Ty :=
  match item with
  | function _ _ outputs _ =>
      match outputs.map (·.ty) with
      | [] => some (.tuple [])
      | [t] => some t
      | ts => some (.tuple ts)
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

/-- Helper: if `name` starts with `pref`, extract the numeric suffix and parse it as a Nat.
Return the constructed type or `none`. -/
def tryPrefix (name : String) (pref : String) (mkTy : Nat → Ty) (rest : List Char) : Option (Ty × List Char) :=
  if name.startsWith pref then
    let numStr := (name.drop pref.length).toString
    if numStr.isEmpty then
      match parseNat rest with
      | some (n, rest') => some (mkTy n, rest')
      | none => none
    else
      match parseNat (numStr.toList) with
      | some (n, []) => some (mkTy n, rest)
      | _ => none
  else none

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
identifier may embed the bit width (e.g., `"uint256"`).  We extract
any numeric suffix from the identifier itself. -/
partial def parseBaseType (cs : List Char) : Option (Ty × List Char) :=
  match parseIdent cs with
  | none => none
  | some (name, rest) =>
      if name = "address" then some (.address, rest)
      else if name = "bool" then some (.bool, rest)
      else if name = "string" then some (.string, rest)
      else if name = "bytes" then some (.bytes, rest)
      else match tryPrefix name "uint" Ty.uint rest with
        | some res => some res
        | none =>
          match tryPrefix name "int" Ty.int rest with
          | some res => some res
          | none =>
            match tryPrefix name "bytes" Ty.bytesN rest with
            | some res => some res
            | none => none

/-- Parse tuple type `(T1, T2, ..., Tn)`. -/
partial def parseTupleType (cs : List Char) : Option (Ty × List Char) := do
  let rest ← parseChar '(' cs
  -- empty tuple ()
  let rest' := skipWS rest
  match rest' with
  | ')' :: rest'' =>
    some (.tuple [], rest'')
  | _ => do
    let (firstTy, rest1) ← parseType rest'
    let (tys, rest2) ← parseTupleRest rest1
    let rest3 ← parseChar ')' rest2
    some (.tuple (firstTy :: tys), rest3)

/-- Parse the rest of a tuple: `, T2, ..., Tn`. -/
partial def parseTupleRest (cs : List Char) : Option (List Ty × List Char) :=
  let cs' := skipWS cs
  match cs' with
  | ',' :: _ => do
    let (ty, rest1) ← parseType (cs'.drop 1)
    let (tys, rest2) ← parseTupleRest rest1
    some (ty :: tys, rest2)
  | _ =>
    some ([], cs')

/-- Parse optional array suffix: `[]` (dynamic) or `[N]` (fixed), or none. -/
partial def parseArraySuffix (ty : Ty) (cs : List Char) : Option (Ty × List Char) :=
  let cs' := skipWS cs
  match cs' with
  | '[' :: rest =>
    let rest' := skipWS rest
    match rest' with
    | ']' :: rest'' =>
      -- dynamic array: T[]
      parseArraySuffix (.array ty) rest''
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


/-! ## Parameter parser -/

section ParamParser

/-- Parse a single ABI parameter: `type indexed? name?`. -/
partial def parseParam (cs : List Char) : Option (AbiParam × List Char) := do
  let cs' := skipWS cs
  let (baseTy, rest0) ← parseType cs'
  -- check for `indexed` keyword
  let rest0' := skipWS rest0
  let (indexed, rest1) ←
    match parseIdent rest0' with
    | some (kw, rest) => if kw = "indexed" then pure (true, rest) else pure (false, rest0')
    | none => pure (false, rest0')
  -- check for parameter name (identifier that isn't a keyword)
  let rest1' := skipWS rest1
  let (name, rest2) ←
    match rest1' with
    | ',' :: _ => pure (none, rest1')
    | ')' :: _ => pure (none, rest1')
    | [] => pure (none, rest1')
    | _ =>
      match parseIdent rest1' with
      | some (ident, r) =>
        -- make sure it's not a reserved word
        if ident = "indexed" || ident = "returns" || ident = "view" ||
           ident = "pure" || ident = "payable" || ident = "nonpayable" ||
           ident = "external" || ident = "internal" then
          pure (none, rest1')
        else
          pure (some ident, r)
      | none => pure (none, rest1')
  pure ({ ty := baseTy, name := name, indexed := indexed }, rest2)

/-- Parse a comma-separated list of parameters, optionally empty. -/
partial def parseParams (cs : List Char) : Option (List AbiParam × List Char) :=
  let cs' := skipWS cs
  match cs' with
  | [] => some ([], cs')
  | ')' :: _ => some ([], cs')  -- empty param list (already inside parens)
  | _ => do
    let (first, rest1) ← parseParam cs'
    let rest1' := skipWS rest1
    match rest1' with
    | ',' :: rest2 => do
      let (more, rest3) ← parseParams rest2
      some (first :: more, rest3)
    | _ =>
      some ([first], rest1')

end ParamParser


/-! ## ABI item parser (function, event, error, constructor, fallback, receive) -/

section AbiItemParser

/-- Parse state-mutability keywords: `view`, `pure`, `payable`, `nonpayable`. -/
def parseMutability (cs : List Char) : Option (StateMutability × List Char) :=
  -- Try to parse an identifier
  match parseIdent cs with
  | some (kw, rest) =>
      if kw = "view" then some (.view, rest)
      else if kw = "pure" then some (.pure, rest)
      else if kw = "payable" then some (.payable, rest)
      else if kw = "nonpayable" then some (.nonpayable, rest)
      else none
  | none => none

/-- Parse the keyword "external" (optional modifier for fallback/receive). -/
def parseExternal (cs : List Char) : Option (List Char) :=
  let cs' := skipWS cs
  match parseIdent cs' with
  | some ("external", rest) => some rest
  | _ => some cs  -- external is optional

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
  let rest4' := skipWS rest4
  let (mutability, rest5) ←
    match parseMutability rest4' with
    | some (m, r) => pure (m, r)
    | none => pure (.nonpayable, rest4')
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
  let rest3' := skipWS rest3
  let (mutability, rest4) ←
    match parseMutability rest3' with
    | some (m, r) => pure (m, r)
    | none => pure (.nonpayable, rest3')
  pure (.constructor inputs mutability, rest4)

/-- Parse a fallback signature:
`fallback ( ) modifiers?` -/
partial def parseFallback (cs : List Char) : Option (AbiItem × List Char) := do
  let rest0 ← parseLit "fallback" cs
  let rest1 ← parseChar '(' rest0
  let rest2 ← parseChar ')' rest1
  let rest2' ← parseExternal rest2
  let rest2'' := skipWS rest2'
  let (mutability, rest3) ←
    match parseMutability rest2'' with
    | some (m, r) => pure (m, r)
    | none => pure (.nonpayable, rest2'')
  pure (.fallback mutability, rest3)

/-- Parse a receive signature:
`receive ( ) modifiers?` -/
partial def parseReceive (cs : List Char) : Option (AbiItem × List Char) := do
  let rest0 ← parseLit "receive" cs
  let rest1 ← parseChar '(' rest0
  let rest2 ← parseChar ')' rest1
  let rest2' ← parseExternal rest2
  let rest2'' := skipWS rest2'
  -- consume optional payable modifier
  let rest3 := skipWS rest2''
  let rest4 ←
    match parseIdent rest3 with
    | some ("payable", r) => some r
    | _ => some rest3
  pure (.receive, rest4)

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

/-- Parse a list of ABI items from a multi-line string (one per line, or
semicolon-separated — but the canonical format omits semicolons). -/
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

end EvmAbi
