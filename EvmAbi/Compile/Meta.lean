import EvmAbi.Compile
import EvmAbi.Compile.Decode
import EvmAbi.HumanReadable.Meta
import Lean

/-!
# EvmAbi.Compile.Meta

The **ABI compiler**: `abi_encoder foo "…"` reads an ABI type (or a whole
function signature) at elaboration time, walks it once, and emits Lean
definitions specialised to that type — plus, for each one, a machine-checked
theorem that it encodes exactly what the verified generic encoder encodes.

What the type decides, the compiler decides *once*, at compile time, instead
of once per call (or, for arrays, once per element):

* which clause of `putBA` applies — the emitted code has no `Ty` to match on;
* whether each component is static or dynamic — no `isStatic` at run time;
* the size of the head section, and therefore the first tail offset — a
  numeral in the emitted code;
* that the components form a list at all — `partsOfTupleBA` allocates a
  `List Part` which `putParts` then walks three times (`headSizes`,
  `putHeads`, `putTails`); compiled tuples are straight-line code and
  compiled arrays are a single loop.

The emitted code is written against the abstract machine in `EvmAbi.Compile`
(`Acc.start`/`static`/`dyn`/`finish` and the element loop, `cons`/`elems` on
the decoder side), whose steps are proved correct there once and for all.  This module never invents a
proof: for every definition it prints, it prints the corresponding lemma
application, and Lean's kernel checks it.  A compiled encoder that is wrong
therefore cannot be produced — the command fails at compile time instead.

```lean
import EvmAbi.Compile.Meta
open EvmAbi.Compile.Meta

abi_encoder transferArgs "transfer(address to, uint256 amount)"

#check @transferArgs      -- ValBA transferArgs.ty → ByteArray
#check @transferArgs_eq   -- ∀ v, transferArgs v = EvmAbi.encode transferArgs.ty v
#print transferArgs.put   -- the generated code
```

The declarations the command emits, for a name `foo`:

| name | what it is |
|---|---|
| `foo.ty` | the `Ty` that was compiled (an `abbrev`) |
| `foo.node…` | the compiled encoder of each compound sub-type |
| `foo.node…_denotes` | `Denotes` for each of those — its correctness |
| `foo.put` / `foo.put_denotes` | the compiled encoder in builder form |
| `foo` | the encoder users call: `ValBA foo.ty → ByteArray` |
| `foo_eq` | `foo v = EvmAbi.encode foo.ty v` |
| `foo_decodeStrict` | the roundtrip, inherited from `decodeStrict_encode` |
-/

open Lean Elab Command Term Meta

namespace EvmAbi.Compile.Meta

open EvmAbi (Ty)
open EvmAbi.HumanReadable.Meta (mkTyStx)

/-! ## the leaves

A leaf compiles to a single `put…` call, so it is inlined at its use site
rather than given a definition of its own. -/

/-- The compiled encoder of a leaf type, as a function. -/
def leafFn : Ty → TermElabM Term
  | .uint _ => `(fun v => EvmAbi.putUint v.val)
  | .int _ => `(fun v => EvmAbi.putInt v.val)
  | .bool => `(fun v => EvmAbi.putBool v)
  | .address => `(fun v => EvmAbi.putAddress v.val)
  | .bytesN _ => `(fun v => EvmAbi.putBytesNBA v.val)
  | .bytes => `(fun v => EvmAbi.putBytesBA v.val)
  | .string => `(fun v => EvmAbi.putString v.val)
  | t => throwError "abi_encoder: {repr t} is not a leaf type"

/-- The compiled encoder of a leaf type, applied to a value. -/
def leafApp (t : Ty) (x : Term) : TermElabM Term :=
  match t with
  | .uint _ => `(EvmAbi.putUint ($x).val)
  | .int _ => `(EvmAbi.putInt ($x).val)
  | .bool => `(EvmAbi.putBool $x)
  | .address => `(EvmAbi.putAddress ($x).val)
  | .bytesN _ => `(EvmAbi.putBytesNBA ($x).val)
  | .bytes => `(EvmAbi.putBytesBA ($x).val)
  | .string => `(EvmAbi.putString ($x).val)
  | t => throwError "abi_encoder: {repr t} is not a leaf type"

/-- The correctness of a leaf's compiled encoder — a lemma from
`EvmAbi.Compile`, never a proof this module builds. -/
def leafProof : Ty → TermElabM Term
  | .uint m => `(EvmAbi.Compile.denotes_uint $(quote m))
  | .int m => `(EvmAbi.Compile.denotes_int $(quote m))
  | .bool => `(EvmAbi.Compile.denotes_bool)
  | .address => `(EvmAbi.Compile.denotes_address)
  | .bytesN m => `(EvmAbi.Compile.denotes_bytesN $(quote m))
  | .bytes => `(EvmAbi.Compile.denotes_bytes)
  | .string => `(EvmAbi.Compile.denotes_string)
  | t => throwError "abi_encoder: {repr t} is not a leaf type"

/-! ## compiled nodes -/

/-- What the compiler produced for a sub-type: a leaf, inlined at its use
sites, or a compound node with a definition and its correctness theorem. -/
inductive Node where
  /-- A leaf type: emitted inline. -/
  | leaf (t : Ty)
  /-- A compound type: `fn` is its encoder, `thm` its `Denotes` theorem. -/
  | node (t : Ty) (fn thm : Name)

/-- The node's code: the definition it was emitted as, or the leaf's inline
form.  `leaf` is how the backend doing the compiling renders a leaf. -/
def Node.code (leaf : Ty → TermElabM Term) : Node → TermElabM Term
  | .leaf t => leaf t
  | .node _ fn _ => pure (mkIdent fn)

/-- The node's correctness, the same way. -/
def Node.proof (leafPf : Ty → TermElabM Term) : Node → TermElabM Term
  | .leaf t => leafPf t
  | .node _ _ thm => pure (mkIdent thm)

/-- The node's encoder applied to a value — a leaf is applied *inline*, so
compiled tuples read `putUint v.1.val` rather than a beta-redex. -/
def Node.appStx : Node → Term → TermElabM Term
  | .leaf t, x => leafApp t x
  | .node _ fn _, x => `($(mkIdent fn) $x)

/-! ## the emitter -/

/-- `v.2.….2.1`: the `i`-th component of a tuple value. -/
private def projStx (x : Term) : Nat → TermElabM Term
  | 0 => `(($x).1)
  | n + 1 => do projStx (← `(($x).2)) n

/-- Emit one compiled node: the definition, then the theorem that says what
it is.  `sig` is the type of the code, `contract` the statement it satisfies —
`Denotes` when compiling an encoder, `Reads` when compiling a decoder. -/
private def emitNode (fn thm : Name) (sig contract body proof : Term) : CommandElabM Unit := do
  elabCommand (← `(def $(mkIdent fn) : $sig := $body))
  elabCommand (← `(theorem $(mkIdent thm) : $contract := $proof))

/-- The type and contract of compiled code, per direction. -/
private def encSig (tyStx : Term) : TermElabM Term :=
  `(EvmAbi.ValBA $tyStx → EvmAbi.Builder)

private def encContract (tyStx : Term) (fn : Name) : TermElabM Term :=
  `(EvmAbi.Compile.Denotes $tyStx $(mkIdent fn))

private def decSig (tyStx : Term) : TermElabM Term :=
  `(ByteArray → Nat → Option (EvmAbi.ValBA $tyStx × Nat))

private def decContract (tyStx : Term) (fn : Name) : TermElabM Term :=
  `(EvmAbi.Compile.Reads $tyStx $(mkIdent fn))

/-- The names of the `i`-th compiled node: `foo.node3` and `foo.node3_denotes`
(`dnode`/`_reads` for a decoder), unless this is the root, which is named. -/
private def nodeNames (root : Name) (tag suffix : String) (i : Nat) (top? : Option Name) :
    Name × Name :=
  let fn := top?.getD (root ++ Name.mkSimple s!"{tag}{i}")
  (fn, Name.appendAfter fn suffix)

/-- Compile one type: emit a definition (and its correctness theorem) for
every compound sub-type, bottom up, and return the node for `t` itself.
`i` is the next free node index. -/
private partial def compileTy (root : Name) (t : Ty) (i : Nat)
    (top? : Option Name := none) : CommandElabM (Node × Nat) := do
  match t with
  | .uint _ | .int _ | .bool | .address | .bytesN _ | .bytes | .string => return (.leaf t, i)
  | .array e | .fixedArray e _ =>
      let (en, i) ← compileTy root e i
      let (fn, thm) := nodeNames root "node" "_denotes" i top?
      let tyStx ← liftTermElabM (mkTyStx t)
      let elemFn ← liftTermElabM (en.code leafFn)
      let elemPf ← liftTermElabM (en.proof leafProof)
      let hs := quote e.headSize
      let isArray := match t with | .array _ => true | _ => false
      -- the instruction the loop runs is picked here, not per element at run
      -- time; `T[]` prefixes the length word, `T[k]` does not
      let (step, stepPf) ← liftTermElabM do
        if e.isStatic then
          pure (← `(EvmAbi.Compile.Acc.static),
            ← `(EvmAbi.Compile.Acc.Inv.stepStatic (by decide) $elemPf))
        else
          pure (← `(EvmAbi.Compile.Acc.dyn),
            ← `(EvmAbi.Compile.Acc.Inv.stepDyn (by decide) $elemPf))
      let section_ ← liftTermElabM
        `(((EvmAbi.Compile.Acc.start (v.val.length * $hs)).elems $step $elemFn v.val).finish)
      let body ← liftTermElabM (do
        if isArray then `(fun v => EvmAbi.putUint v.val.length ++ $section_)
        else `(fun v => $section_))
      let proof ← liftTermElabM (do
        if isArray then `(EvmAbi.Compile.denotes_array (by decide) $stepPf)
        else `(EvmAbi.Compile.denotes_fixedArray (by decide) $stepPf))
      emitNode fn thm (← liftTermElabM (encSig tyStx)) (← liftTermElabM (encContract tyStx fn))
        body proof
      return (.node t fn thm, i + 1)
  | .tuple ts =>
      let mut i := i
      let mut nodes : Array Node := #[]
      for c in ts do
        let (cn, i') ← compileTy root c i
        nodes := nodes.push cn
        i := i'
      let (fn, thm) := nodeNames root "node" "_denotes" i top?
      let tyStx ← liftTermElabM (mkTyStx t)
      -- the head section is a compile-time constant, so the first tail
      -- offset is a numeral and every later one an `O(1)` addition
      let hss := quote (Ty.headSizeSum ts)
      let vId := mkIdent (← MonadQuotation.addMacroScope `v)
      let (body, proof) ← liftTermElabM do
        let mut st ← `(EvmAbi.Compile.Acc.start $hss)
        let mut pf ← `(EvmAbi.Compile.Acc.start_inv $hss)
        let mut k := 0
        for (c, cn) in ts.zip nodes.toList do
          let x ← projStx vId k
          k := k + 1
          let cb ← cn.appStx x
          let cp ← do let p ← cn.proof leafProof; `($p $x)
          if c.isStatic then
            st ← `(($st).static $cb)
            pf ← `(($pf).static (by decide) $cp)
          else
            st ← `(($st).dyn $cb)
            pf ← `(($pf).dyn (by decide) $cp)
        let body ← `(fun $vId:ident => ($st).finish)
        let unfold ← if ts.isEmpty then
            `(tactic| simp only [EvmAbi.Compile.partsOfTupleBA_nil])
          else
            `(tactic| simp only [EvmAbi.Compile.partsOfTupleBA_cons,
                EvmAbi.Compile.partsOfTupleBA_nil])
        let proof ← `(by
          intro $vId:ident
          refine EvmAbi.Compile.toList_tuple (by decide) _ ?_
          $unfold:tactic
          exact $pf)
        return (body, proof)
      emitNode fn thm (← liftTermElabM (encSig tyStx)) (← liftTermElabM (encContract tyStx fn))
        body proof
      return (.node t fn thm, i + 1)

/-! ## the command -/

/-- Read a type, or the argument list of a whole signature: `"(uint256,bool)"`
and `"transfer(address,uint256)"` both name the type of a call's arguments. -/
def parseTarget (s : String) : Option Ty :=
  match EvmAbi.parseTypeFromString s with
  | some t => some t
  | none =>
      -- `transfer(address,uint256)` is how a signature is usually written;
      -- the item parser wants the keyword, so supply it.
      match EvmAbi.parseAbiItem s <|> EvmAbi.parseAbiItem ("function " ++ s) with
      | some (.function _ inputs _ _) | some (.event _ inputs)
      | some (.error _ inputs) | some (.constructor inputs _) =>
          some (.tuple (inputs.map (·.ty)))
      | _ => none

/-! ## the decoder side

Same shape: leaves are the readers of `EvmAbi.Compile.Decode`, compound nodes
get a definition and a `Reads` theorem, and the head sizes the emitter folds
to numerals are justified by `rfl` against `Ty.headSize`/`headSizeSum`. -/

/-- The reader of a leaf type. -/
def leafRead : Ty → TermElabM Term
  | .uint m => `(EvmAbi.Compile.readUint $(quote m))
  | .int m => `(EvmAbi.Compile.readInt $(quote m))
  | .bool => `(EvmAbi.Compile.readBool)
  | .address => `(EvmAbi.Compile.readAddress)
  | .bytesN m => `(EvmAbi.Compile.readBytesN $(quote m))
  | .bytes => `(EvmAbi.Compile.readBytes)
  | .string => `(EvmAbi.Compile.readString)
  | t => throwError "abi_decoder: {repr t} is not a leaf type"

/-- The correctness of a leaf's reader. -/
def leafReadProof : Ty → TermElabM Term
  | .uint m => `(EvmAbi.Compile.reads_uint $(quote m))
  | .int m => `(EvmAbi.Compile.reads_int $(quote m))
  | .bool => `(EvmAbi.Compile.reads_bool)
  | .address => `(EvmAbi.Compile.reads_address)
  | .bytesN m => `(EvmAbi.Compile.reads_bytesN $(quote m))
  | .bytes => `(EvmAbi.Compile.reads_bytes)
  | .string => `(EvmAbi.Compile.reads_string)
  | t => throwError "abi_decoder: {repr t} is not a leaf type"

/-- How one component of type `t` is read — `elemStatic` or `elemDyn` — and
the proof that reading it that way is what the generic decoder does.  This is
the only place the static/dynamic split survives compilation: the tuple chain
and the element loop are the same code either way. -/
def elemReader (t : Ty) (dp : Term) : TermElabM (Term × Term) := do
  if t.isStatic then
    return (← `(EvmAbi.Compile.elemStatic),
      ← `(EvmAbi.Compile.elemStatic_eq (by decide) $dp))
  else
    return (← `(EvmAbi.Compile.elemDyn),
      ← `(EvmAbi.Compile.elemDyn_eq (by decide) $dp))

/-- Compile a decoder for one type: a definition (and its `Reads` theorem)
per compound sub-type, bottom up. -/
private partial def compileDec (root : Name) (t : Ty) (i : Nat)
    (top? : Option Name := none) : CommandElabM (Node × Nat) := do
  match t with
  | .uint _ | .int _ | .bool | .address | .bytesN _ | .bytes | .string => return (.leaf t, i)
  | .array e | .fixedArray e _ =>
      let (en, i) ← compileDec root e i
      let (fn, thm) := nodeNames root "dnode" "_reads" i top?
      let tyStx ← liftTermElabM (mkTyStx t)
      let elemRead ← liftTermElabM (en.code leafRead)
      let elemPf ← liftTermElabM (en.proof leafReadProof)
      let hs := quote e.headSize
      let isArray := match t with | .array _ => true | _ => false
      -- the reader the loop runs is picked here, not per element at run time
      let (mk, erPf) ← liftTermElabM (elemReader e elemPf)
      let (loop, loopPf) ← liftTermElabM do
        pure (← `(EvmAbi.Compile.elems $mk $elemRead), ← `(EvmAbi.Compile.elems_eq $erPf))
      let (body, proof) ← liftTermElabM (do
        if isArray then
          pure (← `(EvmAbi.Compile.readArray $hs $loop),
            ← `(EvmAbi.Compile.reads_array rfl $loopPf))
        else
          pure (← `(EvmAbi.Compile.readFixedArray $hs $loop),
            ← `(EvmAbi.Compile.reads_fixedArray rfl $loopPf)))
      emitNode fn thm (← liftTermElabM (decSig tyStx)) (← liftTermElabM (decContract tyStx fn))
        body proof
      return (.node t fn thm, i + 1)
  | .tuple ts =>
      let mut i := i
      let mut nodes : Array Node := #[]
      for c in ts do
        let (cn, i') ← compileDec root c i
        nodes := nodes.push cn
        i := i'
      let (fn, thm) := nodeNames root "dnode" "_reads" i top?
      let tyStx ← liftTermElabM (mkTyStx t)
      let hss := quote (Ty.headSizeSum ts)
      let (body, proof) ← liftTermElabM do
        -- the component chain, built from the right: each link knows at
        -- compile time whether its component sits in the head or behind an
        -- offset word
        let mut chain ← `(EvmAbi.Compile.consNil)
        let mut chainPf ← `(EvmAbi.Compile.consNil_eq)
        for (c, cn) in (ts.zip nodes.toList).reverse do
          let (mk, erPf) ← elemReader c (← cn.proof leafReadProof)
          chain ← `(EvmAbi.Compile.cons $mk $(← cn.code leafRead) $chain)
          chainPf ← `(EvmAbi.Compile.cons_eq $erPf $chainPf)
        pure (← `(EvmAbi.Compile.readTuple $hss $chain),
          ← `(EvmAbi.Compile.reads_tuple rfl $chainPf))
      emitNode fn thm (← liftTermElabM (decSig tyStx)) (← liftTermElabM (decContract tyStx fn))
        body proof
      return (.node t fn thm, i + 1)

/-! ## the commands -/

/-- Emit the type abbreviation and return its identifier. -/
private def emitTy (root : Name) (t : Ty) : CommandElabM Ident := do
  let tyStx ← liftTermElabM (mkTyStx t)
  let tyId := mkIdent (root ++ `ty)
  elabCommand (← `(abbrev $tyId : EvmAbi.Ty := $tyStx))
  return tyId

/-- Emit the compiled encoder and its theorems, under the name `encName`. -/
private def emitEncoder (root : Name) (t : Ty) (tyId : Ident) (encName : Name) :
    CommandElabM Unit := do
  let putId := mkIdent (root ++ `put)
  let putThmId := mkIdent (root ++ `put_denotes)
  let (node, _) ← compileTy root t 0 (top? := some (root ++ `put))
  -- a leaf root has no definition of its own yet: give it one, so that
  -- `foo.put` names the compiled encoder whatever the type is
  if let .leaf _ := node then
    emitNode (root ++ `put) (root ++ `put_denotes) (← liftTermElabM (encSig tyId))
      (← liftTermElabM (encContract tyId (root ++ `put)))
      (← liftTermElabM (node.code leafFn)) (← liftTermElabM (node.proof leafProof))
  let encId := mkIdent encName
  elabCommand (← `(def $encId : EvmAbi.ValBA $tyId → ByteArray := fun v => ($putId v).run))
  elabCommand (← `(theorem $(mkIdent (Name.appendAfter encName "_eq")) :
    ∀ (v : EvmAbi.ValBA $tyId), $encId v = EvmAbi.encode $tyId v :=
      EvmAbi.Compile.run_eq_encode $putThmId))
  elabCommand (← `(theorem $(mkIdent (Name.appendAfter encName "_decodeStrict")) :
    ∀ (v : EvmAbi.ValBA $tyId), ($encId v).size < 2 ^ 256 →
      EvmAbi.decodeStrict $tyId ($encId v) = some v :=
      fun v hb => EvmAbi.Compile.decodeStrict_run $putThmId (by decide) v hb))

/-- Emit the compiled strict decoder and its theorems, under the name
`decName`. -/
private def emitDecoder (root : Name) (t : Ty) (tyId : Ident) (decName : Name)
    (wholeApi : Bool := false) : CommandElabM Unit := do
  let readId := mkIdent (root ++ `read)
  let readThmId := mkIdent (root ++ `read_reads)
  let (node, _) ← compileDec root t 0 (top? := some (root ++ `read))
  if let .leaf _ := node then
    emitNode (root ++ `read) (root ++ `read_reads) (← liftTermElabM (decSig tyId))
      (← liftTermElabM (decContract tyId (root ++ `read)))
      (← liftTermElabM (node.code leafRead)) (← liftTermElabM (node.proof leafReadProof))
  let decId := mkIdent decName
  elabCommand (← `(def $decId : ByteArray → Option (EvmAbi.ValBA $tyId) :=
    fun ba => EvmAbi.Compile.runStrict $readId ba))
  elabCommand (← `(theorem $(mkIdent (Name.appendAfter decName "_eq")) :
    ∀ (ba : ByteArray), $decId ba = EvmAbi.decodeStrict $tyId ba :=
      EvmAbi.Compile.runStrict_eq $readThmId))
  elabCommand (← `(theorem $(mkIdent (Name.appendAfter decName "_encode")) :
    ∀ (v : EvmAbi.ValBA $tyId), (EvmAbi.encode $tyId v).size < 2 ^ 256 →
      $decId (EvmAbi.encode $tyId v) = some v :=
      fun v hb => EvmAbi.Compile.runStrict_encode $readThmId (by decide) v hb))
  elabCommand (← `(theorem $(mkIdent (Name.appendAfter decName "_uniq")) :
    ∀ (ba : ByteArray) (v : EvmAbi.ValBA $tyId), $decId ba = some v →
      EvmAbi.encode $tyId v = ba :=
      fun ba v h => EvmAbi.Compile.encode_of_runStrict $readThmId (by decide) ba v h))
  -- the runtime API has four public names; a codec compiles all of them
  if wholeApi then
    let preId := mkIdent (root ++ `decode)
    let canId := mkIdent (root ++ `isCanonical)
    elabCommand (← `(def $preId : ByteArray → Option (EvmAbi.ValBA $tyId × Nat) :=
      fun ba => $readId ba 0))
    elabCommand (← `(theorem $(mkIdent (root ++ `decode_eq)) :
      ∀ (ba : ByteArray), $preId ba = EvmAbi.decode $tyId ba :=
        fun ba => $readThmId ba 0))
    elabCommand (← `(def $canId : ByteArray → Bool := fun ba => ($decId ba).isSome))
    elabCommand (← `(theorem $(mkIdent (root ++ `isCanonical_eq)) :
      ∀ (ba : ByteArray), $canId ba = true ↔ EvmAbi.IsCanonical $tyId ba := by
      intro ba
      show ($decId ba).isSome = true ↔ _
      rw [$(mkIdent (Name.appendAfter decName "_eq")):ident ba]
      exact Iff.rfl))

/-- Parse the command's string argument, or fail with a useful message.

The validity check is defensive: the human-readable parser only produces types
that satisfy `Ty.Valid` — it rejects `uint7`, `bytes33`, an array whose element
type has no head — so no string should reach it.  The emitted proofs are
`by decide` against exactly this predicate, so it is checked rather than
assumed. -/
private def targetOf (cmd : String) (s : TSyntax `str) : CommandElabM Ty := do
  let str := s.getString
  let some t := parseTarget str
    | throwErrorAt s "{cmd}: not an ABI type or signature: {str}"
  unless decide t.Valid do
    throwErrorAt s "{cmd}: {str} is not a valid ABI type"
  return t

/--
Compile an ABI encoder for a type, at elaboration time.

`abi_encoder foo "(address, uint256)"` emits a `ByteArray` encoder `foo`
specialised to that type — no `Ty` dispatch, no `List Part`, offsets folded
to numerals — together with `foo_eq`, the machine-checked proof that it
agrees with `EvmAbi.encode`, and `foo_decodeStrict`, the roundtrip inherited
from it.  A signature (`"transfer(address to, uint256 amount)"`) compiles the
encoder of its argument list.  See the module docstring for the full list of
emitted names.
-/
elab "abi_encoder " nm:ident s:str : command => do
  let t ← targetOf "abi_encoder" s
  let root := nm.getId
  let tyId ← emitTy root t
  emitEncoder root t tyId root

/--
Compile an ABI decoder for a type, at elaboration time.

`abi_decoder foo "(address, uint256)"` emits a strict decoder
`foo : ByteArray → Option (ValBA foo.ty)` specialised to that type — no `Ty`
dispatch, no `isStatic` per component or element — together with `foo_eq`
(it *is* `EvmAbi.decodeStrict`), `foo_encode` (it reads back what `encode`
wrote) and `foo_uniq` (a buffer it accepts is the encoding of what it read).
-/
elab "abi_decoder " nm:ident s:str : command => do
  let t ← targetOf "abi_decoder" s
  let root := nm.getId
  let tyId ← emitTy root t
  emitDecoder root t tyId root

/--
Compile both directions at once.

`abi_codec foo "(address, uint256)"` compiles all four names of the runtime API
— `foo.encode`, `foo.decode` (prefix), `foo.decodeStrict`, `foo.isCanonical` —
each with the theorem that it *is* its `EvmAbi` counterpart, plus
`foo.roundtrip`: what the compiled encoder writes, the compiled decoder reads
back.
-/
elab "abi_codec " nm:ident s:str : command => do
  let t ← targetOf "abi_codec" s
  let root := nm.getId
  let tyId ← emitTy root t
  emitEncoder root t tyId (root ++ `encode)
  emitDecoder root t tyId (root ++ `decodeStrict) (wholeApi := true)
  let encId := mkIdent (root ++ `encode)
  let decId := mkIdent (root ++ `decodeStrict)
  let encEqId := mkIdent (Name.appendAfter (root ++ `encode) "_eq")
  let decEncId := mkIdent (Name.appendAfter (root ++ `decodeStrict) "_encode")
  elabCommand (← `(theorem $(mkIdent (root ++ `roundtrip)) :
    ∀ (v : EvmAbi.ValBA $tyId), ($encId v).size < 2 ^ 256 →
      $decId ($encId v) = some v := by
    intro v hb
    rw [$encEqId:ident v] at hb ⊢
    exact $decEncId v hb))

end EvmAbi.Compile.Meta
