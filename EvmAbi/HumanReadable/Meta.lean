import EvmAbi.Ty
import EvmAbi.HumanReadable
import Lean

open Lean Elab Term Meta

namespace EvmAbi.HumanReadable.Meta

open EvmAbi (Ty AbiItem AbiParam StateMutability)
open EvmAbi.Ty
open EvmAbi.AbiItem
open EvmAbi (skipWS parseTypeFromString parseAbiItem parseParams)

/-! ## Syntax builders (return `Term`, no elaboration) -/

def mkListStx (elemTy : Term) (f : α → TermElabM Term) (xs : List α) : TermElabM Term := do
  match xs with
  | [] => `(@List.nil $elemTy)
  | x :: xs' => do
      let hd ← f x
      let tl ← mkListStx elemTy f xs'
      `($hd :: $tl)

partial def mkTyStx : Ty → TermElabM Term
  | .uint m => `(EvmAbi.Ty.uint $(quote m))
  | .int m => `(EvmAbi.Ty.int $(quote m))
  | .bool => `(EvmAbi.Ty.bool)
  | .address => `(EvmAbi.Ty.address)
  | .bytesN m => `(EvmAbi.Ty.bytesN $(quote m))
  | .bytes => `(EvmAbi.Ty.bytes)
  | .string => `(EvmAbi.Ty.string)
  | .array t => do let t' ← mkTyStx t; `(EvmAbi.Ty.array $t')
  | .fixedArray t n => do let t' ← mkTyStx t; `(EvmAbi.Ty.fixedArray $t' $(quote n))
  | .tuple ts => do
      let ts' ← mkListStx (← `(EvmAbi.Ty)) mkTyStx ts
      `(EvmAbi.Ty.tuple $ts')

def mkOptStrStx : Option String → TermElabM Term
  | none => `(Option.none)
  | some s => `(Option.some $(quote s))

def mkParamStx (p : AbiParam) : TermElabM Term := do
  let ty ← mkTyStx p.ty
  let name ← mkOptStrStx p.name
  let indexed := quote p.indexed
  `(EvmAbi.AbiParam.mk $ty $name $indexed)

def mkSMStx : StateMutability → TermElabM Term
  | .pure => `(EvmAbi.StateMutability.pure)
  | .view => `(EvmAbi.StateMutability.view)
  | .nonpayable => `(EvmAbi.StateMutability.nonpayable)
  | .payable => `(EvmAbi.StateMutability.payable)

partial def mkItemStx : AbiItem → TermElabM Term
  | .function name inputs outputs sm => do
      let inputs' ← mkListStx (← `(EvmAbi.AbiParam)) mkParamStx inputs
      let outputs' ← mkListStx (← `(EvmAbi.AbiParam)) mkParamStx outputs
      let sm' ← mkSMStx sm
      `(EvmAbi.AbiItem.function $(quote name) $inputs' $outputs' $sm')
  | .event name inputs => do
      let inputs' ← mkListStx (← `(EvmAbi.AbiParam)) mkParamStx inputs
      `(EvmAbi.AbiItem.event $(quote name) $inputs')
  | .error name inputs => do
      let inputs' ← mkListStx (← `(EvmAbi.AbiParam)) mkParamStx inputs
      `(EvmAbi.AbiItem.error $(quote name) $inputs')
  | .constructor inputs sm => do
      let inputs' ← mkListStx (← `(EvmAbi.AbiParam)) mkParamStx inputs
      let sm' ← mkSMStx sm
      `(EvmAbi.AbiItem.constructor $inputs' $sm')
  | .fallback sm => do
      let sm' ← mkSMStx sm
      `(EvmAbi.AbiItem.fallback $sm')
  | .receive =>
      `(EvmAbi.AbiItem.receive)

/-! ## Elaboration rules -/

elab "humanAbiType! " s:str : term => do
  let str := s.getString
  match parseTypeFromString str with
  | some ty => elabTerm (← mkTyStx ty) none
  | none => throwErrorAt s "Failed to parse human-readable ABI type: {str}"

elab "humanAbiItem! " s:str : term => do
  let str := s.getString
  match parseAbiItem str with
  | some item => elabTerm (← mkItemStx item) none
  | none => throwErrorAt s "Failed to parse human-readable ABI item: {str}"

elab "humanAbiParams! " s:str : term => do
  let str := s.getString
  match parseParams (str.toList) with
  | some (params, rest) =>
      if (skipWS rest).isEmpty then
        elabTerm (← mkListStx (← `(EvmAbi.AbiParam)) mkParamStx params) none
      else
        throwErrorAt s "Trailing characters after human-readable ABI params: {rest}"
  | none => throwErrorAt s "Failed to parse human-readable ABI params: {str}"

end EvmAbi.HumanReadable.Meta
