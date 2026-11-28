module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Admission.Prefix.Graph.Defs
import Silmaril.SSA.RVSDG.Interprocedural.Terms.Thms

/-! Pass a checked linked export as the callable import of a one-λ client. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix

open Continuation.Partial.Executable (Actions)
open NestedTheta.Equality (OpcodeCode)

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)}
variable {importsL importsR exports extra : Ports (Ty V S)}
variable {sigsL sigsR : List (Ports (Ty V S))}
variable {providerFn clientFn : Function V S}

/-- Check the actual numbered provider links and retain their dispatch
certificate, their typed exports and their post-link stores. -/
def checkGraphExport [DecidableEq (Ty V S)] (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    (actions : Actions m σ) (ids : GlobalRel) (ordinary : OrdinaryOutputs Op) (unitL unitR : Nat)
    (inputsL : Tuple m.Val importsL) (inputsR : Tuple m.Val importsR)
    (left : Omega Op importsL exports sigsL) (right : Omega Op importsR exports sigsR)
    (plan : GraphPlan left right) (port : Port exports providerFn.port) (storeL storeR : σ)
    (captureCode : CaptureCode m := .controlOnly m)
    (exactValue : ExactValueCheck m := fun _ _ => none)
    (exactGroup : ExactGroupCheck m := ExactGroupCheck.ofCaptures keys exactValue) :
    Option (CheckedExport actions.toPrimitives ids keys captureCode port
      (Executable.link actions unitL left inputsL storeL)
      (Executable.link actions unitR right inputsR storeR)) :=
  (walkExport keys captureCode exactValue exactGroup actions ids ordinary unitL unitR inputsL inputsR port
    (left := left.toTerm.region) (right := right.toTerm.region)
    PUnit.unit PUnit.unit storeL storeR plan .unseeded).map fun checked =>
      checked.reindex
        (by
          change Executable.link actions unitL left inputsL storeL = Executable.link actions unitL left.toTerm.toGraph inputsL storeL
          rw [Omega.toGraph_toTerm])
        (by
          change Executable.link actions unitR right inputsR storeR = Executable.link actions unitR right.toTerm.toGraph inputsR storeR
          rw [Omega.toGraph_toTerm])

/-- Check a numbered provider and keep its actual unit IDs in the result
type. The allocation-aware client checks its unit IDs against these
indices, which come from the provider's executable link. -/
structure CheckedProvider (actions : Actions m σ) (ids : GlobalRel)
    (keys : OpcodeCode (Instruction Op)) (captureCode : CaptureCode m)
    (unitL unitR : Nat)
    (left : Omega Op importsL exports sigsL) (right : Omega Op importsR exports sigsR)
    (inputsL : Tuple m.Val importsL) (inputsR : Tuple m.Val importsR)
    (port : Port exports providerFn.port) (storeL storeR : σ) where
  checked : CheckedExport actions.toPrimitives ids keys captureCode port
    (Executable.link actions unitL left inputsL storeL)
    (Executable.link actions unitR right inputsR storeR)

def checkGraphProvider [DecidableEq (Ty V S)] (keys : OpcodeCode (Instruction Op)) [DecidableEq keys.Key]
    (actions : Actions m σ) (ids : GlobalRel) (ordinary : OrdinaryOutputs Op) (unitL unitR : Nat)
    (inputsL : Tuple m.Val importsL) (inputsR : Tuple m.Val importsR)
    (left : Omega Op importsL exports sigsL) (right : Omega Op importsR exports sigsR)
    (plan : GraphPlan left right) (port : Port exports providerFn.port) (storeL storeR : σ)
    (captureCode : CaptureCode m := .controlOnly m)
    (exactValue : ExactValueCheck m := fun _ _ => none)
    (exactGroup : ExactGroupCheck m := ExactGroupCheck.ofCaptures keys exactValue) :
    Option (CheckedProvider actions ids keys captureCode unitL unitR left right inputsL inputsR port storeL storeR) :=
  (checkGraphExport keys actions ids ordinary unitL unitR inputsL inputsR left right plan port
    storeL storeR captureCode exactValue exactGroup).map fun checked => ⟨checked⟩

/-- Number one client λ and export its linked value at the sole result port. -/
def clientGraph {imports : Ports (Ty V S)} (definition : Lambda Op imports [] clientFn) :
    Omega Op imports [clientFn.port] [[clientFn.port]] :=
  ⟨⟨Fin.cases (.lambda definition) (fun i => i.elim0), .cons (.output (0 : Fin 1) .head) .nil⟩⟩

def Row.headOnly {family : Family m} {port : Ty V S} {values : Tuple m.Val (port :: extra)}
    (known : family (values.get .head)) : Row family values
  | _, .head => some ⟨known⟩
  | _, .tail _ => none

/-- Certify membership for the imported values by exact comparison with
the actual selected exports. -/
def CheckedExport.checkImport (exactValue : ExactValueCheck m)
    {primitives : Continuation.Partial.Primitives m σ} {ids : GlobalRel}
    {keys : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m}
    {port : Port exports providerFn.port} {outcomeL outcomeR : Outcome m σ exports}
    (provider : CheckedExport primitives ids keys captureCode port outcomeL outcomeR)
    (left right : m.Val providerFn.port) :
    Option (PLift (provider.familyL left ∧ provider.familyR right)) := do
  let sameL ← exactValue left (provider.valuesL.get port)
  let sameR ← exactValue right (provider.valuesR.get port)
  pure ⟨⟨sameL.down.symm ▸ provider.knownL, sameR.down.symm ▸ provider.knownR⟩⟩

/-- Add a client λ in the actual client locals, with membership only for
the independently checked provider import and for ordinary values. -/
def CheckedExport.extendClientLambda [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)}
    [DecidableEq keys.Key] {captureCode : CaptureCode m}
    (ordinary : OrdinaryOutputs Op) (exactValue : ExactValueCheck m)
    {primitives : Continuation.Partial.Primitives m σ} {ids : GlobalRel}
    {port : Port exports providerFn.port} {outcomeL outcomeR : Outcome m σ exports}
    (provider : CheckedExport primitives ids keys captureCode port outcomeL outcomeR)
    {pastL pastR : List (Ports (Ty V S))}
    (inputsL inputsR : Tuple m.Val (providerFn.port :: extra))
    (localsL : Locals m.Val pastL) (localsR : Locals m.Val pastR)
    (left : Lambda Op (providerFn.port :: extra) pastL clientFn)
    (right : Lambda Op (providerFn.port :: extra) pastR clientFn) :
    Option (PLift (LinkedFamily primitives ids keys captureCode
      (WithExport provider.familyL (linkedLambda left inputsL localsL))
      (WithExport provider.familyR (linkedLambda right inputsR localsR))
      (provider.keys.addLambda (lambdaBodyKey keys captureCode left inputsL localsL)
        (lambdaBodyKey keys captureCode right inputsR localsR)))) := do
  let known ← provider.checkImport exactValue (inputsL.get .head) (inputsR.get .head)
  provider.certified.addLambda keys ordinary
    ((Table.empty provider.familyL localsL).availableWithImports provider.certified.ordinaryL (Row.headOnly known.down.1))
    ((Table.empty provider.familyR localsR).availableWithImports provider.certified.ordinaryR (Row.headOnly known.down.2))
    left right

def CheckedExport.addClientLambda [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)}
    [DecidableEq keys.Key] {captureCode : CaptureCode m}
    (ordinary : OrdinaryOutputs Op) (exactValue : ExactValueCheck m)
    {primitives : Continuation.Partial.Primitives m σ} {ids : GlobalRel}
    {port : Port exports providerFn.port} {outcomeL outcomeR : Outcome m σ exports}
    (provider : CheckedExport primitives ids keys captureCode port outcomeL outcomeR)
    {pastL pastR : List (Ports (Ty V S))}
    (inputsL inputsR : Tuple m.Val (providerFn.port :: extra))
    (localsL : Locals m.Val pastL) (localsR : Locals m.Val pastR)
    (left : Lambda Op (providerFn.port :: extra) pastL clientFn)
    (right : Lambda Op (providerFn.port :: extra) pastR clientFn) :
    Option (PLift (ExportAdmission primitives ids
      (linkedLambda left inputsL localsL) (linkedLambda right inputsR localsR))) :=
  (provider.extendClientLambda ordinary exactValue inputsL inputsR localsL localsR left right).map fun checked =>
    ⟨checked.down.forExports .exported .exported⟩

/-- Extend the provider's dispatch family with a fresh client λ. Its first
import must equal the selected provider export on each side. Other
imports may be used through the ordinary-value rule. The client links
at the provider's final store and has no δ allocations of its own. -/
def admitClient [DecidableEq (Ty V S)] {keys : OpcodeCode (Instruction Op)} [DecidableEq keys.Key]
    {captureCode : CaptureCode m} (actions : Actions m σ) {ids : GlobalRel}
    (ordinary : OrdinaryOutputs Op) (exactValue : ExactValueCheck m)
    {port : Port exports providerFn.port} {outcomeL outcomeR : Outcome m σ exports}
    (provider : CheckedExport actions.toPrimitives ids keys captureCode port outcomeL outcomeR)
    (unitL unitR : Nat) (inputsL inputsR : Tuple m.Val (providerFn.port :: extra))
    (left right : Lambda Op (providerFn.port :: extra) [] clientFn) :
    Option (PLift (AdmittedExport actions.toPrimitives ids (fn := clientFn) .head
      (Executable.link actions unitL (clientGraph left) inputsL provider.storeL)
      (Executable.link actions unitR (clientGraph right) inputsR provider.storeR))) :=
  provider.addClientLambda ordinary exactValue inputsL inputsR
    (pastL := []) (pastR := []) PUnit.unit PUnit.unit left right

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.Isomorphism.RecursiveCall.Numbered.Prefix
