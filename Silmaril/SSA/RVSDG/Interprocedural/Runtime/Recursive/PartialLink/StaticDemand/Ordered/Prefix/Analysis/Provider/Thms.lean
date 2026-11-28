module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Provider.Defs

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation.Partial.Executable (Actions)
open NestedTheta.Equality (OpcodeCode)
open Isomorphism.RecursiveCall.Numbered (CaptureCode ExactValueCheck)
open Isomorphism.RecursiveCall.Numbered.Prefix (CheckedProvider Row)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {actions : Actions m σ}
variable {summary : MemberSummary V S} {extra providerImports : Ports (Ty V S)}
variable {providerSigs : List (Ports (Ty V S))}
variable {providerGraph : Omega Op providerImports [summary.fn.port] providerSigs}
variable {providerUnit : Nat} {providerL providerR : Tuple m.Val providerImports} {initial : σ}
variable {ids : GlobalRel} {keys : OpcodeCode (Instruction Op)} {captureCode : CaptureCode m}
variable {value : ValueSort V S} {clientFn : Function V S}

/-- Analyze one allocating numbered client. The operational provider and
its demand receipt concern the same actual links. The head import is checked
against the selected export, and its actual captures come from the demand
receipt's dispatch certificate. The λ still requires static resolution
for all formals and the actual initialized locals. -/
def analyzeAllocatingClient [DecidableEq σ]
    (provider : CheckedProvider actions ids keys captureCode providerUnit providerUnit providerGraph providerGraph
      providerL providerR (.head : Port [summary.fn.port] summary.fn.port) initial initial)
    (sound : Export actions summary
      (Executable.link actions providerUnit providerGraph providerL initial)
      (Executable.link actions providerUnit providerGraph providerR initial))
    (exactValue : ExactValueCheck m) (unitId : Nat)
    (inputsL inputsR : Tuple m.Val (summary.fn.port :: extra))
    (init : DeltaTerm Op (summary.fn.port :: extra) [] value)
    (binding : Binding Op (prepend summary sound.earlier) (summary.fn.port :: extra)
      [[.value (.global value)]] clientFn)
    (readyL : inputsL.get .head = sound.targetL →
      ∀ receipt : DeltaPrefix actions unitId init inputsL inputsR sound.store,
        binding.resolved sound.dispatch.left inputsL (receipt.left, PUnit.unit))
    (readyR : inputsR.get .head = sound.targetR →
      ∀ receipt : DeltaPrefix actions unitId init inputsL inputsR sound.store,
        binding.resolved sound.dispatch.right inputsR (receipt.right, PUnit.unit)) :
    Option (ExportAnalysis actions binding.summary
      (Executable.link actions unitId (sound.clientGraph init binding) inputsL sound.store)
      (Executable.link actions unitId (sound.clientGraph init binding) inputsR sound.store)) :=
  if unitId = providerUnit then none else
  match exactValue (inputsL.get .head) (provider.checked.valuesL.get .head),
      exactValue (inputsR.get .head) (provider.checked.valuesR.get .head) with
  | some exactL, some exactR => do
    let targetL := exactL.down.trans (congrArg (fun values => values.get .head)
      (Outcome.linked.inj (provider.checked.linkedL.symm.trans sound.linkedL)).1)
    let targetR := exactR.down.trans (congrArg (fun values => values.get .head)
      (Outcome.linked.inj (provider.checked.linkedR.symm.trans sound.linkedR)).1)
    let receipt ← DeltaPrefix.check actions unitId init inputsL inputsR sound.store
    let scope := sound.importScope.addInitialized receipt.left receipt.right
    let checked : scope.Checked actions := sound.importChecked.addInitialized receipt.left receipt.right
    let knownL := Known.callable (guard := sound.dispatch.left) (0 : Fin (sound.earlier.members.length + 1)) sound.targetL sound.capsL sound.resolvedL
    let knownR := Known.callable (guard := sound.dispatch.right) (0 : Fin (sound.earlier.members.length + 1)) sound.targetR sound.capsR sound.resolvedR
    let added ← checked.addWithImports binding inputsL inputsR
      (Row.headOnly (targetL.symm ▸ knownL)) (Row.headOnly (targetR.symm ▸ knownR))
      (readyL targetL receipt) (readyR targetR receipt)
    let linked := Scope.Checked.export (scope := scope)
      binding inputsL inputsR added unitId receipt.store
    let plan := Plan.finish (scope := scope)
      binding (readyL targetL receipt) (readyR targetR receipt)
    let tail := ModuleTerm.bind (.lambda binding.term) (.ret (lastExport [[.value (.global value)]] clientFn))
    pure ⟨linked.relink (link_delta inputsL tail receipt.linkedL) (link_delta inputsR tail receipt.linkedR),
      plan.problem, plan.mem_problem_iff⟩
  | _, _ => none

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix
