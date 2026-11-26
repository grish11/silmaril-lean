module

public import Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Provider.Relocation.Defs
import Silmaril.Proofs.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix.Analysis.Provider.Relocation.Transport

@[expose] public section

namespace Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix

open Continuation (Stack)
open Continuation.Partial (Config Primitives Step)
open Continuation.Partial.Executable (Actions)
open Isomorphism (OutcomesRelated)
open Isomorphism.RecursiveCall (Admitted ClosedFamily Frames TupleIn)
open NestedTheta.Liveness (Demand)

open Isomorphism.RecursiveCall.Numbered (ExactValueCheck ordinaryPorts)
open Isomorphism.RecursiveCall.Numbered.Prefix (AdmittedExport AllocatingClient Row)

universe u v w
variable {V S : Type u} {Op : Dialect.{u, v} (ValueSort V S) S}
variable {m : Machine.{u, v, w} Op} {σ : Type (max u v w)} {actions : Actions m σ}
variable {imports extra : Ports (Ty V S)} {value : ValueSort V S} {fn : Function V S}
variable {table : MemberSummaries V S} {shifted : Bool}

theorem AllocationPlan.link_initialized
    (layout : AllocationPlan Op table imports fn value shifted) (actions : Actions m σ)
    (unit : Nat) (inputs : Tuple m.Val imports) (initial : σ)
    {values : Tuple m.Val [.value (.global value)]} {store : σ}
    (linked : layout.linkDelta actions unit inputs initial = .linked values store) :
    Executable.link actions unit layout.numbered.toGraph inputs initial =
      .linked (.cons (layout.binding.value inputs ((AllocatingClient.initialLocals m shifted).snoc values)) .nil) store :=
  (layout.numbered.link_body actions unit inputs initial).trans (congrArg (fun (outcome : Outcome m σ [.value (.global value)]) =>
    match outcome with
    | .undefined failure => Outcome.undefined failure
    | .linked values middle => Outcome.linked (.cons (layout.binding.value inputs
      ((AllocatingClient.initialLocals m shifted).snoc values)) .nil) middle) linked)

/-- Use actual successful δ outcomes to run the final λ's GenKill
analysis and index its dispatch receipt by the actual numbered links. -/
def AllocationPlan.analyze
    (layout : AllocationPlan Op table imports fn value shifted)
    (dispatch : Dispatch actions table) (unit : Nat) (inputsL inputsR : Tuple m.Val imports) (initial : σ)
    (receipt : layout.Initialized actions unit inputsL inputsR initial)
    (importedL : Row (Known dispatch.left) inputsL) (importedR : Row (Known dispatch.right) inputsR)
    (readyL : layout.binding.resolved dispatch.left inputsL
      ((AllocatingClient.initialLocals m shifted).snoc receipt.left))
    (readyR : layout.binding.resolved dispatch.right inputsR
      ((AllocatingClient.initialLocals m shifted).snoc receipt.right)) :
    Option (ExportAnalysis actions layout.binding.summary
      (Executable.link actions unit layout.numbered.toGraph inputsL initial)
      (Executable.link actions unit layout.numbered.toGraph inputsR initial)) := do
  let scope := (allocationScope dispatch shifted).addInitialized receipt.left receipt.right
  let checked : scope.Checked actions := (allocationChecked dispatch shifted).addInitialized receipt.left receipt.right
  let added ← checked.addWithImports layout.binding inputsL inputsR importedL importedR readyL readyR
  let exportReceipt := Scope.Checked.export (scope := scope) layout.binding inputsL inputsR added unit receipt.store
  let plan := Plan.finish (scope := scope) layout.binding readyL readyR
  let actualL := layout.link_initialized actions unit inputsL initial receipt.linkedL
  let actualR := layout.link_initialized actions unit inputsR initial receipt.linkedR
  pure ⟨exportReceipt.relink (actualL.trans exportReceipt.linkedL.symm) (actualR.trans exportReceipt.linkedR.symm),
    plan.problem, plan.mem_problem_iff⟩

/-- Analyze either physical client layout from an actual provider demand
receipt. Each import check is against the closure selected by that receipt;
the successful δ rows supply the actual locals for body resolution. -/
def AllocationPlan.analyzeImported [DecidableEq σ]
    {summary : MemberSummary V S} {providerL providerR : Outcome m σ [summary.fn.port]}
    (sound : Export actions summary providerL providerR)
    (layout : AllocationPlan Op (prepend summary sound.earlier) (summary.fn.port :: extra) fn value shifted)
    (exact : ExactValueCheck m) (unit : Nat)
    (inputsL inputsR : Tuple m.Val (summary.fn.port :: extra))
    (readyL : inputsL.get .head = sound.targetL →
      ∀ receipt : layout.Initialized actions unit inputsL inputsR sound.store,
        layout.binding.resolved sound.dispatch.left inputsL ((AllocatingClient.initialLocals m shifted).snoc receipt.left))
    (readyR : inputsR.get .head = sound.targetR →
      ∀ receipt : layout.Initialized actions unit inputsL inputsR sound.store,
        layout.binding.resolved sound.dispatch.right inputsR ((AllocatingClient.initialLocals m shifted).snoc receipt.right)) :
    Option (ExportAnalysis actions layout.binding.summary
      (Executable.link actions unit layout.numbered.toGraph inputsL sound.store)
      (Executable.link actions unit layout.numbered.toGraph inputsR sound.store)) :=
  match exact (inputsL.get .head) sound.targetL, exact (inputsR.get .head) sound.targetR with
  | some sameL, some sameR => do
    let initialized ← LinkedRows.check (layout.linkDelta actions unit inputsL sound.store)
      (layout.linkDelta actions unit inputsR sound.store)
    let slot : Fin (sound.earlier.members.length + 1) := 0
    let knownL := Known.callable (guard := sound.dispatch.left) slot sound.targetL sound.capsL sound.resolvedL
    let knownR := Known.callable (guard := sound.dispatch.right) slot sound.targetR sound.capsR sound.resolvedR
    layout.analyze sound.dispatch unit inputsL inputsR sound.store initialized
      (Row.headOnly (sameL.down.symm ▸ knownL)) (Row.headOnly (sameR.down.symm ▸ knownR))
      (readyL sameL.down initialized) (readyR sameR.down initialized)
  | _, _ => none

/-- A shared result-demand summary selects the same ports on both layouts.
After replacement, start the actual numbered jobs with the existing
relocation and dispatch certificates. The returned invariant is consumed
by the linked family's return, block and finite-prefix transport. -/
theorem ExportAnalysis.relocated_substituted_starts {summary : MemberSummary V S} {ids : GlobalRel}
    {importsL importsR : Ports (Ty V S)}
    {sigsL sigsR : List (Ports (Ty V S))} {unitL unitR : Nat}
    {graphL : Omega Op importsL [summary.fn.port] sigsL} {graphR : Omega Op importsR [summary.fn.port] sigsR}
    {inputsL : Tuple m.Val importsL} {inputsR : Tuple m.Val importsR} {initialL initialR : σ}
    {rename : Nat → Nat}
    (a : ExportAnalysis actions summary (Executable.link actions unitL graphL inputsL initialL)
      (Executable.link actions unitL graphL inputsL initialL))
    (b : ExportAnalysis actions summary (Executable.link actions unitR graphR inputsR initialR)
      (Executable.link actions unitR graphR inputsR initialR))
    (linked : OutcomesRelated m ids σ rename [summary.fn.port]
      (Executable.link actions unitL graphL inputsL initialL)
      (Executable.link actions unitR graphR inputsR initialR))
    (admitted : AdmittedExport actions.toPrimitives ids (fn := summary.fn) .head
      (Executable.link actions unitL graphL inputsL initialL)
      (Executable.link actions unitR graphR inputsR initialR))
    (demand : Demand) {argsL argsR replacementsL replacementsR : Tuple m.Val summary.fn.args}
    (args : TupleRelated m ids argsL argsR) (replacements : TupleRelated m ids replacementsL replacementsR)
    (ordinary : ordinaryPorts summary.fn.args = true) :
    ∃ familyL familyR, ∃ startL startR : Config m σ summary.fn.results,
      Executable.start actions unitL graphL inputsL .head (a.substituteDeadFormals demand argsL replacementsL)
        initialL = .ok startL ∧
      Executable.start actions unitR graphR inputsR .head (b.substituteDeadFormals demand argsR replacementsR)
        initialR = .ok startR ∧
      ClosedFamily actions.toPrimitives ids familyL familyR ∧ Admitted m ids familyL familyR startL startR :=
  RelocationProofs.substituted_starts a b linked admitted demand args replacements ordinary

/-- Resume two reached saved suffixes with related admitted packets at a
common store. The relocation block certificate supplies the paired frames;
machine closure retains membership of both actual saved stacks. -/
theorem relocated_resume {ids : GlobalRel} {primitives : Primitives m σ}
    {familyL familyR : Isomorphism.RecursiveCall.Family m} {returned final : Ports (Ty V S)}
    {startL startR : Config m σ final} (closed : ClosedFamily primitives ids familyL familyR)
    (admitted : Admitted m ids familyL familyR startL startR)
    {jobL jobR : Job m returned} {stackL stackR : Stack m returned final} {blockedStore : σ}
    (pathL : Relation.ReflTransGen (Step primitives) startL ⟨.eval jobL stackL, blockedStore⟩)
    (pathR : Relation.ReflTransGen (Step primitives) startR ⟨.eval jobR stackR, blockedStore⟩)
    (frames : Frames m ids final stackL stackR)
    {valuesL valuesR : Tuple m.Val returned} (packets : TupleRelated m ids valuesL valuesR)
    (validL : TupleIn familyL valuesL) (validR : TupleIn familyR valuesR) (store : σ) :
    Admitted m ids familyL familyR ⟨.returned valuesL stackL, store⟩ ⟨.returned valuesR stackR, store⟩ :=
  ⟨.returned store packets frames, ⟨validL, (closed.closedL.steps admitted.memberL pathL).2⟩,
    ⟨validR, (closed.closedR.steps admitted.memberR pathR).2⟩⟩

end Silmaril.SSA.RVSDG.Interprocedural.Runtime.Recursive.PartialLink.StaticDemand.Ordered.Prefix
