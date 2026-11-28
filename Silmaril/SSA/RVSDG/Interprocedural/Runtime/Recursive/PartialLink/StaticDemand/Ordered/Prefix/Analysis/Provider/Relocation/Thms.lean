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

open Isomorphism.RecursiveCall.Numbered (ExactValueCheck checkWires ordinaryPorts)
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

/-- Check both physical capture boundaries using their actual successful
initializer rows. The shared typed body supplies one GenKill problem.
The resulting receipt indexes the two original numbered links. -/
def AllocationPlan.analyzeLayouts {shiftedR : Bool}
    (layoutL : AllocationPlan Op table imports fn value shifted)
    (right : layoutL.Layout shiftedR)
    (dispatch : Dispatch actions table) (unitL unitR : Nat) (inputsL inputsR : Tuple m.Val imports) (initial : σ)
    (receipt : LinkedRows (layoutL.linkDelta actions unitL inputsL initial)
      ((layoutL.withLayout right).linkDelta actions unitR inputsR initial))
    (importedL : Row (Known dispatch.left) inputsL) (importedR : Row (Known dispatch.right) inputsR)
    (readyL : layoutL.binding.resolved dispatch.left inputsL
      ((AllocatingClient.initialLocals m shifted).snoc receipt.left))
    (readyR : (layoutL.withLayout right).binding.resolved dispatch.right inputsR
      ((AllocatingClient.initialLocals m shiftedR).snoc receipt.right)) :
    Option (ExportAnalysis actions layoutL.binding.summary
      (Executable.link actions unitL layoutL.numbered.toGraph inputsL initial)
      (Executable.link actions unitR (layoutL.withLayout right).numbered.toGraph inputsR initial)) :=
  let layoutR := layoutL.withLayout right
  let checkedL := (allocationChecked dispatch shifted).addInitialized receipt.left receipt.left
  let checkedR := (allocationChecked dispatch shiftedR).addInitialized receipt.right receipt.right
  let localsL := (AllocatingClient.initialLocals m shifted).snoc receipt.left
  let localsR := (AllocatingClient.initialLocals m shiftedR).snoc receipt.right
  let capturesL := checkWires (entry := inputsL)
    (checkedL.state.left.availableWithImports Known.ordinary importedL) layoutL.binding.captures
  let capturesR := checkWires (entry := inputsR)
    (checkedR.state.right.availableWithImports Known.ordinary importedR) layoutR.binding.captures
  if capturesL.isSome && capturesR.isSome then
    let linked : Export actions layoutL.binding.summary
        (Executable.link actions unitL layoutL.numbered.toGraph inputsL initial)
        (Executable.link actions unitR layoutR.numbered.toGraph inputsR initial) :=
      { earlier := table
        dispatch := ⟨layoutL.binding.extendGuard dispatch.left inputsL localsL,
          layoutR.binding.extendGuard dispatch.right inputsR localsR,
          dispatch.lambda_transport_withCaptures layoutL.binding right.captures
            inputsL inputsR localsL localsR readyL readyR⟩
        targetL := layoutL.binding.value inputsL localsL
        targetR := layoutR.binding.value inputsR localsR
        capsL := layoutL.binding.captures.read inputsL localsL
        capsR := layoutR.binding.captures.read inputsR localsR
        store := receipt.store
        linkedL := layoutL.link_initialized actions unitL inputsL initial receipt.linkedL
        linkedR := layoutR.link_initialized actions unitR inputsR initial receipt.linkedR
        resolvedL := ⟨rfl, rfl⟩
        resolvedR := ⟨rfl, rfl⟩ }
    some ⟨linked, layoutL.binding.body.liveness, fun demand origin =>
      (layoutL.binding.body.mem_liveIn_iff demand origin).symm.trans List.mem_eraseDups⟩
  else none

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
      (Executable.link actions unit layout.numbered.toGraph inputsR initial)) :=
  layout.analyzeLayouts ⟨layout.init, layout.binding.captures⟩ dispatch unit unit inputsL inputsR initial
    receipt importedL importedR readyL readyR

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
    {rename : Nat → Nat} {otherL otherR : Outcome m σ [summary.fn.port]}
    (a : ExportAnalysis actions summary (Executable.link actions unitL graphL inputsL initialL) otherR)
    (b : ExportAnalysis actions summary otherL (Executable.link actions unitR graphR inputsR initialR))
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
