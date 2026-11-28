module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Identity

open Silmaril.Languages.Python
open Compile.ModuleEntry
open Compile.ModuleEntry.Functions.Run
open Compile.ModuleEntry.Functions.Run.Seeded
open Core.Module (IdentityOperator Singleton)
open Core.Module.SeededCall (Failure Namespace Value)
open Core.Module.Functions (Session)

private theorem scalar_seeded (value : Core.Closure.Value) :
    Seeded.scalar? (seededValue value) = Functions.Run.scalar? value := by cases value <;> rfl

private theorem scan_mapError (left : Singleton) (links : List (IdentityOperator × (Unit → Except Completion Singleton))) :
    Core.Module.Identity.scan left (links.map fun link =>
      (link.1, fun () => (link.2 ()).mapError scalarFailure)) =
      (Core.Module.Identity.scan left links).mapError scalarFailure := by
  induction links generalizing left with
  | nil => rfl
  | cons link rest ih =>
    obtain ⟨operator, read⟩ := link
    cases found : read () with
    | error => simp [Core.Module.Identity.scan, found, Except.bind, Except.mapError]
    | ok right =>
      cases passed : operator.test left right <;>
        simp only [Core.Module.Identity.scan, List.map_cons, found, Except.bind, Except.mapError, passed,
          Bool.false_eq_true, ↓reduceIte]
      exact ih right

private theorem project_map (value : Except Completion Core.Closure.Value) :
    Core.Module.Identity.project (fun x => (Seeded.scalar? x).bind Core.Module.Value.singleton?)
      .unsupported ((value.map seededValue).mapError scalarFailure) =
      (Core.Module.Identity.project (fun x => (Functions.Run.scalar? x).bind Core.Module.Value.singleton?)
        .scalarProfile value).mapError scalarFailure := by
  cases value with
  | error => rfl
  | ok value =>
    cases found : (Functions.Run.scalar? value).bind Core.Module.Value.singleton? <;>
      simp [Core.Module.Identity.project, Except.bind, Except.mapError, Except.map, scalar_seeded, found, scalarFailure]

theorem evaluateScalar_agrees {scope : Source.Scope} (space : Namespace) (session : Session)
    (reads : ∀ name, space.lookupGlobal name = (session.globals name).map seededValue)
    (operand : Operand scope) (admitted : operand.comparable = true) :
    evaluateScalar space true operand = ((Functions.Run.evaluate session operand).map seededValue).mapError scalarFailure := by
  cases operand with
  | integer | none_ | boolean => simp [evaluateScalar, lowerScalarOperand, Functions.Run.evaluate]; rfl
  | read name reference =>
    simp only [evaluateScalar, lowerScalarOperand, Core.Module.SeededCall.Operand.eval, Functions.Run.evaluate, reads]
    cases session.globals name <;> rfl
  | binary operator left right =>
    cases operator <;> simp only [Operand.comparable, Bool.and_eq_true_iff] at admitted
    all_goals try contradiction
    all_goals
      have lhs := evaluateScalar_agrees space session reads left admitted.1
      have rhs := evaluateScalar_agrees space session reads right admitted.2
      rw [evaluateScalar, Functions.Run.evaluate, lhs, rhs]
      cases Functions.Run.evaluate session left
      · rfl
      cases Functions.Run.evaluate session right
      · rfl
      rename_i first second
      cases first <;> cases second <;> rfl
  | identityChain left links =>
    rw [Operand.comparable] at admitted
    obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp admitted
    have lhs := evaluateScalar_agrees space session reads left head
    let ordinary := links.attach.map fun link =>
      (link.val.1, fun _ : Unit => Core.Module.Identity.project
        (fun x => (Functions.Run.scalar? x).bind Core.Module.Value.singleton?) .scalarProfile
        (Functions.Run.evaluate session link.val.2))
    have mapped : (links.attach.map fun link =>
        (link.val.1, fun _ : Unit => Core.Module.Identity.project
          (fun x => (Seeded.scalar? x).bind Core.Module.Value.singleton?) .unsupported
          (evaluateScalar space true link.val.2))) =
        ordinary.map (fun link => (link.1, fun () => (link.2 ()).mapError scalarFailure)) := by
      simp only [ordinary, List.map_map]
      apply List.map_congr_left
      intro link member
      have checked := List.all_eq_true.mp tail link member
      rw [evaluateScalar_agrees space session reads link.val.2 checked, project_map]
      rfl
    rw [evaluateScalar, Functions.Run.evaluate]
    dsimp only []
    rw [lhs, project_map, mapped]
    cases found : Core.Module.Identity.project (fun x => (Functions.Run.scalar? x).bind Core.Module.Value.singleton?)
        .scalarProfile (Functions.Run.evaluate session left) with
    | error => rfl
    | ok first =>
      change (Core.Module.Identity.scan first (ordinary.map fun link =>
        (link.1, fun () => (link.2 ()).mapError scalarFailure))).map _ =
        (((Core.Module.Identity.scan first ordinary).map Core.Closure.Value.bool).map seededValue).mapError _
      rw [scan_mapError]
      cases Core.Module.Identity.scan first ordinary <;> rfl
termination_by sizeOf operand
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals
    first
    | omega
    | have smaller := Core.Module.Identity.sizeOf_operand_lt link.property
      omega

theorem evaluate_singletonResult {scope : Source.Scope} (session : Session)
    (operand : Operand scope) (certified : operand.singletonResult = true) (value : Core.Closure.Value)
    (evaluated : Functions.Run.evaluate session operand = .ok value) :
    ∃ exact, (Functions.Run.scalar? value).bind Core.Module.Value.singleton? = some exact := by
  cases operand with
  | integer | read => contradiction
  | boolean | none_ =>
    rw [Functions.Run.evaluate] at evaluated
    cases evaluated
    exact ⟨_, rfl⟩
  | binary operator left right =>
    cases operator <;> try contradiction
    all_goals
      rw [Functions.Run.evaluate] at evaluated
      cases lhs : Functions.Run.evaluate session left with
      | error => simp [lhs, bind, Except.bind] at evaluated
      | ok first =>
        cases rhs : Functions.Run.evaluate session right with
        | error => simp [lhs, rhs, bind, Except.bind] at evaluated
        | ok second =>
          cases lhsScalar : Functions.Run.scalar? first with
          | none => simp [lhs, rhs, lhsScalar, bind, Except.bind] at evaluated
          | some a =>
            cases rhsScalar : Functions.Run.scalar? second with
            | none => simp [lhs, rhs, lhsScalar, rhsScalar, bind, Except.bind] at evaluated
            | some b =>
              simp [lhs, rhs, lhsScalar, rhsScalar, bind, Except.bind,
                Compile.ModuleEntry.Run.operator, Core.Module.Operator.eval, Functions.Run.embed] at evaluated
              subst value
              exact ⟨_, rfl⟩
  | identityChain left links =>
    rw [Functions.Run.evaluate] at evaluated
    dsimp only [] at evaluated
    let read (value : Operand scope) := Core.Module.Identity.project
      (fun exact => (Functions.Run.scalar? exact).bind Core.Module.Value.singleton?) Completion.scalarProfile
      (Functions.Run.evaluate session value)
    change ((read left).bind fun first =>
      (Core.Module.Identity.scan first (links.attach.map fun link =>
        (link.val.1, fun _ => read link.val.2))).map Core.Closure.Value.bool) = .ok value at evaluated
    cases head : read left with
    | error => simp [head, Except.bind] at evaluated
    | ok first =>
      simp only [head, Except.bind] at evaluated
      generalize Core.Module.Identity.scan first (links.attach.map fun link =>
        (link.val.1, fun _ => read link.val.2)) = walked at evaluated
      cases walked with
      | error => contradiction
      | ok result => cases evaluated; exact ⟨_, rfl⟩


theorem run_identityAssertion {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (left : Operand scope) (links : List (IdentityOperator × Operand scope)) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.scalar (.assertion (.identityChain left links)) :: rest) =
      match (assertOperand space (.identityChain left links) true context.heap).binding with
      | .ok _ => runInstructionsIn space context rest
      | .error error => ⟨space, .error error, [], context.heap, Core.Module.ListHeap.empty⟩ := by
  have settlement : ∀ {α : Type} (result : Except Failure α),
      match ((result.map fun _ => (none : Option (String × Value))).mapError ModuleFailure.ofCall) with
      | .ok value => value = none
      | .error _ => True := by intro α result; cases result <;> trivial
  simp only [runInstructionsIn, effectWithLists, effect, scalarBinding]
  cases h : (assertOperand space (.identityChain left links) true context.heap).binding with
  | error => rfl
  | ok binding =>
    have exactBinding := settlement
      ((evaluateScalar space false (.identityChain left links)).bind (fun value => assertTruthAs true value context.heap))
    change (match (assertOperand space (.identityChain left links) true context.heap).binding with
      | .ok value => value = none
      | .error _ => True) at exactBinding
    rw [h] at exactBinding
    subst binding
    rfl

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.Identity
