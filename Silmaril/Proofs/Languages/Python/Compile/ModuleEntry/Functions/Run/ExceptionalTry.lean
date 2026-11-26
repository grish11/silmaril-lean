module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry.Defs
public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Thms

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry

open Silmaril.Languages.Python
open Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run
open Core.Module (ListHeap)
open Core.Module.Functions (Session)
open Core.Module.SeededCall (Namespace)
open Core.Closure.Executor (CodeTable)

theorem ordinary_scalar_trace {scope : Source.Scope} (table : CodeTable) (session : Session)
    (actions : List (Compile.ModuleEntry.Action scope)) :
    ∃ reached completion,
      runPrefix table (actions.length + 1) (.ready session (actions.map .scalar)) =
        ([], .finished reached completion) ∧ reached.heap = session.heap ∧ reached.lists = session.lists := by
  induction actions generalizing session with
  | nil => exact ⟨session, .normal, rfl, rfl, rfl⟩
  | cons action rest tail =>
    cases action with
    | assign name reference operand =>
      cases evaluated : evaluate session operand with
      | error failure =>
        exact ⟨session, failure, by simp [runPrefix, advance, evaluated], rfl, rfl⟩
      | ok value =>
        obtain ⟨reached, completion, finished, heap, lists⟩ := tail (session.bindGlobal name value)
        exact ⟨reached, completion, by simpa [runPrefix, advance, evaluated] using finished, heap, lists⟩
    | assertion operand =>
      cases evaluated : evaluate session operand with
      | error failure =>
        exact ⟨session, failure, by simp [runPrefix, advance, assertOperand, evaluated], rfl, rfl⟩
      | ok value =>
        by_cases holds : Core.Module.Functions.truth value = true
        · obtain ⟨reached, completion, finished, heap, lists⟩ := tail session
          exact ⟨reached, completion, by simpa [runPrefix, advance, assertOperand, evaluated, holds] using finished,
            heap, lists⟩
        · exact ⟨session, .assertionError, by simp [runPrefix, advance, assertOperand, evaluated, holds], rfl, rfl⟩

theorem seeded_scalar_carriers {scope : Source.Scope} (space : Namespace) (context : Seeded.CallContext)
    (actions : List (Compile.ModuleEntry.Action scope)) (lists : ListHeap) :
    let outcome := Seeded.runInstructionsIn space context (actions.map .scalar) lists
    outcome.heap = context.heap ∧ outcome.lists = lists ∧ outcome.calls = [] ∧
      outcome.residual.builtins = space.builtins := by
  induction actions generalizing space with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons action rest tail =>
    cases action with
    | assign name reference operand =>
      cases evaluated : Seeded.evaluateScalar space false operand with
      | error failure =>
        simp [Seeded.runInstructionsIn, Seeded.effectWithLists, Seeded.effect, evaluated, Except.map, Except.mapError]
      | ok value =>
        simpa [Seeded.runInstructionsIn, Seeded.effectWithLists, Seeded.effect, evaluated, Except.map,
          Except.mapError, Core.Module.SeededCall.Namespace.bindGlobal] using tail (space.bindGlobal name value)
    | assertion operand =>
      cases evaluated : Seeded.evaluateScalar space false operand with
      | error failure =>
        simp [Seeded.runInstructionsIn, Seeded.effectWithLists, Seeded.effect, Seeded.assertOperand,
          evaluated, Except.bind, Except.map, Except.mapError]
      | ok value =>
        by_cases holds : Seeded.truth value = true
        · simpa [Seeded.runInstructionsIn, Seeded.effectWithLists, Seeded.effect, Seeded.assertOperand,
            Seeded.assertTruthAs, evaluated, holds, Except.bind, Except.map, Except.mapError] using tail space
        · simp [Seeded.runInstructionsIn, Seeded.effectWithLists, Seeded.effect, Seeded.assertOperand,
            Seeded.assertTruthAs, evaluated, holds, Except.bind, Except.map, Except.mapError]

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.ExceptionalTry
