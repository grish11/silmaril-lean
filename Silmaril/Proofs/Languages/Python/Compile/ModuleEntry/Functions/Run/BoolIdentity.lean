module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Run.Seeded.Defs

public section

namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.BoolIdentity

open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions
open Compile.ModuleEntry.Functions.Run
open Compile.ModuleEntry.Functions.Run.Seeded
open Core.Module (ListHeap)
open Core.Module.SeededCall (Namespace)

theorem run_assertBoolIdentity {scope : Source.Scope} (space : Namespace) (context : CallContext)
    (lists : ListHeap) (test : BoolIdentityTest scope) (rest : List (Instruction scope)) :
    runInstructionsIn space context (.assertBoolIdentity test :: rest) lists =
      let result := readBoolCall space test.argument
      let receipt : CallEvent := ⟨"bool", ⟨result.map .bool, none⟩⟩
      match result.bind (checkBoolIdentityResult space test) with
      | .error error => ⟨space, .error (.ofCall error), [receipt], context.heap, lists⟩
      | .ok () =>
        let tail := runInstructionsIn space context rest lists
        { tail with calls := receipt :: tail.calls } := by
  simp only [runInstructionsIn, effectWithLists, effect, assertBoolIdentity]
  cases (readBoolCall space test.argument).bind (checkBoolIdentityResult space test) with
  | error _ => rfl
  | ok value => cases value; rfl

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.Run.BoolIdentity
