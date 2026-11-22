module

public import Silmaril.Calculi.PERConstraints.Patterns.Dasl.Examples.Defs
import Silmaril.Proofs.Calculi.PERConstraints.Patterns.DaslExamples

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Patterns.DaslExamples

open CategoryTheory Silmaril.Formats.Dasl

theorem selected_holds : narrowRule.Holds selectedFamily := Proofs.selected_holds

theorem widened_fails : ¬ widenedRule.Holds selectedFamily := Proofs.widened_fails

def selectedModel : selectedSystem.Model := ⟨selectedFamily, fun _ chosen => (Set.mem_singleton_iff.mp chosen).symm ▸ selected_holds⟩

theorem closure_selected : (selectedSystem.closure selectedFamily).val = selectedFamily :=
  generated_eq selectedModel.property

theorem selected_not_full : ¬ signature.base.constructors.Closed (selectedFamily .output) := Proofs.selected_not_full

theorem independentlyFull_closed (sort : Index) : signature.base.constructors.Closed (independentlyFull sort) :=
  Proofs.independentlyFull_closed sort

theorem independentlyFull_fails : ¬ narrowRule.Holds independentlyFull := Proofs.independentlyFull_fails

private def collapse : daslSignature Bool (@nonemptyLists Bool) ⟶ daslSignature Unit (@nonemptyLists Unit) :=
  daslMap (fun _ => ()) id (fun _ => ()) (fun shape => by cases shape <;> exact Iff.rfl)
    (tree_map_surjective (fun _ => ⟨false, rfl⟩) Function.surjective_id)

private def repeated : Rule (daslSignature Bool (@nonemptyLists Bool)) :=
  ⟨1, fun _ => false, true, .node (.list 2) (fun _ => .hole 0)⟩

example (tuple : Fin 1 → Tree Bool Empty) : repeated.pattern.plug tuple = .list 2 (fun _ => tuple 0) := rfl

example (family : Family (daslSignature Unit (@nonemptyLists Unit))) :
    (repeated.map collapse).Holds family ↔ repeated.Holds (reduct collapse family) :=
  satisfaction collapse family repeated

end Silmaril.Calculi.PERConstraints.Patterns.DaslExamples
