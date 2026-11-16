module

public import Silmaril.Logic.Kore.Modules.Semantics.Modules.Thms
public import Silmaril.Logic.Kore.Modules.Theory.Examples

@[expose] public section
namespace Silmaril.Logic.Kore.Modules.Semantics.Examples
open Checking
open Silmaril.Logic.Kore.Modules.Examples
  (checked join model capture_claim_proved model_satisfies_join false_claim_false)
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def captureSource : CheckedSentence checked.ambient :=
  join.claims.get ⟨0, by decide +kernel⟩
def falseSource : CheckedSentence checked.ambient :=
  join.claims.get ⟨1, by decide +kernel⟩

/-- Truth of the actual raw alias/binder claim in the accepted four-module text,
for all models satisfying the actual raw imported source axioms. -/
theorem actual_source_claim : Proves join captureSource :=
  (proves_sound join captureSource).2 capture_claim_proved

/-- A genuine source model witnesses consistency of these imported axioms. -/
theorem actual_source_model : Models join model :=
  (models_sound join model).2 model_satisfies_join

theorem actual_source_false : ¬ Satisfies model falseSource.fuel falseSource.raw := by
  intro h
  exact false_claim_false ((checkedSentence_sound falseSource model).1 h)

theorem actual_source_false_not_proved : ¬ Proves join falseSource := by
  intro h
  exact actual_source_false (h model actual_source_model)

/-- Direct raw interpretation itself distinguishes capture from fresh binding. -/
theorem direct_alias_capture :
    denote model 8 [⟨"Y", "S", {true}⟩] "S"
      (.app "hold" [.variable "Y" "S"]) = {true} := by
  ext result
  change (∃ _ : Bool, result = true) ↔ result = true
  simp

theorem captured_variable_differs :
    false ∉ denote model 8 [⟨"Y", "S", {true}⟩] "S"
      (.app "hold" [.variable "Y" "S"]) ∧
    false ∈ denote model 8 [⟨"Y", "S", {true}⟩] "S"
      (.exists "S" "Y" "S" (.variable "Y" "S")) := by
  constructor
  · rw [direct_alias_capture]
    change false ≠ true
    decide
  · change ∃ x : Bool, false = x
    exact ⟨false, rfl⟩
end Silmaril.Logic.Kore.Modules.Semantics.Examples
