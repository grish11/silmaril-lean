module

public import Silmaril.Logic.Matching.FixedPoint
public import Silmaril.Logic.ModalMu.Examples

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.FixedPoint.Examples
open ModalMu.Examples (signature chain cycle dead)

/-- The chain and cycle are encoded using actual arbitrary set-valued operations. -/
theorem chain_reaches : (expandModal chain).Satisfies (encodeModal (ModalMu.reach () ())) :=
  (expandModal_satisfies chain _).mpr ModalMu.Examples.chain_reaches

theorem cycle_forever : (expandModal cycle).Satisfies (encodeModal (ModalMu.forever ())) :=
  (expandModal_satisfies cycle _).mpr ModalMu.Examples.cycle_forever

theorem cycle_nonreach : ¬ (expandModal cycle).Satisfies (encodeModal (ModalMu.reach () ())) :=
  fun h => ModalMu.Examples.cycle_never_reaches ((expandModal_satisfies cycle _).mp h)

theorem empty_action_nonreach : ¬ (expandModal dead).Satisfies (encodeModal (ModalMu.reach () ())) :=
  fun h => ModalMu.Examples.dead_not_reach ((expandModal_satisfies dead _).mp h)

theorem empty_action_not_forever : ¬ (expandModal dead).Satisfies (encodeModal (ModalMu.forever ())) :=
  fun h => ModalMu.Examples.dead_not_forever ((expandModal_satisfies dead _).mp h)

/-- The derived box is true at an empty operation, even on an empty argument pattern. -/
theorem empty_action_box : (expandModal dead).Satisfies (encodeModal (.box () .bot)) :=
  (expandModal_satisfies dead _).mpr (fun _ h => h.elim)

abbrev one : Fin 1 → Unit := fun _ => ()
abbrev zero : Fin 0 → Unit := Fin.elim0

/-- This keeps the original nonempty 2017 carrier, while every operation is empty. -/
abbrev emptyOperations : Model (modalSignature signature) where
  carrier := fun _ => Bool
  nonempty := fun _ => ⟨false⟩
  operation := fun _ _ => ∅

/-- An element variable is a singleton; a set variable can denote both Boolean states. -/
theorem element_set_difference :
    true ∉ (Pattern.base (.var 0) : Pattern (modalSignature signature) one one ()).denote
      emptyOperations ![false] ![Set.univ] ∧
    true ∈ (Pattern.setvar 0 : Pattern (modalSignature signature) one one ()).denote
      emptyOperations ![false] ![Set.univ] :=
  ⟨Bool.noConfusion, Set.mem_univ _⟩

def objectBinder : Pattern (modalSignature signature) one one () := .ex () (.setvar 0)
def replacement : ∀ i, Pattern (modalSignature signature) zero one (one i) := fun _ => .base (.var 0)

/-- The free element variable in a substituted pattern is not captured by ∃. -/
theorem substitution_no_object_capture :
    true ∉ (objectBinder.substituteSets replacement).denote emptyOperations ![false] (fun i => i.elim0) := by
  rw [Pattern.denote_substituteSets]
  change ¬ ∃ _ : Bool, true = false
  exact fun ⟨_, h⟩ => Bool.noConfusion h

def setBinder : Pattern (modalSignature signature) one one () :=
  .mu (P' := fun _ : Fin 2 => ()) (.setvar 1)

/-- A substituted free set remains free beneath a fresh least-fixed-point binder. -/
theorem substitution_no_set_capture :
    true ∉ (setBinder.substituteSets replacement).denote emptyOperations ![false] (fun i => i.elim0) := by
  rw [Pattern.denote_substituteSets]
  have he : setBinder.denote emptyOperations ![false]
      (fun i => (replacement i).denote emptyOperations ![false] (fun i => i.elim0)) = {false} :=
    mu_unfold emptyOperations (.setvar (P := fun _ : Fin 2 => ()) (Γ := one) 1) ![false] _
  rw [he]
  exact Bool.noConfusion

/-- info: 'Silmaril.Logic.Matching.FixedPoint.Pattern.denote_substituteSets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Pattern.denote_substituteSets
/-- info: 'Silmaril.Logic.Matching.FixedPoint.Pattern.denote_dual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Pattern.denote_dual
/-- info: 'Silmaril.Logic.Matching.FixedPoint.modal_entails_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms modal_entails_iff
/-- info: 'Silmaril.Logic.Matching.FixedPoint.firstOrderToFixedPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firstOrderToFixedPoint
/-- info: 'Silmaril.Logic.Matching.FixedPoint.firstOrderPointedToFixedPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms firstOrderPointedToFixedPoint

end Silmaril.Logic.Matching.FixedPoint.Examples
