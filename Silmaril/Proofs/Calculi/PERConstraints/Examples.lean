module

public import Silmaril.Calculi.PERConstraints.Examples.Defs

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Examples.Proofs

open Silmaril.Formats

theorem separation_sat : Dictionary.SAT separation := by
  refine ⟨PER.equality Bool, ?_⟩
  intro key bound lookup
  cases lookup
  simp [Bound.Holds, DISTINCTList, PER.Dom, PER.equality]

theorem conflict_unsat : Dictionary.UNSAT conflict := by
  intro model holds
  have same : EQ model ({false, true} : Set Bool) := holds true _ rfl
  have separate : DISTINCTList model [false, true] := holds false _ rfl
  exact (List.pairwise_pair.mp separate.2) (same false (by simp) true (by simp))

theorem collapsed_unsat : (CNF.map (fun _ : Bool => ()) (Dictionary.toCNF separation)).UNSAT := by
  intro model holds
  have pulled := (CNF.holds_map model _ _).mp holds
  have separate : DISTINCTList (model.pull (fun _ : Bool => ())) [false, true] :=
    (Dictionary.holds_toCNF _ separation).mp pulled () _ rfl
  exact (List.pairwise_pair.mp separate.2) (separate.1 false (by simp))

theorem set_distinct_collapse :
    DISTINCT (PER.equality Unit) ((fun _ : Bool => ()) '' Set.univ) ∧
      ¬DISTINCT ((PER.equality Unit).pull (fun _ : Bool => ())) Set.univ := by
  constructor
  · refine ⟨fun _ _ => rfl, ?_⟩
    intro left _ right _ different
    exact (different (Subsingleton.elim left right)).elim
  · intro holds
    exact holds.2 (Set.mem_univ false) (Set.mem_univ true) Bool.false_ne_true rfl

end Silmaril.Calculi.PERConstraints.Examples.Proofs
