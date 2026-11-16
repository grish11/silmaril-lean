module

public import Silmaril.Logic.FirstOrderLFP.Boolean.Thms
public import Silmaril.Proofs.Logic.FirstOrderLFP.Boolean.Complement
public import Silmaril.Logic.FirstOrderLFP.Examples

@[expose] public section
noncomputable section
namespace Silmaril.Logic.FirstOrderLFP.Boolean.Examples
open Silmaril.Logic.Institution.Examples
open FirstOrderLFP.Reachability

/-- Negation applies to an actual nested, parameter-capturing LFP formula,
not merely to a recursion-independent FOL atom. -/
def notReaches : Formula signature emptyProfiles (context 2) (fun _ => true) :=
  .neg (positiveWith reaches (fun _ => false) (fun i => i.elim0))

/-- An infinite carrier and the actual forward chain distinguish nonreachability. -/
theorem chain_nonreach :
    ![1, 0] ∈ notReaches.denote (model Nat (fun a b => b = a + 1))
      (noRelations (fun a b : Nat => b = a + 1)) := by
  change ![1, 0] ∉ (positiveWith reaches (fun _ => false) (fun i => i.elim0)).denote (model Nat (fun a b => b = a + 1)) (noRelations (fun a b : Nat => b = a + 1))
  rw [positiveWith_denote]
  exact FirstOrderLFP.Examples.chain_nonreach

theorem chain_reachable_rejected :
    ![0, 5] ∉ notReaches.denote (model Nat (fun a b => b = a + 1))
      (noRelations (fun a b : Nat => b = a + 1)) := by
  change ¬ ![0, 5] ∉ (positiveWith reaches (fun _ => false) (fun i => i.elim0)).denote (model Nat (fun a b => b = a + 1)) (noRelations (fun a b : Nat => b = a + 1))
  rw [positiveWith_denote]
  exact not_not.mpr (FirstOrderLFP.Examples.natural_chain 5)

abbrev nullary : Profile signature := ⟨0, context 0⟩
abbrev nullaryProfiles (n : Nat) : Fin n → Profile signature := fun _ => nullary

/-- The free outer recursive predicate occurs negatively inside a distinct LFP.
The bound predicate is unused; its fixed-point operator is genuinely constant. -/
def negativeOuterBody : Formula signature (nullaryProfiles 2) (context 0)
    (Fin.cases true (fun _ => false)) :=
  .neg (.pred 1 rfl (fun i => i.elim0))

def negativeOuter : Formula signature (nullaryProfiles 1) (context 0) (fun _ => false) :=
  .lfp (P' := nullaryProfiles 2) (Δ := context 0) rfl rfl negativeOuterBody (fun i => i.elim0)

/-- Changing a captured outer relation changes the fixed point, even though
there are no object variables. This also exercises nullary recursive profiles. -/
theorem negativeOuter_denote (M : Model signature)
    (η : RelEnv M (nullaryProfiles 1)) (v : ObjEnv M (context 0)) :
    v ∈ negativeOuter.denote M η ↔ (fun i => i.elim0) ∉ η 0 := by
  rw [negativeOuter, Formula.denote_lfp]
  have constant (X : Set (Tuple M nullary)) :
      bodyOperator M negativeOuterBody η v X = (η 0)ᶜ := by
    apply Set.ext
    intro x
    have hExtends : Extends (M := M) (Δ := context 0) (fun i => i.elim0) x v :=
      ⟨fun i => i.elim0, fun i => i.elim0⟩
    rw [bodyOperator_iff M (P' := nullaryProfiles 2) (Γ := context 0) (Δ := context 0) rfl rfl negativeOuterBody η v X x (fun i => i.elim0) hExtends]
    simp only [negativeOuterBody, Formula.denote, insertRel]
    change _ ∉ η 0 ↔ x ∉ η 0
    apply not_congr
    exact iff_of_eq (congrArg (fun t : Tuple M nullary => t ∈ η 0) (Subsingleton.elim _ _))
  have fixed := (bodyOperator M negativeOuterBody η v).map_lfp
  rw [constant] at fixed
  change _ ∈ (bodyOperator M negativeOuterBody η v).lfp ↔ _
  rw [← fixed]
  change _ ∉ η 0 ↔ _ ∉ η 0
  apply not_congr
  exact iff_of_eq (congrArg (fun t : Tuple M nullary => t ∈ η 0) (Subsingleton.elim _ _))

theorem negativeOuter_distinguishes (M : Model signature) :
    (fun i => i.elim0) ∈ negativeOuter.denote M (fun _ => ∅) ∧
      (fun i => i.elim0) ∉ negativeOuter.denote M (fun _ => Set.univ) := by
  constructor
  · exact (negativeOuter_denote M _ _).mpr (fun h => h)
  · intro h
    exact (negativeOuter_denote M _ _).mp h (Set.mem_univ _)

/-- Empty object carriers remain admitted independently of nullary tuple values. -/
theorem empty_nonexistence :
    (fun i => i.elim0) ∈
      (Formula.neg (.ex (Δ := context 1) (.base .tt)) : Formula signature emptyProfiles (context 0) (fun _ => true)).denote
        (model Empty (fun _ _ => False)) (noRelations (fun _ _ : Empty => False)) := by
  rintro ⟨x, _⟩
  exact x.elim

end Silmaril.Logic.FirstOrderLFP.Boolean.Examples
