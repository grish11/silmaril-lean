module

public import Silmaril.Logic.FirstOrderLFP.Reachability.Defs
public import Mathlib.Tactic.FinCases

@[expose] public section
namespace Silmaril.Logic.FirstOrderLFP.Reachability
open Silmaril.Logic.Institution.Examples

variable {A : Type} (E : A → A → Prop)

def noRelations {P : Fin 0 → Profile signature} : RelEnv (model A E) P := fun i => i.elim0
def noObjects : ObjEnv (model A E) (context 0) := fun i => i.elim0

theorem binary_operator (X : Set (Fin 2 → A)) (x : Fin 2 → A) :
    x ∈ bodyOperator (model A E) (Γ := context 0) binaryBody (noRelations E) (noObjects E) X ↔
      E (x 0) (x 1) ∨ ∃ z, ![x 0, z] ∈ X ∧ E z (x 1) := by
  have hx : Extends (M := model A E) (Δ := context 2) (w := context 2) (Γ := context 0) x x (noObjects E) :=
    ⟨fun _ => HEq.rfl, fun i => i.elim0⟩
  rw [bodyOperator_iff (model A E) rfl rfl binaryBody (noRelations E) (noObjects E) X x x hx]
  change (E (x 0) (x 1) ∨ ∃ z, (fun j => _) ∈ X ∧ E z (x 1)) ↔ _
  have he (z : A) :
      (fun j => EQ.Term.eval (model A E).toStructure.toAlgebra (Fin.cases z x)
        (![varTerm 1, varTerm 0] j)) = ![x 0, z] := by
    funext j; fin_cases j <;> rfl
  simp only [he]

theorem parameter_operator (X : Set (Fin 1 → A)) (x : Fin 1 → A) (ρ : Fin 2 → A) :
    x ∈ bodyOperator (model A E) (Γ := context 2) parameterBody (noRelations E) ρ X ↔
      x 0 = ρ 1 ∨ ∃ z, E (x 0) z ∧ ![z] ∈ X := by
  let θ : Fin 3 → A := ![x 0, ρ 0, ρ 1]
  have hθ : Extends (M := model A E) (Δ := context 3) (w := context 1) (Γ := context 2) θ x ρ := by
    constructor
    · intro j; fin_cases j; rfl
    · intro j; fin_cases j <;> rfl
  rw [bodyOperator_iff (model A E) rfl rfl parameterBody (noRelations E) ρ X x θ hθ]
  change (x 0 = ρ 1 ∨ ∃ z, E (x 0) z ∧
    (fun j => EQ.Term.eval (model A E).toStructure.toAlgebra (Fin.cases z θ)
      (![varTerm 0] j)) ∈ X) ↔ _
  have he (z : A) :
      (fun j => EQ.Term.eval (model A E).toStructure.toAlgebra (Fin.cases z θ)
        (![varTerm 0] j)) = ![z] := by
    funext j; fin_cases j; rfl
  simp only [he]

theorem binary_parameter_operator (X : Set (Fin 2 → A)) (x ρ : Fin 2 → A) :
    x ∈ bodyOperator (model A E) (Γ := context 2) binaryParameterBody (noRelations E) ρ X ↔
      E (x 0) (x 1) ∨ ∃ z, ![x 0, z] ∈ X ∧ E z (x 1) := by
  let θ : Fin 4 → A := ![x 0, x 1, ρ 0, ρ 1]
  have hθ : Extends (M := model A E) (Δ := context 4) (w := context 2)
      (Γ := context 2) θ x ρ := by
    constructor
    · intro j; fin_cases j <;> rfl
    · intro j; fin_cases j <;> rfl
  rw [bodyOperator_iff (model A E) rfl rfl binaryParameterBody (noRelations E) ρ X x θ hθ]
  change (E (x 0) (x 1) ∨ ∃ z,
    (fun j => EQ.Term.eval (model A E).toStructure.toAlgebra (Fin.cases z θ)
      (![varTerm 1, varTerm 0] j)) ∈ X ∧ E z (x 1)) ↔ _
  have he (z : A) :
      (fun j => EQ.Term.eval (model A E).toStructure.toAlgebra (Fin.cases z θ)
        (![varTerm 1, varTerm 0] j)) = ![x 0, z] := by
    funext j; fin_cases j <;> rfl
  simp only [he]

/-- Binary recursion denotes exactly the nonempty finite edge paths. -/
theorem binary_finite_path (x : Fin 2 → A) :
    x ∈ lfpSet (model A E) (Γ := context 0) binaryBody (noRelations E) (noObjects E) ↔
      Relation.TransGen E (x 0) (x 1) := by
  let L := lfpSet (model A E) (Γ := context 0) binaryBody (noRelations E) (noObjects E)
  have close (y : Fin 2 → A) :
      (E (y 0) (y 1) ∨ ∃ z, ![y 0, z] ∈ L ∧ E z (y 1)) → y ∈ L := by
    intro h
    rw [← binary_operator E] at h
    exact (congrArg (y ∈ ·) (lfpSet_unfold (model A E) (Γ := context 0) binaryBody (noRelations E) (noObjects E))).mpr h
  constructor
  · apply lfpSet_induction (model A E) (Γ := context 0) binaryBody (noRelations E) (noObjects E)
        {y : Fin 2 → A | Relation.TransGen E (y 0) (y 1)}
    intro y hy
    rcases (binary_operator E _ y).mp hy with h | ⟨z, hz, hzy⟩
    · exact .single h
    · exact hz.tail hzy
  · intro h
    have hp : ∀ a b, Relation.TransGen E a b → ![a, b] ∈ L := by
      intro a b hab
      induction hab with
      | single h => exact close _ (Or.inl h)
      | @tail b c hab hbc ih => exact close _ (Or.inr ⟨b, ih, hbc⟩)
    have hx : ![x 0, x 1] = x := by funext i; fin_cases i <;> rfl
    exact hx ▸ hp _ _ h

/-- The actual binary-binder formula denotes exactly nonempty finite paths. -/
theorem transitive_finite_path (ρ : Fin 2 → A) :
    ρ ∈ transitive.denote (model A E) (noRelations E) ↔
      Relation.TransGen E (ρ 0) (ρ 1) := by
  have hF : bodyOperator (model A E) (Γ := context 2) binaryParameterBody (noRelations E) ρ =
      bodyOperator (model A E) (Γ := context 0) binaryBody (noRelations E) (noObjects E) := by
    apply OrderHom.ext
    funext X
    apply Set.ext
    intro x
    exact (binary_parameter_operator E X x ρ).trans (binary_operator E X x).symm
  have he : (fun j => EQ.Term.eval (model A E).toStructure.toAlgebra ρ
      (![varTerm 0, varTerm 1] j)) = ![ρ 0, ρ 1] := by
    funext j; fin_cases j <;> rfl
  change (fun j => EQ.Term.eval (model A E).toStructure.toAlgebra ρ (![varTerm 0, varTerm 1] j)) ∈
    (bodyOperator (model A E) (Γ := context 2) binaryParameterBody (noRelations E) ρ).lfp ↔ _
  rw [he, hF]
  exact binary_finite_path E ![ρ 0, ρ 1]

/-- The unary fixed point computes finite paths to the captured target. -/
theorem parameter_finite_path (x : Fin 1 → A) (ρ : Fin 2 → A) :
    x ∈ lfpSet (model A E) (Γ := context 2) parameterBody (noRelations E) ρ ↔
      Relation.ReflTransGen E (x 0) (ρ 1) := by
  let L := lfpSet (model A E) (Γ := context 2) parameterBody (noRelations E) ρ
  have close (y : Fin 1 → A) :
      (y 0 = ρ 1 ∨ ∃ z, E (y 0) z ∧ ![z] ∈ L) → y ∈ L := by
    intro h
    rw [← parameter_operator E] at h
    exact (congrArg (y ∈ ·) (lfpSet_unfold (model A E) (Γ := context 2) parameterBody (noRelations E) ρ)).mpr h
  constructor
  · apply lfpSet_induction (model A E) (Γ := context 2) parameterBody (noRelations E) ρ
        {y : Fin 1 → A | Relation.ReflTransGen E (y 0) (ρ 1)}
    intro y hy
    rcases (parameter_operator E _ y ρ).mp hy with h | ⟨z, hyz, hz⟩
    · exact h ▸ Relation.ReflTransGen.refl
    · exact hz.head hyz
  · intro h
    have hp : ∀ a, Relation.ReflTransGen E a (ρ 1) → ![a] ∈ L := by
      intro a ha
      induction ha using Relation.ReflTransGen.head_induction_on with
      | refl => exact close _ (Or.inl rfl)
      | @head a c hac hct ih => exact close _ (Or.inr ⟨c, hac, ih⟩)
    have hx : ![x 0] = x := by funext i; fin_cases i; rfl
    exact hx ▸ hp _ h

theorem reaches_finite_path (ρ : Fin 2 → A) :
    ρ ∈ reaches.denote (model A E) (noRelations E) ↔
      Relation.ReflTransGen E (ρ 0) (ρ 1)  := by
  have he : (fun j => EQ.Term.eval (model A E).toStructure.toAlgebra ρ
      (![varTerm 0] j)) = ![ρ 0] := by
    funext j; fin_cases j; rfl
  change (fun j => EQ.Term.eval (model A E).toStructure.toAlgebra ρ (![varTerm 0] j)) ∈
    lfpSet (model A E) (Γ := context 2) parameterBody (noRelations E) ρ ↔ _
  rw [he]
  exact parameter_finite_path E ![ρ 0] ρ

end Silmaril.Logic.FirstOrderLFP.Reachability
