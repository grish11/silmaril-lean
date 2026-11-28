module

public import Silmaril.Proofs.SSA.Isotope.Institution.Parallel.Model

@[expose] public section

namespace Silmaril.Isotope.Parallel.InstitutionProofs

open Silmaril.Isotope.Institution Parallel.Institution CategoryTheory Semantics

universe u v q

variable {τ ε : Type u} {S S' S'' : InstrSig τ ε} {tier : Tier} {ν : Type v}
  [HasProduct τ] [HasUnit τ] [CaseTypes tier τ] [DecidableEq ν] {Γ : Ctx ν τ}

theorem equation_map_id (φ : Equation S tier Γ) : φ.map (𝟙 S) = φ := by
  cases φ
  unfold Equation.map
  congr 1 <;> first | exact derivation_map_id _ | exact Tm.map_id _

theorem equation_map_comp (f : S ⟶ S') (g : S' ⟶ S'') (φ : Equation S tier Γ) :
    (φ.map f).map g = φ.map (f ≫ g) := by
  cases φ
  unfold Equation.map
  congr 1 <;> first | exact derivation_map_comp f g _ | exact Tm.map_comp f.instr g.instr _

variable {D : τ → Type q} [ProductModel D] [UnitModel D]

theorem holds_map (f : S ⟶ S') (φ : Equation S tier Γ) (X : Model D S')
    (C : Control tier D X.M) :
    (φ.map f).Holds X C ↔ φ.Holds (X.reduct f) C := by
  unfold Equation.Holds Equation.map
  simp only [denote_mapInstr]
  rfl

end Silmaril.Isotope.Parallel.InstitutionProofs
