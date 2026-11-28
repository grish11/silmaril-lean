module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Completion.Defs

/-! # Phase injections and the class map on phases of one payload type -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] (A : τ)

theorem phaseInj_base : phaseInj (Φ := Φ) A 0 0 = 𝟙 _ :=
  Category.comp_id _

theorem phaseInj_zero (K : Nat) : phaseInj (Φ := Φ) A (K + 1) 0 = sumInl A (phaseType A K) :=
  (sumInl_sumDesc _ _).trans (Category.id_comp _)

theorem phaseInj_succ (K : Nat) (i : Fin (K + 1)) :
    phaseInj (Φ := Φ) A (K + 1) i.succ = phaseInj A K i ≫ sumInr A (phaseType A K) :=
  (Category.assoc _ _ _).trans
    ((congrArg (famInj K (fun _ => A) i ≫ ·) (sumInr_sumDesc _ _)).trans (Category.assoc _ _ _).symm)

/-- The class-map equation on phases: phase `i` goes to phase `cls i`. -/
theorem phaseInj_classFold {K K' : Nat} (cls : Fin (K + 1) → Fin (K' + 1)) (i : Fin (K + 1)) :
    phaseInj (Φ := Φ) A K i ≫ classFold A cls = phaseInj A K' (cls i) := by
  have e := famInj_tagFold (Φ := Φ) (fun _ : Fin (K' + 1) => A) cls i
  simp only [phaseInj, classFold, Category.assoc, Iso.hom_inv_id_assoc]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (constIso A K').hom) e)

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
