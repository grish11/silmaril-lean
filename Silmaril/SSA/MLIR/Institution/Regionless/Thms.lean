module

public import Silmaril.SSA.MLIR.Institution.Regionless.Defs
public import Silmaril.SSA.MLIR.Institution.Thms
import Silmaril.Proofs.SSA.MLIR.Institution.Regionless

public section

namespace Silmaril.MLIR.Institution

open CategoryTheory Silmaril.Logic.Institution

variable {S : Signature false} {n : Nat} {Γ : Fin n → S.Ty} {s : S.Ty}

theorem Term.withRegions_map {T : Signature false} (f : S ⟶ T) (t : Term S Γ s) :
    (t.map f).withRegions = t.withRegions.map (Signature.withRegions.map f) :=
  Proofs.MLIR.Institution.withRegions_map f t

theorem Term.denote_withRegions (M : Model (Signature.withRegions.obj S)) (t : Term S Γ s)
    (env : Assignment M.carrier Γ) :
    t.withRegions.denote M env = t.denote M.restrictRegionless env :=
  Proofs.MLIR.Institution.denote_withRegions M t env

/-- Translating an equation and restricting a model preserve and reflect satisfaction. -/
theorem satisfaction_withRegions (M : Model (Signature.withRegions.obj S)) (e : Equation S) :
    e.withRegions.Holds M ↔ e.Holds M.restrictRegionless := by
  simp only [Equation.Holds, Equation.withRegions, Term.denote_withRegions]
  rfl

/-- The regionless institution maps into the isolated-region institution along the
signature inclusion, as a natural family of corridors. -/
def includeRegionless :
    institution (withRegions := false) ⟶
      Signature.withRegions ⋙ institution (withRegions := true) where
  app _ := ⟨Equation.withRegions, Discrete.functor (fun M => Discrete.mk M.restrictRegionless),
    fun M e => satisfaction_withRegions M.as e⟩
  naturality {_ _} f := Room.hom_ext (Proofs.MLIR.Institution.withRegions_natural f)
    (Functor.ext (fun M => by cases M; rfl))

end Silmaril.MLIR.Institution
