module

public import Silmaril.SSA.MLIR.Institution.Regionless.Defs
public import Silmaril.SSA.MLIR.Institution.Thms

@[expose] public section

namespace Silmaril.Proofs.MLIR.Institution

open CategoryTheory Silmaril.MLIR.Institution

variable {S T : Signature false} {n : Nat} {Γ : Fin n → S.Ty} {s : S.Ty}

theorem withRegions_map (f : S ⟶ T) (t : Term S Γ s) :
    (t.map f).withRegions = t.withRegions.map (Signature.withRegions.map f) := by
  induction t with
  | var => rfl
  | app o args bodies i ih _ =>
    simp only [Term.map, Term.withRegions]
    congr
    · exact funext ih
    · funext r
      exact Fin.elim0 r

theorem denote_withRegions (M : Model (Signature.withRegions.obj S)) (t : Term S Γ s)
    (env : Assignment M.carrier Γ) :
    t.withRegions.denote M env = t.denote M.restrictRegionless env := by
  induction t with
  | var => rfl
  | app o args bodies i ih _ =>
    simp only [Term.withRegions, Term.denote, Model.restrictRegionless]
    congr
    · exact funext (fun j => ih j env)
    · funext r
      exact Fin.elim0 r

theorem withRegions_natural (f : S ⟶ T) :
    Equation.withRegions ∘ Equation.map f =
      Equation.map (Signature.withRegions.map f) ∘ Equation.withRegions := by
  funext e
  cases e
  simp only [Function.comp_apply, Equation.withRegions, Equation.map, withRegions_map]
  rfl

end Silmaril.Proofs.MLIR.Institution
