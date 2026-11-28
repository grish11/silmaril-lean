module

public import Silmaril.SSA.Isotope.LetParIter.Institution.Defs
import Silmaril.Proofs.SSA.Isotope.LetParIter.Institution.Laws

/-! # Change of signature for native LetParIter equations -/

@[expose] public section

namespace Silmaril.Isotope.LetParIter.Institution

open CategoryTheory LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Logic.Institution (Room)

universe u v w

variable {τ ε : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {P Q R : InstrSig τ ε}
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ}

@[simp] theorem Expr.map_id (a : Expr P Γ β A) : a.map (𝟙 P) = a :=
  Proofs.expr_map_id a

theorem Expr.map_comp (σ : P ⟶ Q) (θ : Q ⟶ R) (a : Expr P Γ β A) :
    (a.map σ).map θ = a.map (σ ≫ θ) :=
  Proofs.expr_map_comp σ θ a

@[simp] theorem Sentence.map_id (s : Sentence P ν) : s.map (𝟙 P) = s :=
  Proofs.sentence_map_id s

theorem Sentence.map_comp (σ : P ⟶ Q) (θ : Q ⟶ R) (s : Sentence P ν) :
    (s.map σ).map θ = s.map (σ ≫ θ) :=
  Proofs.sentence_map_comp σ θ s

variable [Subtyping τ] [Bot ε] [TypeModel.{u, v} τ]

omit [TypeFormers τ] [Subtyping τ] [TypeModel τ] in
/-- A signature map preserves and reflects the designated bottom purity of an instruction. -/
theorem pure_iff (σ : P ⟶ Q) (f : P.Instr) :
    IsPure (⊥ : ε) (σ.instr f) ↔ IsPure (⊥ : ε) f := by
  rw [IsPure, IsPure, σ.effect f]

@[simp] theorem reductFunctor_id (P : InstrSig τ ε) : reductFunctor (𝟙 P) = 𝟭 (Model P) :=
  Proofs.reduct_id P

theorem reductFunctor_comp (σ : P ⟶ Q) (θ : Q ⟶ R) :
    reductFunctor (σ ≫ θ) = reductFunctor θ ⋙ reductFunctor σ :=
  Proofs.reduct_comp σ θ

/-- Evaluation after sentence translation agrees with evaluation in the reduct. -/
theorem Model.eval_reduct (σ : P ⟶ Q) (M : Model Q) (a : Expr P Γ β A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    M.eval (a.map σ) γ ρ = (M.reduct σ).eval a γ ρ :=
  Proofs.eval_reduct σ M a γ ρ

/-- A strict model arrow commutes with evaluation at every exact derivation. -/
theorem Model.Hom.eval {M N : Model P} (F : Model.Hom M N)
    (a : Expr P Γ β A) (γ : CtxDen Γ) (ρ : BoundDen β) :
    F.app (M.eval a γ ρ) = N.eval a γ ρ :=
  Proofs.eval_hom F a γ ρ

/-- Truth of actual native term equations is invariant under change of signature. -/
theorem satisfaction (σ : P ⟶ Q) (M : Model Q) (s : Sentence P ν) :
    Sat M (s.map σ) ↔ Sat (M.reduct σ) s :=
  Proofs.satisfaction σ M s

/-- The model category and equations at one native signature. -/
def room (P : InstrSig τ ε) (ν : Type w) [DecidableEq ν] :
    Room.{max u w, v + 1, max u (v + 1)} where
  Sen := Sentence P ν
  Mod := Cat.of (Model P)
  Sat := Sat

/-- The institution of native LetParIter equations over a fixed value model. -/
def inst (ν : Type w) [DecidableEq ν] :
    InstrSig τ ε ⥤ Room.{max u w, v + 1, max u (v + 1)} where
  obj P := room P ν
  map σ := ⟨Sentence.map σ, reductFunctor σ, satisfaction σ⟩
  map_id P := Room.hom_ext (funext Sentence.map_id) (reductFunctor_id P)
  map_comp σ θ := Room.hom_ext (funext fun s => (Sentence.map_comp σ θ s).symm)
    (reductFunctor_comp σ θ)

end Silmaril.Isotope.LetParIter.Institution
