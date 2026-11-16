module

public import Silmaril.Logic.Algebraic.OrderSorted.Free.Defs
import Silmaril.Proofs.Logic.Algebraic.OrderSorted.FreeUniversal

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.OrderSorted.Free
open CategoryTheory CategoryTheory.Limits
@[ext] theorem hom_ext {A : Signature} {M N : Model A} (f g : M ⟶ N)
    (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

variable {A : Signature} {k : ℕ} {Γ : Fin k → A.base.S}

/-- Evaluation uniquely extends the prescribed finite sorted generator assignment. -/
theorem fold_unique {M : Model A} (f : model A Γ ⟶ M)
    (v : ∀ i, M.algebra.carrier (Γ i)) (hv : ∀ i, f.map (Γ i) (generator i) = v i) :
    f = foldHom M v := by
  apply hom_ext
  funext s x
  exact Silmaril.Proofs.Logic.Algebraic.OrderSorted.FreeUniversal.onNormal f v hv x

/-- The universal property retains every actual coherent algebra homomorphism. -/
def freeHomEquiv (Γ : Fin k → A.base.S) (M : Model A) :
    (model A Γ ⟶ M) ≃ ((i : Fin k) → M.algebra.carrier (Γ i)) where
  toFun f i := f.map (Γ i) (generator i)
  invFun := foldHom M
  left_inv f := (fold_unique f _ (fun _ => rfl)).symm
  right_inv v := funext (eval_generator M v)

/-- Evaluation commutes with every actual homomorphism, including noninjective ones. -/
theorem fold_natural {M N : Model A} (v : ∀ i, M.algebra.carrier (Γ i)) (f : M ⟶ N) :
    foldHom M v ≫ f = foldHom N (fun i => f.map (Γ i) (v i)) := by
  apply fold_unique
  intro i
  change f.map _ (eval M v (generator i)) = _
  rw [eval_generator]

/-- No generator inhabitance is needed: the closed coherent term model is initial. -/
def closed_isInitial (A : Signature) : IsInitial (closedModel A) :=
  IsInitial.ofUniqueHom (fun M => foldHom M (fun i => i.elim0)) (by
    intro M f
    exact fold_unique f _ (fun i => i.elim0))

end Silmaril.Logic.Algebraic.OrderSorted.Free
