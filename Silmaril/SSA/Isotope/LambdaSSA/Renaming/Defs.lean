module

public import Silmaril.SSA.Isotope.LambdaSSA.Kleisli.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Typing.Thms

/-! # Pulling a monadic λSSA environment back along typed renaming -/

@[expose] public section

universe u v q r

namespace Silmaril.Isotope.LambdaSSA.Semantics.Monadic

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Elgot

variable {τ : Type u} [TypeFormers τ] [Silmaril.Isotope.Subtyping τ] [TypeModel.{u, v} τ]

/-- Pull an environment back along a type-preserving variable renaming. -/
def Env.rename {Γ Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren Γ Δ ρ) (δ : Env Δ) : Env Γ :=
  match Γ with
  | [] => PUnit.unit
  | A :: Γ =>
      (Env.rename (Γ := Γ) (Δ := Δ) (ρ := fun i => ρ (i + 1))
        (fun ⦃i B⦄ hi => hρ (i := i + 1)
          (by simpa [LambdaSSA.At] using hi)) δ,
       Env.get δ (ρ 0) (hρ (by simp [LambdaSSA.At])))

@[simp] theorem Env.rename_nil {Δ : LambdaSSA.VCtx τ} {ρ : Nat → Nat}
    (hρ : LambdaSSA.Ren [] Δ ρ) (δ : Env Δ) :
    Env.rename hρ δ = PUnit.unit := rfl

end Silmaril.Isotope.LambdaSSA.Semantics.Monadic
