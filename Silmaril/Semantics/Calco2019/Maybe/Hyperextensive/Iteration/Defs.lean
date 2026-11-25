module

public import Silmaril.Semantics.Calco2019.Maybe.Hyperextensive.Thms
public import Silmaril.Semantics.Calco2019.ExceptionGuard

/-! # Canonical deterministic solutions on a hyperextensive category -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019.Maybe

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  {X Y E : C}

/-- Failure at a given result object. -/
def failure (E₀ : IsTerminal E) : X ⟶ P.sum Y E :=
  E₀.from X ≫ P.inr

/-- The value returned by each exact finite exit layer. -/
def LoopDecomposition.returnAt {f : X ⟶ P.sum Y X} (D : LoopDecomposition f) :
    (n : ℕ) → D.finite n ⟶ Y
  | 0 => D.result
  | n + 1 => D.advance n ≫ returnAt D n

/-- The solution is a fixpoint and gives failure on each invariant pure subcomputation. -/
def Canonical (E₀ : IsTerminal E) (f : X ⟶ P.sum (P.sum Y E) X)
    (s : X ⟶ P.sum Y E) : Prop :=
  f ≫ P.desc (𝟙 _) s = s ∧
  ∀ ⦃A : C⦄ (i : A ⟶ X) (k : A ⟶ A), i ≫ f = k ≫ i ≫ P.inr →
    i ≫ s = failure E₀

variable [Hyperextensive C]

/-- Choose a decomposition of the pure loop. Its induced solution is independent
of the choice by the canonical solution equations. -/
noncomputable def decompose (f : X ⟶ P.sum Y X) : LoopDecomposition f :=
  (hyperextensive_decompose f).some

/-- Run the finite branches and return the failure value on the invariant residual. -/
noncomputable def solve (E₀ : IsTerminal E) (f : X ⟶ P.sum (P.sum Y E) X) :
    X ⟶ P.sum Y E :=
  Cofan.IsColimit.desc (decompose f).isColimit
    (fun i => match i with
      | some n => (decompose f).returnAt n
      | none => failure E₀)


/-- A Maybe loop reads a failure as an explicit exit rather than as a recursive step. -/
noncomputable def loop (E₀ : IsTerminal E)
    (f : X ⟶ (monad P E).obj (P.sum Y X)) : X ⟶ P.sum Y E :=
  solve E₀ (f ≫ Exception.rearrange P E)

end Silmaril.Calco2019.Maybe
