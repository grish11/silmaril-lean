module

public import Silmaril.Semantics.Calco2019.Examples.TypeKleisli.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.TypeKleisli

/-! # From function-level laws to the CALCO Kleisli interface -/

public section

namespace Silmaril.Calco2019.Examples.TypeKleisli

universe u

open CategoryTheory

variable {m : Type u → Type u} [_root_.Monad m] [LawfulMonad m]

/-- The inherited sums give the CALCO guarded Elgot bundle. Dinaturality follows
from the other equations by Proposition 17. -/
noncomputable def assemble {G : Guard m} (I : Iteration m G) :
    GuardedElgotMonad typeCoproducts :=
  Proofs.assemble I

/-- The concrete guard on the inherited coproducts of the Kleisli category. -/
noncomputable def categoricalGuard (G : Guard m) :
    MonadGuardedness typeCoproducts (ofTypeMonad m) :=
  Proofs.guard m G

theorem iterative_iff (G : Guard m) : (categoricalGuard G).Iterative ↔ G.HasUniqueFixpoints :=
  Proofs.iterative_iff G

end Silmaril.Calco2019.Examples.TypeKleisli
