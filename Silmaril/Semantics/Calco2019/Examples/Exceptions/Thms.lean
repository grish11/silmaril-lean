module

public import Silmaril.Semantics.Calco2019.Examples.Exceptions.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.Exceptions

/-! # Iteration in the exception fibres of Example 22 -/

public section

universe u

namespace Silmaril.Calco2019.Examples.Exceptions

variable {m : Type u → Type u} [Monad m] [LawfulMonad m]
  [Elgot.Iterate m] [Elgot.LawfulElgotMonad m] {E F X Y : Type u}

/-- The total Elgot structure in each fibre is the existing exception iteration. -/
theorem fibre_isElgot : (fibre m E).IsElgot :=
  ofLawfulMonad_isElgot (ExceptT E m)

omit [Elgot.Iterate m] [Elgot.LawfulElgotMonad m] in
theorem adapt_pure (h : E → F) (x : X) :
    ExceptT.adapt h (pure x : ExceptT E m X) = pure x :=
  Proofs.adapt_pure h x

omit [Elgot.Iterate m] [Elgot.LawfulElgotMonad m] in
theorem adapt_bind (h : E → F) (p : ExceptT E m X) (k : X → ExceptT E m Y) :
    ExceptT.adapt h (p >>= k) = ExceptT.adapt h p >>= fun x => ExceptT.adapt h (k x) :=
  Proofs.adapt_bind h p k

/-- Changing the parameter by a function preserves the iteration of each loop. -/
theorem adapt_iter (h : E → F) (f : X → ExceptT E m (Y ⊕ X)) (x : X) :
    ExceptT.adapt h (Elgot.iter f x) = Elgot.iter (fun x => ExceptT.adapt h (f x)) x :=
  Proofs.adapt_iter h f x

/-- The parametrized guarded Elgot monad for the identity parameter functor on types. -/
noncomputable def parametrized (m : Type u → Type u) [Monad m] [LawfulMonad m]
    [Elgot.Iterate m] [Elgot.LawfulElgotMonad m] :
    ParametrizedGuardedElgotMonad typeCoproducts.{u} :=
  Proofs.parametrized m

@[simp] theorem parametrized_obj (E : Type u) : (parametrized m).obj E = fibre m E :=
  Proofs.parametrized_obj E

open CategoryTheory in
/-- Example 22 for a total Elgot type monad and any endofunctor on types. -/
noncomputable def parametrizedBy (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]
    [Elgot.Iterate m] [Elgot.LawfulElgotMonad m] (H : Type u ⥤ Type u) :
    ParametrizedGuardedElgotMonad typeCoproducts.{u} :=
  H ⋙ parametrized m

open CategoryTheory in
@[simp] theorem parametrizedBy_obj (H : Type u ⥤ Type u) (W : Type u) :
    (parametrizedBy m H).obj W = fibre m (H.obj W) := by
  change (parametrized m).obj (H.obj W) = _
  exact parametrized_obj _

end Silmaril.Calco2019.Examples.Exceptions
