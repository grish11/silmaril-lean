module

public import Silmaril.Semantics.Calco2019.ExceptionUniformity
public import Silmaril.Semantics.Calco2019.Thms
import Silmaril.Proofs.Semantics.Calco2019.ExceptionElgot

/-! # Guarded Elgot structure of the exception family in Example 22 -/

public section

universe u v

namespace Silmaril.Calco2019.Exception

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (T : GuardedElgotMonad P)

/-- Moving exceptions into the return summand transports the two Conway equations. -/
theorem naturalCodiagonal (E : C) : (fixpoints T E).NaturalCodiagonal where
  naturality := Proofs.exception_naturality T E
  codiagonal := Proofs.exception_codiagonal T E

/-- At each exception parameter, iteration is inherited from the guarded Elgot base. -/
@[expose]
noncomputable def fibre (E : C) : GuardedElgotMonad P where
  monad := (family P T.monad).obj E
  guard := guardedness T E
  iteration :=
    { toFixpoints := fixpoints T E
      naturalCodiagonal := naturalCodiagonal T E
      dinaturality := (fixpoints T E).dinaturality_of_uniform
        (P.kleisliPreservesSelected _) (fun X => ⟨X.of, rfl⟩)
        (naturalCodiagonal T E) (uniformity T E) }
  uniformity := uniformity T E

/-- Change of exception parameter is a guarded Elgot monad morphism. -/
@[expose]
noncomputable def guardedChange {E E' : C} (h : E ⟶ E') :
    GuardedElgotMonadHom P (fibre T E) (fibre T E') where
  hom := (family P T.monad).map h
  guarded := change_preserves T h
  iteration := fun _ hf => change_iterate T h hf

/-- The exception family is functorial in its exception parameter. -/
@[expose]
noncomputable def guardedFamily : ParametrizedGuardedElgotMonad P where
  obj := fibre T
  map := guardedChange T
  map_id E := GuardedElgotMonadHom.ext ((family P T.monad).map_id E)
  map_comp h k := GuardedElgotMonadHom.ext ((family P T.monad).map_comp h k)

/-- Example 22. The family `X # W = T (X + H W)` forms a parametrized guarded Elgot monad. -/
@[expose]
noncomputable def parametrizedElgot (H : C ⥤ C) : ParametrizedGuardedElgotMonad P :=
  H ⋙ guardedFamily T

end Silmaril.Calco2019.Exception
