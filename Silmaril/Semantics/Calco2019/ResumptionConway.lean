module

public import Silmaril.Semantics.Calco2019.ResumptionGuardThms
public import Silmaril.Semantics.Calco2019.Thms
import Silmaril.Proofs.Semantics.Calco2019.ResumptionConway

/-! # The guarded Elgot structure of the resumption monad (Theorem 25) -/

public section

universe u v

namespace Silmaril.Calco2019.ParametrizedGuardedElgotMonad

open CategoryTheory

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (M : ParametrizedGuardedElgotMonad P) (R : FinalResumptions M.toParametrizedMonad)

theorem resumption_naturalCodiagonal :
    (M.resumptionFixpoints R).NaturalCodiagonal :=
  Proofs.resumption_naturalCodiagonal M R

theorem resumption_uniformity :
    (M.resumptionFixpoints R).Uniform (Kleisli.Adjunction.toKleisli (R.monad P)) :=
  Proofs.resumption_uniformity M R

/-- The final-coalgebra resumption monad carries the observed guard and the
two-stage iteration, satisfying all guarded Elgot laws. -/
@[expose]
def resumptionElgotMonad : GuardedElgotMonad P where
  monad := R.monad P
  guard := M.resumptionGuardedness R
  iteration :=
    { toFixpoints := M.resumptionFixpoints R
      naturalCodiagonal := M.resumption_naturalCodiagonal R
      dinaturality := (M.resumptionFixpoints R).dinaturality_of_uniform
        (P.kleisliPreservesSelected (R.monad P)) (fun X => ⟨X.of, rfl⟩)
        (M.resumption_naturalCodiagonal R) (M.resumption_uniformity R) }
  uniformity := M.resumption_uniformity R

/-- The construction is totally guarded whenever all the parameter monads are. -/
theorem resumptionElgotMonad_isElgot (h : ∀ W : C, (M.obj W).IsElgot) :
    (M.resumptionElgotMonad R).IsElgot :=
  fun f => M.resumptionGuardedness_total R h f

end Silmaril.Calco2019.ParametrizedGuardedElgotMonad
