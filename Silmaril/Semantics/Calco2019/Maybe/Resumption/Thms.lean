module

public import Silmaril.Semantics.Calco2019.Maybe.Types.Thms
public import Silmaril.Semantics.Calco2019.ExceptionResumption.Specializations
import Silmaril.Proofs.Semantics.Calco2019.Maybe.Resumption

/-! # Free total Elgot resumptions, CALCO 2019 §1.3 -/

public section

universe u v

namespace Silmaril.Calco2019.Maybe

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {P : Coproducts C} [HasInitial C]
  {T : GuardedElgotMonad P} (total : T.IsElgot) {H : C ⥤ C}
  (R : FinalResumptions (Exception.parametrizedElgot T H).toParametrizedMonad)

/-- Resumptions of an initial total Elgot monad freely add the operations of the
endofunctor. The natural transformation into each total target is unrestricted. -/
theorem resumption_freeOn (initial : IsInitial (⟨T, total⟩ : TotalElgot P))
    (S : TotalElgot P) (σ : H ⟶ (S.obj.monad : C ⥤ C)) :
    ∃! k : (⟨(Exception.parametrizedElgot T H).resumptionElgotMonad R,
        Exception.resumption_isElgot T H R total⟩ : TotalElgot P) ⟶ S,
      Exception.suspension T H R ≫ k.hom.hom.toNatTrans = σ :=
  Proofs.resumption_freeOn total R initial S σ

end Silmaril.Calco2019.Maybe
