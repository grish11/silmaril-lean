module

public import Silmaril.SSA.Isotope.Institution.Adapters.UpperPowerset.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.Adapters.UpperPowerset

/-! # LetParIter comparisons with the lower powerset and relational institutions -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Adapters.UpperPowerset

open CategoryTheory Semantics Silmaril.Logic.Institution
open LetIter.ProofRelevant.Semantics (TypeModel TyDen)
open Parallel (Control)

universe u v

variable {τ ε : Type u} [TypeFormers τ] [Subtyping τ] [Bot ε] [TypeModel.{u, v} τ]
  {S T U : InstrSig τ ε} {ν : Type u} [DecidableEq ν] {Γ : Ctx ν τ}

attribute [local instance] LetParIter.nativeProductModel LetParIter.nativeUnitModel
  Iteration.nativeCoproductModel Iteration.nativeEmptyModel

namespace Model

/-- The chosen model arrows are exactly the strict arrows with identity computation maps. -/
theorem strict_arrow_iff (pair : Elgot.ParallelPairing (SetM : Type v → Type v)) (X Y : Model.{u, v} S) :
    Nonempty (X ⟶ Y) ↔
      ∃ H : LetParIter.Institution.Model.Hom (X.toNative pair) (Y.toNative pair),
        ∀ (A : Type v) (a : SetM A), H.app a = a :=
  Proofs.strict_arrow_iff pair X Y

theorem reductFunctor_comp (pair : Elgot.ParallelPairing (SetM : Type v → Type v))
    (f : S ⟶ T) (g : T ⟶ U) :
    reductFunctor pair (f ≫ g) = reductFunctor pair g ⋙ reductFunctor pair f :=
  CategoryTheory.Functor.ext (Proofs.reduct_comp pair f g) (fun _ _ _ => Subsingleton.elim _ _)

theorem toCase_reduct (pair : Elgot.ParallelPairing (SetM : Type v → Type v)) (f : S ⟶ T) :
    reductFunctor pair f ⋙ toCase = toCase ⋙ Powerset.Model.reductFunctor f :=
  CategoryTheory.Functor.ext (Proofs.toCase_reduct_obj pair f) (fun _ _ _ => Subsingleton.elim _ _)

theorem toRelational_reduct (pair : Elgot.ParallelPairing (SetM : Type v → Type v)) (f : S ⟶ T) :
    reductFunctor pair f ⋙ toRelational = toRelational ⋙ Relational.Model.reductFunctor TyDen f :=
  CategoryTheory.Functor.ext (fun X => congrArg Powerset.Model.relational (Proofs.toCase_reduct_obj pair f X))
    (fun _ _ _ => Subsingleton.elim _ _)

end Model

/-- The native upper institution restricted to the fixed lawful powerset profile. -/
def observation (pair : Elgot.ParallelPairing (SetM : Type v → Type v)) (ν : Type u) [DecidableEq ν] :
    InstrSig τ ε ⥤ Room.{u, 0, max u v} where
  obj S := room pair S ν
  map f := ⟨LetParIter.Institution.Sentence.map f, Model.reductFunctor pair f,
    fun X φ => LetParIter.Institution.satisfaction f (X.toNative pair) φ⟩
  map_id _ := Room.hom_ext (funext LetParIter.Institution.Sentence.map_id) rfl
  map_comp f g := Room.hom_ext
    (funext fun φ => (LetParIter.Institution.Sentence.map_comp f g φ).symm)
    (Model.reductFunctor_comp pair f g)

/-- Include the relational LetIter sentences using native powerset equality. -/
def letIter (hΓ : Function.Surjective (Iteration.visibleEnv.{u, v} (Γ := Γ)))
    (pair : Elgot.ParallelPairing (SetM : Type v → Type v)) :
    Inst.CoHom ⟨InstrSig τ ε, Relational.LetIter.institution (TyDen (τ := τ)) Γ⟩
      ⟨InstrSig τ ε, observation pair ν⟩ where
  Φ := 𝟭 _
  ρ :=
    { app := fun _ => ⟨Iteration.ofLetIter, Model.toRelational,
        fun X φ => Iteration.set_satisfaction hΓ pair X.instructions φ⟩
      naturality := fun _ _ f =>
        Room.hom_ext (funext fun φ => (Iteration.ofLetIter_map f φ).symm) (Model.toRelational_reduct pair f).symm }

/-- Include the lower case sentences at the same lawful powerset pairing. -/
def letParCase (hΓ : Function.Surjective (Iteration.visibleEnv.{u, v} (Γ := Γ)))
    (pair : Elgot.ParallelPairing (SetM : Type v → Type v)) :
    Inst.CoHom ⟨InstrSig τ ε, Powerset.observation (by decide) (Control.case (TyDen (τ := τ)) Id)
        Γ (fun a b => pair.pair a b)⟩
      ⟨InstrSig τ ε, observation pair ν⟩ where
  Φ := 𝟭 _
  ρ :=
    { app := fun _ => ⟨Iteration.ofLetParCase, Model.toCase,
        fun X φ => Iteration.ofLetParCase_sat hΓ (X.toNative pair) φ⟩
      naturality := fun _ _ f =>
        Room.hom_ext (funext fun φ => (Iteration.ofLetParCase_map f φ).symm) (Model.toCase_reduct pair f).symm }

end Silmaril.Isotope.Institution.Adapters.UpperPowerset
