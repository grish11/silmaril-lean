module

public import Silmaril.SSA.Isotope.Institution.Adapters.UpperPowerset.Defs

@[expose] public section

namespace Silmaril.Isotope.Institution.Adapters.UpperPowerset.Proofs

open CategoryTheory Semantics
open LetIter.ProofRelevant.Semantics (TypeModel TyDen)

universe u v

variable {τ ε : Type u} [TypeFormers τ] [Subtyping τ] [Bot ε] [TypeModel.{u, v} τ]
  {S T U : InstrSig τ ε}

private theorem instruction_heq {X Y : LetParIter.Institution.Model.{u, v} S} (h : X = Y) :
    HEq X.instructions Y.instructions := by
  cases h
  rfl

theorem reduct_comp (pair : Elgot.ParallelPairing (SetM : Type v → Type v))
    (f : S ⟶ T) (g : T ⟶ U) (X : Model.{u, v} U) :
    X.reduct pair (f ≫ g) = (X.reduct pair g).reduct pair f :=
  congrArg Model.mk (eq_of_heq (instruction_heq
    (congrArg (fun F : LetParIter.Institution.Model U ⥤ LetParIter.Institution.Model S =>
      F.obj (X.toNative pair)) (LetParIter.Institution.reductFunctor_comp f g))))

theorem strict_arrow_iff (pair : Elgot.ParallelPairing (SetM : Type v → Type v))
    (X Y : Model.{u, v} S) :
    Nonempty (X ⟶ Y) ↔
      ∃ H : LetParIter.Institution.Model.Hom (X.toNative pair) (Y.toNative pair),
        ∀ (A : Type v) (a : SetM A), H.app a = a := by
  constructor
  · rintro ⟨h⟩
    cases h.down
    exact ⟨𝟙 (X.toNative pair), fun _ _ => rfl⟩
  · rintro ⟨H, identity⟩
    have h : X.instructions.denote = Y.instructions.denote := by
      funext op a
      exact (identity _ _).symm.trans (H.map_instr op a)
    have hp : X.instructions.denotePure = Y.instructions.denotePure :=
      funext fun op => funext fun p => funext fun a => H.map_pureInstr op p a
    cases X with
    | mk I =>
      cases Y with
      | mk J =>
        cases I
        cases J
        cases h
        cases hp
        exact ⟨⟨rfl⟩⟩

private theorem membership_transport {A B C E : τ} (hs : A = B) (ht : C = E)
    (eval : TyDen A → SetM (TyDen C)) (a : TyDen B) (b : TyDen E) :
    b ∈ (ht ▸ eval (hs.symm ▸ a) : SetM (TyDen E)).run ↔
      cast (congrArg TyDen ht.symm) b ∈ (eval (cast (congrArg TyDen hs.symm) a)).run := by
  cases hs
  cases ht
  rfl

theorem toCase_reduct_obj (pair : Elgot.ParallelPairing (SetM : Type v → Type v))
    (f : S ⟶ T) (X : Model.{u, v} T) :
    Model.toCase.obj (X.reduct pair f) = (Model.toCase.obj X).reduct f := by
  let make (eval : (op : S.Instr) → TyDen (instrSrc op) → TyDen (instrTrg op) → Prop) :
      Powerset.Model (TyDen (τ := τ)) S := ⟨⟨eval⟩⟩
  apply congrArg make
  funext op a b
  exact propext (membership_transport (f.source op) (f.target op) (X.instructions.denote (f.instr op)) a b)

end Silmaril.Isotope.Institution.Adapters.UpperPowerset.Proofs
