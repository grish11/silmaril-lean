module

public import Silmaril.SSA.Isotope.Institution.Adapters.Powerset.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.Adapters.Powerset

/-! # Exact LetSeq and LetCase comparisons with powerset parallel models -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Adapters.Powerset

open CategoryTheory Semantics Silmaril.Logic.Institution
open Parallel (Tier CaseTypes Control ParOp)
open Parallel.Institution (Equation)

universe u v

variable {τ ε : Type u} {S T U : InstrSig τ ε} {D : τ → Type v}
  {ν : Type u} [DecidableEq ν] {Γ : Ctx ν τ}

namespace Model

/-- A powerset model reduct agrees with the strict native reduct on objects. -/
theorem toParallel_reduct (f : S ⟶ T) (X : Model D T)
    (pair : ParOp (SetM : Type v → Type v)) :
    (X.reduct f).toParallel pair = (X.toParallel pair).reduct f :=
  Proofs.parallel_reduct f X pair

/-- The models admit exactly the strict arrows with identity computation maps. -/
theorem strict_arrow_iff (pair : ParOp (SetM : Type v → Type v)) (X Y : Model D S) :
    Nonempty (X ⟶ Y) ↔
      ∃ H : Parallel.Institution.Model.Hom (X.toParallel pair) (Y.toParallel pair),
        ∀ (A : Type v) (a : SetM A), H.app a = a :=
  Proofs.strict_arrow_iff pair X Y

/-- Forgetting the restriction commutes with native reducts on objects and arrows. -/
theorem toParallelFunctor_reduct (f : S ⟶ T) (pair : ParOp (SetM : Type v → Type v)) :
    reductFunctor f ⋙ toParallelFunctor (D := D) pair =
      toParallelFunctor pair ⋙ Parallel.Institution.Model.reductFunctor f :=
  Proofs.toParallelFunctor_reduct f pair

/-- The comparison commutes with signature reducts, including their action on arrows. -/
theorem toRelational_reduct (f : S ⟶ T) :
    reductFunctor f ⋙ toRelational (D := D) =
      toRelational ⋙ Relational.Model.reductFunctor D f :=
  Proofs.toRelational_reduct f

theorem reductFunctor_comp (f : S ⟶ T) (g : T ⟶ U) :
    reductFunctor (D := D) (f ≫ g) = reductFunctor g ⋙ reductFunctor f :=
  CategoryTheory.Functor.ext (fun X => congrArg Model.mk (Relational.Model.reduct_comp f g X.relational))
    (fun _ _ _ => Subsingleton.elim _ _)

end Model

section Rooms

variable [HasProduct τ] [HasUnit τ] [ProductModel D] [UnitModel D]

theorem room_sat_map {tier : Tier} [CaseTypes tier τ] (h : tier ≠ .iter)
    (C : Control tier D Id) (pair : ParOp (SetM : Type v → Type v)) (f : S ⟶ T)
    (X : Model D T) (φ : Equation S tier Γ) :
    (room h C Γ pair T).Sat X (φ.map f) ↔ (room h C Γ pair S).Sat (X.reduct f) φ :=
  Proofs.room_sat_map h C pair f X φ

/-- Observe exact equations in the powerset profile with an arbitrary fixed pairing.
Satisfaction compares the two stored derivations by equality of computations. -/
def observation {tier : Tier} [CaseTypes tier τ] (h : tier ≠ .iter) (C : Control tier D Id)
    (Γ : Ctx ν τ) (pair : ParOp (SetM : Type v → Type v)) :
    InstrSig τ ε ⥤ Room.{u, 0, max u v} where
  obj := room h C Γ pair
  map f := ⟨Equation.map f, Model.reductFunctor f, room_sat_map h C pair f⟩
  map_id _ := Room.hom_ext (funext Equation.map_id) rfl
  map_comp f g :=
    Room.hom_ext (funext fun φ => (φ.map_comp f g).symm) (Model.reductFunctor_comp f g)

end Rooms

section Seq

variable [HasProduct τ] [HasUnit τ]

theorem ofLetSeq_map (f : S ⟶ T) (φ : Relational.LetSeq.Sentence S Γ) :
    (ofLetSeq φ).map f = ofLetSeq (Relational.LetSeq.Sentence.translate f φ) :=
  Proofs.ofLetSeq_map f φ

variable [ProductModel D] [UnitModel D]

/-- Full equality in this powerset interpretation is exactly equality of successful results. -/
theorem ofLetSeq_sat (pair : ParOp (SetM : Type v → Type v)) (X : Model D S)
    (φ : Relational.LetSeq.Sentence S Γ) :
    (room (by decide) (Control.seq D Id) Γ pair S).Sat X (ofLetSeq φ) ↔
      Relational.LetSeq.Sentence.Satisfies X.relational φ :=
  Proofs.ofLetSeq_sat pair X φ

/-- Include exact LetSeq sentences over the identity instruction signature. -/
def letSeq (Γ : Ctx ν τ) (pair : ParOp (SetM : Type v → Type v)) :
    Inst.CoHom ⟨InstrSig τ ε, Relational.LetSeq.institution D Γ⟩
      ⟨InstrSig τ ε, observation (by decide) (Control.seq D Id) Γ pair⟩ where
  Φ := 𝟭 _
  ρ :=
    { app := fun _ => ⟨ofLetSeq, Model.toRelational, ofLetSeq_sat pair⟩
      naturality := fun _ _ f =>
        Room.hom_ext (funext fun φ => (ofLetSeq_map f φ).symm) (Model.toRelational_reduct f).symm }

end Seq

section Case

variable [TypeFormers τ]

theorem ofLetCase_map (f : S ⟶ T) (φ : Relational.LetCase.Sentence S Γ) :
    (ofLetCase φ).map f = ofLetCase (Relational.LetCase.Sentence.translate f φ) :=
  Proofs.ofLetCase_map f φ

variable [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]

/-- The native case evaluator interprets abort using the fixed empty-type equivalence. -/
theorem ofLetCase_sat (pair : ParOp (SetM : Type v → Type v)) (X : Model D S)
    (φ : Relational.LetCase.Sentence S Γ) :
    (room (by decide) (Control.case D Id) Γ pair S).Sat X (ofLetCase φ) ↔
      Relational.LetCase.Sentence.Satisfies X.relational φ :=
  Proofs.ofLetCase_sat pair X φ

/-- Include exact LetCase sentences over the identity instruction signature. -/
def letCase (Γ : Ctx ν τ) (pair : ParOp (SetM : Type v → Type v)) :
    Inst.CoHom ⟨InstrSig τ ε, Relational.LetCase.institution D Γ⟩
      ⟨InstrSig τ ε, observation (by decide) (Control.case D Id) Γ pair⟩ where
  Φ := 𝟭 _
  ρ :=
    { app := fun _ => ⟨ofLetCase, Model.toRelational, ofLetCase_sat pair⟩
      naturality := fun _ _ f =>
        Room.hom_ext (funext fun φ => (ofLetCase_map f φ).symm) (Model.toRelational_reduct f).symm }

/-- Widen LetPar equations within the same powerset model restriction. -/
def letParCaseInclusion (Γ : Ctx ν τ) (pair : ParOp (SetM : Type v → Type v)) :
    Inst.CoHom ⟨InstrSig τ ε, observation (by decide) (Control.seq D Id) Γ pair⟩
      ⟨InstrSig τ ε, observation (by decide) (Control.case D Id) Γ pair⟩ where
  Φ := 𝟭 _
  ρ :=
    { app := fun _ => ⟨fun φ => φ.ofLetPar, 𝟭 _, fun X φ => φ.ofLetPar_sat (X.toParallel pair)⟩
      naturality := fun _ _ f => Room.hom_ext (funext fun φ => (φ.ofLetPar_map f).symm) rfl }

end Case
end Silmaril.Isotope.Institution.Adapters.Powerset
