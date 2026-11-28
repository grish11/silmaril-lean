module

public import Silmaril.Logic.Abstraction.Propositional.Defs
public import Silmaril.Logic.Abstraction.FirstOrder.Thms
import Silmaril.Proofs.Logic.Abstraction.Propositional.Correctness

@[expose] public section

namespace Silmaril.Logic.Abstraction.Propositional

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples

variable {P Q : Type}

/-- A translated formula agrees with the valuation read off any corresponding UFOL structure. -/
theorem holds_toUFOL (M : UFOL.Structure (signature P)) (φ : PL.Formula P) :
    UFOL.Sentence.Holds M (toUFOL φ) ↔ φ.eval (valuation M) :=
  Proofs.Logic.Abstraction.Propositional.holds_toUFOL M φ

theorem toUFOL_map (f : P ⟶ Q) (φ : PL.Formula P) :
    toUFOL (φ.rename f) = (toUFOL φ).map (signatureFunctor.map f) :=
  Proofs.Logic.Abstraction.Propositional.toUFOL_map f φ

/-- UFOL homomorphisms induce propositional model arrows by preserving nullary predicates. -/
def modelFunctor (P : Type) : UFOL.Structure (signature P) ⥤ PL.Model P where
  obj M := ULift.up (valuation M)
  map {M N} h := ⟨fun p hp => by
    exact (congrArg (N.rel (n := 0) (⟨rfl⟩, p)) (Subsingleton.elim _ _)).mp (h.map_rel _ _ hp)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A propositional-to-UFOL comorphism on signatures of nullary predicates. -/
def toUFOLComorphism : Inst.CoHom PL.inst UFOL.inst where
  Φ := signatureFunctor
  ρ :=
    { app := fun P => ⟨toUFOL, modelFunctor P, holds_toUFOL⟩
      naturality := fun _ _ f => Room.hom_ext (funext (toUFOL_map f)) rfl }

/-- The composite comorphism from propositional logic to the canonical abstraction profile. -/
noncomputable def toProfile : Inst.CoHom PL.inst FirstOrder.profileInst :=
  toUFOLComorphism.comp FirstOrder.fromUFOL

/-- Translating a propositional formula agrees with its original truth under each valuation. -/
theorem sat_sentence (v : P → Prop) (φ : PL.Formula P) :
    (model v).Sat (sentence φ) ↔ φ.eval v :=
  (FirstOrder.sat_sentence (structureOf v) (toUFOL φ)).trans (holds_toUFOL (structureOf v) φ)

theorem sentence_map (f : P ⟶ Q) (φ : PL.Formula P) :
    sentence (φ.rename f) = (sentence φ).map (FirstOrder.signatureFunctor.map (signatureFunctor.map f)) :=
  (congrArg FirstOrder.sentence (toUFOL_map f φ)).trans (FirstOrder.sentence_map _ _)

/-- Canonical singleton models commute with propositional variable renaming. -/
theorem model_reduct (f : P ⟶ Q) (v : Q → Prop) :
    (model v).reduct (FirstOrder.signatureFunctor.map (signatureFunctor.map f)) = model (v ∘ f) :=
  FirstOrder.model_reduct _ (structureOf v)

/-- Every valuation is the reduct of a singleton UFOL structure. -/
theorem toUFOL_modelExpansive : toUFOLComorphism.ModelExpansive :=
  fun _ v => ⟨structureOf v.val, rfl⟩

/-- Every valuation comes from a canonical abstraction model with singleton object carrier. -/
theorem toProfile_modelExpansive : toProfile.ModelExpansive :=
  fun _ v => ⟨structureOf v.val, rfl⟩

/-- Propositional consequence is exactly consequence of the translations in the profile. -/
theorem entails_iff (P : Type) (Γ : Set (PL.Formula P)) (φ : PL.Formula P) :
    (PL.institution.obj P).Entails Γ φ ↔
      (FirstOrder.profileInst.I.obj (signature P)).Entails (sentence '' Γ) (sentence φ) :=
  toProfile.entails_iff toProfile_modelExpansive P Γ φ

end Silmaril.Logic.Abstraction.Propositional
