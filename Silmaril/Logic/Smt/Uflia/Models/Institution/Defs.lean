module

public import Silmaril.Logic.Smt.Uflia.Models.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia
open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution

namespace HomModels

/-- All existing models and all actual UF homomorphisms, at one signature. -/
noncomputable def room {U : Type} (A : Signature U) : Room.{0,0,1} :=
  ⟨Formula A, Cat.of (Model A), Model.Holds⟩

noncomputable def corridor {U : Type} {A B : Signature U} (f : A ⟶ B) :
    room A ⟶ room B :=
  ⟨Term.map f, Model.reductFunctor f, Model.holds_map f⟩

noncomputable def institution (U : Type) : Signature U ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id A := Room.hom_ext (funext Term.map_id) (Model.reductFunctor_id A)
  map_comp f g := Room.hom_ext (funext (Term.map_comp f g)) (Model.reductFunctor_comp f g)

noncomputable def inst (U : Type) : Inst.{1,0,0,0,1} := ⟨Signature U, institution U⟩

/-- Equality transport supplies a genuine UF homomorphism. This includes the
old discrete model presentation in the new category without inventing maps. -/
def ofDiscrete {U : Type} (A : Signature U) : Disc (Model A) ⥤ Model A where
  obj M := M
  map h := eqToHom h.down
  map_id _ := rfl
  map_comp f g := by
    rcases f with ⟨hf⟩
    cases hf
    rcases g with ⟨hg⟩
    cases hg
    rfl

/-- The old discrete rooms remain available through an exact comparison.
The corridor reverses model translation, so its direction is homs to discrete. -/
noncomputable def toDiscrete (U : Type) : Inst.CoHom (inst U) (Uflia.institution U) where
  Φ := 𝟭 _
  ρ :=
    { app A := ⟨id, ofDiscrete A, fun _ _ => Iff.rfl⟩
      naturality := by
        intro A B f
        refine Room.hom_ext ?_ ?_
        · rfl
        · refine Functor.ext ?_ ?_
          · intro M
            rfl
          · intro M N h
            rcases h with ⟨same⟩
            cases same
            rfl }

theorem toDiscrete_modelExpansive {U : Type} (A : Signature U) :
    ((toDiscrete U).ρ.app A).ModelExpansive := fun M => ⟨M, rfl⟩

end HomModels

namespace EmbeddingModels

/-- The same model objects, with injective user-carrier maps as arrows. -/
noncomputable def room {U : Type} (A : Signature U) : Room.{0,0,1} :=
  ⟨Formula A, Cat.of (EmbeddingModel A), fun M φ => M.model.Holds φ⟩

noncomputable def corridor {U : Type} {A B : Signature U} (f : A ⟶ B) :
    room A ⟶ room B :=
  ⟨Term.map f, EmbeddingModel.reduct f, fun M φ => Model.holds_map f M.model φ⟩

noncomputable def institution (U : Type) : Signature U ⥤ Room.{0,0,1} where
  obj := room
  map := corridor
  map_id A := Room.hom_ext (funext Term.map_id) (EmbeddingModel.reduct_id A)
  map_comp f g := Room.hom_ext (funext (Term.map_comp f g)) (EmbeddingModel.reduct_comp f g)

noncomputable def inst (U : Type) : Inst.{1,0,0,0,1} := ⟨Signature U, institution U⟩

end EmbeddingModels

/-- Identity sentence translation, with the genuine embedding-to-hom functor
as the model reduct. The comparison changes arrows, not model existence. -/
noncomputable def HomModels.toEmbeddings (U : Type) :
    Inst.CoHom (HomModels.inst U) (EmbeddingModels.inst U) where
  Φ := 𝟭 _
  ρ :=
    { app A := ⟨id, EmbeddingModel.forget A, fun _ _ => Iff.rfl⟩
      naturality := fun {_ _} f => Room.hom_ext rfl (EmbeddingModel.forget_reduct f).symm }

theorem HomModels.toEmbeddings_modelExpansive {U : Type} (A : Signature U) :
    ((HomModels.toEmbeddings U).ρ.app A).ModelExpansive := fun M => ⟨⟨M⟩, rfl⟩

end Silmaril.Logic.Smt.Uflia
