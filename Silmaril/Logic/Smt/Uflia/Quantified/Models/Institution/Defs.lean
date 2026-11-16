module

public import Silmaril.Logic.Smt.Uflia.Models.Institution.Defs
public import Silmaril.Logic.Smt.Uflia.Quantified.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.Quantified
open CategoryTheory Silmaril.Inst Silmaril.Logic.Institution

namespace HomModels

/-- All existing models and all actual UF homomorphisms, at one signature. -/
noncomputable def room {U : Type} (A : Signature U) : Room.{0,0,1} :=
  ⟨Sentence A, Cat.of (Model A), fun M p => p.Holds M⟩

noncomputable def corridor {U : Type} {A B : Signature U} (f : A ⟶ B) :
    room A ⟶ room B :=
  ⟨Term.map f, Model.reductFunctor f, fun M p => Sentence.holds_map f p M⟩

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
noncomputable def toDiscrete (U : Type) : Inst.CoHom (inst U) (Quantified.institution U) where
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

end Silmaril.Logic.Smt.Uflia.Quantified
