module

public import Silmaril.Logic.Region.Defs
import Silmaril.Proofs.Logic.Region.Institution

@[expose] public section
namespace Silmaril.Logic.Region
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Semantics.Region

theorem satisfaction {A B : Signature} (f : A ⟶ B) (M : Model B) (p : Sentence A) :
    Sat M (p.map f) ↔ Sat (reduct f M) p := Proofs.satisfaction f M p
theorem map_id {A : Signature} (p : Sentence A) : p.map (𝟙 A) = p := Proofs.map_id p
theorem map_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) (p : Sentence A) :
    p.map (f ≫ g) = (p.map f).map g := Proofs.map_comp f g p
theorem reduct_id {A : Signature} (M : Model A) : reduct (𝟙 A) M = M := Proofs.reduct_id M
theorem reduct_comp {A B C : Signature} (f : A ⟶ B) (g : B ⟶ C) (M : Model C) :
    reduct (f ≫ g) M = reduct f (reduct g M) := Proofs.reduct_comp f g M
theorem reduct_laws {A B : Signature} (f : A ⟶ B) (M : Model B) (h : SegmentRegionLaws M) :
    SegmentRegionLaws (reduct f M) := Proofs.reduct_laws f M h

def room (A : Signature) : Room.{0, 0, 0} :=
  ⟨Sentence A, Cat.of (Discrete (Model A)), fun M p => Sat (Discrete.as M) p⟩
noncomputable def corridor {A B : Signature} (f : A ⟶ B) : room A ⟶ room B :=
  ⟨Sentence.map f, Discrete.functor fun M => Discrete.mk (reduct f M),
    fun M p => satisfaction f (Discrete.as M) p⟩

/-- A proved institution for raw relation renaming. No claim that semantic
region gluing, decoding, or arbitrary encodings are categorical. -/
noncomputable def institution : Signature ⥤ Room.{0, 0, 0} where
  obj := room
  map := corridor
  map_id _ := Room.hom_ext (funext fun p => map_id p)
    (CategoryTheory.Functor.ext (fun M => congrArg Discrete.mk (reduct_id (Discrete.as M)))
      (fun _ _ _ => @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _))
  map_comp f g := Room.hom_ext (funext fun p => map_comp f g p)
    (CategoryTheory.Functor.ext (fun M => congrArg Discrete.mk (reduct_comp f g (Discrete.as M)))
      (fun _ _ _ => @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _))

noncomputable def classic : ClassicInstitution.{1, 0, 0, 0, 0} Signature :=
  ClassicInstitution.ofRoomFunctor institution
end Silmaril.Logic.Region
