module

public import Silmaril.Logic.Fragments.Institution.Defs
import Silmaril.Proofs.Logic.Fragments.Institution

@[expose] public section
namespace Silmaril.Logic.Fragments
open CategoryTheory Silmaril.Logic.Institution
universe u

theorem Fragment.corridor_id (F : Fragment.{u}) (R : Room.{u,u,u}) : F.corridor (𝟙 R) = 𝟙 (F.room R) :=
  Proofs.corridor_id F R
theorem Fragment.corridor_comp (F : Fragment.{u}) {R S T : Room.{u,u,u}} (c : R ⟶ S) (d : S ⟶ T) :
    F.corridor (c ≫ d) = F.corridor c ≫ F.corridor d := Proofs.corridor_comp F c d

/-- Every supplied fragment is a proved endofunctor of rooms, hence extends
any institution of these universes, including an atom-only base institution. -/
def Fragment.rooms (F : Fragment.{u}) : Room.{u,u,u} ⥤ Room.{u,u,u} where
  obj := F.room
  map := F.corridor
  map_id := F.corridor_id
  map_comp := F.corridor_comp

def Fragment.institution {Sign : Type*} [Category Sign] (F : Fragment.{u})
    (I : Sign ⥤ Room.{u,u,u}) : Sign ⥤ Room.{u,u,u} := I ⋙ F.rooms

theorem atomicCorridor_id (A : AtomicSignature.{u}) : atomicCorridor (𝟙 A) = 𝟙 (atomicRoom A) := by
  apply Room.hom_ext
  · rfl
  · exact Functor.ext (fun _ => rfl) (fun _ _ _ => @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _)

theorem atomicCorridor_comp {A B C : AtomicSignature.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    atomicCorridor (f ≫ g) = atomicCorridor f ≫ atomicCorridor g := by
  apply Room.hom_ext
  · rfl
  · exact Functor.ext (fun _ => rfl) (fun _ _ _ => @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _) _ _)

def atomicInstitution : AtomicSignature.{u} ⥤ Room.{u,u,u} where
  obj := atomicRoom
  map := atomicCorridor
  map_id := atomicCorridor_id
  map_comp := atomicCorridor_comp

/-- A fragment over arbitrary raw typed atoms; neither finite supports nor
machine semantics are required. Reducts are predicate precomposition. -/
def Fragment.atomic (F : Fragment.{u}) : AtomicSignature.{u} ⥤ Room.{u,u,u} :=
  F.institution atomicInstitution

end Silmaril.Logic.Fragments
