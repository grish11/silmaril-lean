module

public import Silmaril.Logic.Fragments.Institution.Defs

@[expose] public section
namespace Silmaril.Logic.Fragments.Proofs
open CategoryTheory Silmaril.Logic.Institution
universe u

theorem corridor_id (F : Fragment.{u}) (R : Room.{u,u,u}) : F.corridor (𝟙 R) = 𝟙 (F.room R) := by
  apply Room.hom_ext
  · exact funext fun p => F.map_id p
  · rfl

theorem corridor_comp (F : Fragment.{u}) {R S T : Room.{u,u,u}} (c : R ⟶ S) (d : S ⟶ T) :
    F.corridor (c ≫ d) = F.corridor c ≫ F.corridor d := by
  apply Room.hom_ext
  · exact funext fun p => F.map_comp c.sen d.sen p
  · rfl

end Silmaril.Logic.Fragments.Proofs
