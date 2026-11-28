module

public import Silmaril.Games.BrookesSC.Defs
import Silmaril.Games.Handler.Thms

public section

namespace Silmaril.Proofs.Games.BrookesSC

open CategoryTheory Silmaril.Games Silmaril.Games.BrookesSC Silmaril.Logic.BrookesSC

universe u

variable {W : World.{u}} {S T U : Signature W}

theorem forwarding_id : forwarding (𝟙 S) = 𝟙 (events S) :=
  Strategy.ofHandler_id (events S)

theorem forwarding_comp (f : S ⟶ T) (g : T ⟶ U) :
    forwarding (f ≫ g) = forwarding g ≫ forwarding f := by
  change Strategy.ofHandler (Handler.ofHom (eventHom (f ≫ g))) =
    (Strategy.ofHandler (Handler.ofHom (eventHom g))).comp
      (Strategy.ofHandler (Handler.ofHom (eventHom f)))
  rw [← Strategy.ofHandler_comp]
  rfl

end Silmaril.Proofs.Games.BrookesSC
