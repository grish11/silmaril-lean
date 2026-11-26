module

public import Silmaril.Games.BrookesSC.Defs
import Silmaril.Proofs.Games.BrookesSC.Forwarding

public section

namespace Silmaril.Games.BrookesSC

open CategoryTheory Opposite Silmaril.Logic.BrookesSC

universe u

variable {W : World.{u}} {S T U : Signature W}

@[simp] theorem forwarding_id : forwarding (𝟙 S) = 𝟙 (events S) :=
  Proofs.Games.BrookesSC.forwarding_id

@[simp] theorem forwarding_comp (f : S ⟶ T) (g : T ⟶ U) :
    forwarding (f ≫ g) = forwarding g ≫ forwarding f :=
  Proofs.Games.BrookesSC.forwarding_comp f g

/-- In the game category a forwarding strategy implements the source interface
on top of the target. Taking the opposite gives the signature-map direction. -/
@[expose] def eventFunctor (W : World.{u}) : Signature W ⥤ Sig.{u}ᵒᵖ where
  obj S := op (events S)
  map f := (forwarding f).op
  map_id _ := Quiver.Hom.unop_inj forwarding_id
  map_comp f g := Quiver.Hom.unop_inj (forwarding_comp f g)

end Silmaril.Games.BrookesSC
