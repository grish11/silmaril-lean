module

public import Silmaril.Games.Category.Defs
public import Silmaril.Games.Handler.Defs
public import Silmaril.Logic.BrookesSC.Defs

/-! Forget the SC designation in the interface presented to an effect client. -/

@[expose] public section

namespace Silmaril.Games.BrookesSC

open CategoryTheory Silmaril.Logic.BrookesSC

universe u

variable {W : World.{u}} {S T U : Signature W}

/-- An effect request is an SC operation label packaged with its designation.
The ordinary effect interface carries only its request and reply types. -/
def events (S : Signature W) : Sig.{u} :=
  ⟨Sigma S.Op, fun q => q.1.Reply⟩

/-- Forward requests and use the target reply verbatim. -/
def eventHom (f : S ⟶ T) : Sig.Hom (events S) (events T) :=
  ⟨fun q => ⟨q.1, f.label q.2⟩, fun _ r => r⟩

-- These laws use the request/reply maps, before any conversion to strategies.
@[simp] theorem eventHom_id : eventHom (𝟙 S) = Sig.Hom.id (events S) := rfl

@[simp] theorem eventHom_comp (f : S ⟶ T) (g : T ⟶ U) :
    eventHom (f ≫ g) = (eventHom f).comp (eventHom g) := rfl

/-- Implement the source interface by forwarding to the target in the game category. -/
def forwarding (f : S ⟶ T) : events T ⟶ events S :=
  Strategy.ofHandler (Handler.ofHom (eventHom f))

end Silmaril.Games.BrookesSC
