module

public import Silmaril.Semantics.Page.Defs

@[expose] public section
namespace Silmaril.Semantics.Page.Examples

/-- Only page zero is eligible for allocation in this fixture. -/
def singlePage (Content : Type) : Model Nat Content (MapMemory Nat Content) :=
  ⟨mapStore Nat Content, fun _ p => p = 0⟩

def empty (Content : Type) : MapMemory Nat Content := fun _ => .absent

def uninitialized (Content : Type) : MapMemory Nat Content := override (empty Content) 0 .undef

def initializeThenRead : Program Nat Bool Bool := (Program.write 0 true).bind fun _ => Program.read 0

def chooseBit : Program Nat Bool Bool := .choose (.pure false) (.pure true)

def bitPost (bit : Bool) (_ : MapMemory Nat Bool) (image : Image Nat Bool) : Prop :=
  image 0 = some bit

end Silmaril.Semantics.Page.Examples
