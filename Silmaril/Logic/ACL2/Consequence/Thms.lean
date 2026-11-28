module

public import Silmaril.Logic.ACL2.Consequence.Defs

@[expose] public section

namespace Silmaril.Logic.ACL2.Consequence

theorem presentationSound (P : Presentation) : presentationDerives P ≤ presentationEntails P :=
  fun _ _ h M hΓ => (piSound.ρ.app P).map_derives h M fun _ ⟨q, hq, eq⟩ => eq ▸ hΓ q hq

theorem exampleSound : exampleDerives ≤ exampleEntails :=
  presentationSound Examples.exampleWorld.presentation

end Silmaril.Logic.ACL2.Consequence
