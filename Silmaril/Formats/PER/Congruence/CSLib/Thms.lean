module

public import Silmaril.Formats.PER.Congruence.CSLib.Defs
import Silmaril.Proofs.Formats.PER.Congruence.CSLib

public section

namespace Silmaril.Formats.PER.Constructors

/-- Guarded closure induces a CSLib congruence on support for total single-hole frames. -/
theorem support_context_lawful {α : Type} (C : Constructors α) (R : PER α) (closed : C.Closed R) :
    @Cslib.LawfulCongruence _ R.supportSetoid.r ⟨⟩ (C.supportContexts R closed) :=
  Proofs.Formats.PER.Congruence.support_context_lawful C R closed

end Silmaril.Formats.PER.Constructors
