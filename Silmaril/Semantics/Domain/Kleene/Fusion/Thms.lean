module

public import Silmaril.Semantics.Domain.Kleene
import Silmaril.Proofs.Semantics.Domain.Kleene.Fusion

/-! # Preservation of least fixed points -/

public section

namespace Silmaril.Semantics.Domain

/-- A strict continuous map intertwining the unfoldings transports their least fixed points. -/
theorem fix_fusion {D E : Type*} [OmegaCompletePartialOrder D] [OrderBot D]
    [OmegaCompletePartialOrder E] [OrderBot E] (f : D →𝒄 D) (g : E →𝒄 E) (h : D →𝒄 E)
    (strict : Strict h) (comm : ∀ x, h (f x) = g (h x)) :
    h (fix f) = fix g :=
  Proofs.Semantics.Domain.fix_fusion f g h strict comm

end Silmaril.Semantics.Domain
