module

public import Silmaril.Semantics.Domain.Kleene

public section

namespace Silmaril.Proofs.Semantics.Domain

open Silmaril.Semantics.Domain OmegaCompletePartialOrder

theorem fix_fusion {D E : Type*} [OmegaCompletePartialOrder D] [OrderBot D]
    [OmegaCompletePartialOrder E] [OrderBot E] (f : D →𝒄 D) (g : E →𝒄 E) (h : D →𝒄 E)
    (strict : Strict h) (comm : ∀ x, h (f x) = g (h x)) :
    h (fix f) = fix g := by
  unfold fix
  rw [h.continuous]
  congr 1
  ext n
  change h (kleeneChain (f : D →o D) n) = kleeneChain (g : E →o E) n
  induction n with
  | zero => exact strict
  | succ n ih =>
    rw [kleeneChain_succ, kleeneChain_succ]
    change h (f _) = g _
    rw [comm, ih]

end Silmaril.Proofs.Semantics.Domain
