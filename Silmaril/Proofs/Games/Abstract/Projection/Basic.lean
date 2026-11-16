module

public import Silmaril.Games.Abstract.Projection.Defs
public import Silmaril.Games.Abstract.Module.Thms

/-!
# Projections: proofs

Closing preserves trap ≈ divergence equivalence of open modules but does not
reflect it: a self-recursive function and an empty one close alike.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.Projection

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.Shape Silmaril.Games.Abstract.AFun

universe u

theorem close_preserves (sh : Shape.{u}) :
    PreservesMod (X := OpenModule sh) (fun m m' => OpenCollapseEquiv m.mod m'.mod) :=
  fun _ _ h => close_congr h

/-- One function, unit everything, no imports. -/
abbrev shU : Shape.{0} := ⟨Sig.empty, PUnit, PUnit, fun _ => PUnit, fun _ => PUnit⟩

/-- The recursive call. -/
def callSelf : Call (shU.E ⊕ₛ shU.self) := ⟨.inr ⟨⟨⟩, (⟨⟩, ⟨⟩)⟩, (⟨⟩, ⟨⟩)⟩

/-- `f () = f ()`. -/
def recM : shU.OpenMod := fun _ _ _ => {([callSelf], .ret ⟨⟩ ⟨⟩)}

theorem close_recM : close recM = ⊥ := by
  refine le_antisymm (OrderHom.lfp_le _ ?_) bot_le
  rintro f s a y ⟨x, hx, hs⟩
  obtain rfl : x = ([callSelf], .ret ⟨⟩ ⟨⟩) := hx
  cases hs with
  | int hc _ => exact hc
  | intTrap hc => exact hc
  | intDiv hc => exact hc

theorem close_not_reflects :
    ¬ ReflectsMod (X := OpenModule shU) (fun m m' => OpenCollapseEquiv m.mod m'.mod) := by
  intro h
  have he : ClosedCollapseEquiv (close recM) (close (lift ⊥)) := by
    rw [close_recM, close_lift]
    exact fun _ _ _ => rfl
  have := h (OpenModule.mk recM) (OpenModule.mk (lift ⊥)) he (⟨⟩ : PUnit) (⟨⟩ : PUnit)
    (⟨⟩ : PUnit)
  have hm : obsCollapse (([callSelf], .ret ⟨⟩ ⟨⟩) : CallBeh (shU.E ⊕ₛ shU.self) PUnit PUnit) ∈
      obsCollapse '' lift (⊥ : shU.ClosedMod) (⟨⟩ : PUnit) (⟨⟩ : PUnit) (⟨⟩ : PUnit) :=
    this ▸ ⟨_, rfl, rfl⟩
  obtain ⟨_, ⟨w, hw, rfl⟩, -⟩ := hm
  exact hw

end Silmaril.Proofs.Games.Abstract.Projection
