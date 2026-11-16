module

public import Silmaril.Wasm.Component.ExtSession.Thms
public import Silmaril.Games.AnsPull.Thms
public import Silmaril.Games.DivComp.Thms

/-!
# The component environment extension on sessions, all components (proofs)

`ext_eq`: `DStrategy.ext e` with the session answers relabelled by `toU` (above) and the node's
import answers by `ofU` (below) is `SessionExt.extS (splitR e)` relabelled by `toU`, for
divergence and infinite plays as well as finite plays. The steps, all on divergence-observing
strategies (`Silmaril.Games.AnsPull`):

* `ofU` below the pairing distributes over it (`DStrategy.ofHandler_ansH_comp_pair`) and
  copycat on `sigU` is `ofU` then `toU` (`DStrategy.ofHandler_ansH_comp_ansH`), so
  `id.pair (ofU ∘ M) = ofU ∘ (toU.pair M)`;
* `toU` then `ofU` cancels in the middle (`DStrategy.ofHandler_ansH_comp_ansH`);
* `toU.pair (N₀ ∘ toU)` is the pairing `id.pair N₀` relabelled side by side
  (`DStrategy.comp_ansH`, `DStrategy.mapAns_pair`);
* the side-by-side relabelling below `splitH e` is the routing handler below `toU`
  (`DStrategy.ofHandler_ansH_comp_ofHandler`, `sumMap_comp_splitH`,
  `DStrategy.ofHandler_comp_ansH`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.ExtSessionFull

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.SessionExt
  Silmaril.Wasm.Component

theorem ofOpt_toOpt (x : Payload ⊕ PUnit.{1}) : ofOpt (toOpt x) = x := by
  rcases x with b | ⟨⟩ <;> rfl

theorem toOpt_ofOpt (y : Option Payload) : toOpt (ofOpt y) = y := by
  cases y <;> rfl

/-- `toU` then `ofU` is copycat on `sigS`. -/
theorem toU_comp_ofU :
    (Games.DStrategy.ofHandler toU).comp (Games.DStrategy.ofHandler ofU) =
      Games.DStrategy.id sigS :=
  Games.DStrategy.ofHandler_ansH_comp_ansH (E := sigS) (k := fun _ => toOpt)
    (k' := fun _ => ofOpt) fun _ => ofOpt_toOpt

/-- `ofU` then `toU` is copycat on `sigU`. -/
theorem ofU_comp_toU :
    (Games.DStrategy.ofHandler ofU).comp (Games.DStrategy.ofHandler toU) =
      Games.DStrategy.id sigU :=
  Games.DStrategy.ofHandler_ansH_comp_ansH (E := sigU) (k := fun _ => ofOpt)
    (k' := fun _ => toOpt) fun _ => toOpt_ofOpt

/-- `ofU` below a pairing distributes over it. -/
theorem ofU_comp_pair {F₁ F₂ : Sig.{0}} (σ₁ : Games.DStrategy sigS F₁)
    (σ₂ : Games.DStrategy sigS F₂) :
    (Games.DStrategy.ofHandler ofU).comp (σ₁.pair σ₂) =
      ((Games.DStrategy.ofHandler ofU).comp σ₁).pair ((Games.DStrategy.ofHandler ofU).comp σ₂) :=
  Games.DStrategy.ofHandler_ansH_comp_pair (E := sigU) (k := fun _ => ofOpt) σ₁ σ₂

/-- The side-by-side relabelling of a paired session interface. -/
abbrev toUU : (a : (sigS ⊕ₛ sigS).Op) → (sigS ⊕ₛ sigS).Ar a → (sigU ⊕ₛ sigU).Ar a :=
  sumAns (F₁ := sigS) (F₂ := sigS) (B₁ := fun _ => Option Payload) (B₂ := fun _ => Option Payload)
    (fun _ => toOpt) (fun _ => toOpt)

/-- `toU` above both sides of a pairing is the side-by-side relabelling above it. -/
theorem pair_toU_ansH {X : Sig.{0}} (σ₁ σ₂ : Games.DStrategy X sigS) :
    (σ₁.comp (Games.DStrategy.ofHandler toU)).pair (σ₂.comp (Games.DStrategy.ofHandler toU)) =
      (σ₁.pair σ₂).comp (Games.DStrategy.ofHandler (ansH toUU)) := by
  have h₁ : σ₁.comp (Games.DStrategy.ofHandler toU) = σ₁.mapAns fun _ => toOpt :=
    Games.DStrategy.comp_ansH _ σ₁
  have h₂ : σ₂.comp (Games.DStrategy.ofHandler toU) = σ₂.mapAns fun _ => toOpt :=
    Games.DStrategy.comp_ansH _ σ₂
  rw [h₁, h₂]
  exact (Games.DStrategy.mapAns_pair (F₁ := sigS) (F₂ := sigS)
    (B₁ := fun _ => Option Payload) (B₂ := fun _ => Option Payload)
    (k₁ := fun _ => toOpt) (k₂ := fun _ => toOpt) (k₁' := fun _ => ofOpt) (k₂' := fun _ => ofOpt)
    (fun _ => ofOpt_toOpt) (fun _ => toOpt_ofOpt) (fun _ => ofOpt_toOpt) (fun _ => toOpt_ofOpt)
    σ₁ σ₂).trans (Games.DStrategy.comp_ansH toUU (σ₁.pair σ₂)).symm

theorem ansH_toUU : (ansH toUU : Handler (sigS ⊕ₛ sigS) (sigU ⊕ₛ sigU)) =
    Handler.sumMap toU toU := by
  funext a
  rcases a with q | q <;> rfl

/-- `toU` above both sides of a pairing is `toU` side by side above it. -/
theorem pair_toU {X : Sig.{0}} (σ₁ σ₂ : Games.DStrategy X sigS) :
    (σ₁.comp (Games.DStrategy.ofHandler toU)).pair (σ₂.comp (Games.DStrategy.ofHandler toU)) =
      (σ₁.pair σ₂).comp (Games.DStrategy.ofHandler (Handler.sumMap toU toU)) := by
  have key : ∀ h : Handler (sigS ⊕ₛ sigS) (sigU ⊕ₛ sigU), ansH toUU = h →
      (σ₁.comp (Games.DStrategy.ofHandler toU)).pair (σ₂.comp (Games.DStrategy.ofHandler toU)) =
        (σ₁.pair σ₂).comp (Games.DStrategy.ofHandler h) := by
    rintro h rfl
    exact pair_toU_ansH σ₁ σ₂
  exact key _ ansH_toUU

/-- The side-by-side relabelling below `splitH e` is the routing handler below `toU`. -/
theorem sumMap_toU_comp_splitH (e : Nat) :
    (Games.DStrategy.ofHandler (Handler.sumMap toU toU)).comp
        (Games.DStrategy.ofHandler (splitH e)) =
      (Games.DStrategy.ofHandler (routeH (splitR e))).comp (Games.DStrategy.ofHandler toU) := by
  have key : ∀ h : Handler (sigS ⊕ₛ sigS) (sigU ⊕ₛ sigU), ansH toUU = h →
      (Games.DStrategy.ofHandler h).comp (Games.DStrategy.ofHandler (splitH e)) =
        Games.DStrategy.ofHandler (h.comp (splitH e)) := by
    rintro h rfl
    exact Games.DStrategy.ofHandler_ansH_comp_ofHandler (E := sigS ⊕ₛ sigS)
      (B' := (sigU ⊕ₛ sigU).Ar) (k := toUU) (splitH e)
  have hu : (Games.DStrategy.ofHandler (routeH (splitR e))).comp
      (Games.DStrategy.ofHandler toU) =
        Games.DStrategy.ofHandler ((routeH (splitR e)).comp toU) :=
    Games.DStrategy.ofHandler_comp_ansH (k' := fun _ => ofOpt) (fun _ => ofOpt_toOpt)
      (fun _ => toOpt_ofOpt) (routeH (splitR e))
  rw [key _ ansH_toUU, hu, sumMap_comp_splitH]

/-- **`DStrategy.ext e` with relabelled answers is the relabelled `extS (splitR e)`.** -/
theorem ext_eq {X : Sig.{0}} (e : Nat) (D₀ : Games.DStrategy X sigS)
    (N₀ : Games.DStrategy sigS sigS) :
    Silmaril.Wasm.Component.DStrategy.ext e (D₀.comp (Games.DStrategy.ofHandler toU))
        ((Games.DStrategy.ofHandler ofU).comp (N₀.comp (Games.DStrategy.ofHandler toU))) =
      (extS (splitR e) D₀ N₀).comp (Games.DStrategy.ofHandler toU) := by
  have h₁ : (Games.DStrategy.id sigU).pair
      ((Games.DStrategy.ofHandler ofU).comp (N₀.comp (Games.DStrategy.ofHandler toU))) =
        (Games.DStrategy.ofHandler ofU).comp ((Games.DStrategy.ofHandler toU).pair
          (N₀.comp (Games.DStrategy.ofHandler toU))) := by
    rw [ofU_comp_pair, ofU_comp_toU]
  have h₂ : (Games.DStrategy.ofHandler toU).pair (N₀.comp (Games.DStrategy.ofHandler toU)) =
      ((Games.DStrategy.id sigS).pair N₀).comp
        (Games.DStrategy.ofHandler (Handler.sumMap toU toU)) := by
    rw [← pair_toU, Games.DStrategy.id_comp]
  show (D₀.comp (Games.DStrategy.ofHandler toU)).comp
      (((Games.DStrategy.id sigU).pair
        ((Games.DStrategy.ofHandler ofU).comp (N₀.comp (Games.DStrategy.ofHandler toU)))).comp
        (Games.DStrategy.ofHandler (splitH e))) =
    (D₀.comp (((Games.DStrategy.id sigS).pair N₀).comp
      (Games.DStrategy.ofHandler (routeH (splitR e))))).comp (Games.DStrategy.ofHandler toU)
  rw [h₁, h₂]
  simp only [Games.DStrategy.comp_assoc]
  rw [← Games.DStrategy.comp_assoc (Games.DStrategy.ofHandler toU), toU_comp_ofU,
    Games.DStrategy.id_comp, sumMap_toU_comp_splitH]

end Silmaril.Proofs.Wasm.Component.ExtSessionFull
