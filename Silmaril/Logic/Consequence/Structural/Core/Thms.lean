module

public import Silmaril.Logic.Consequence.Defs
public import Silmaril.Logic.Consequence.Structural.Witness.Thms
public import Silmaril.Logic.Consequence.Refutation.Thms

/-!
# Structural closures over the core consequence systems

A thin bridge to `Silmaril.Logic.Consequence.Defs`. It adds no new definitions:

* `Structural.Rel C` is `System (List C) C` (`rel_eq_system`, by `rfl`), so every structural
  closure is a closure of a core system.
* Weakening along a policy is core's monotonicity along that relation
  (`weakensAlong_iff_monoWrt`); the three policies stay distinct.
* `Derives rs S` is sound for a closed `T` iff `S` is (`sound_derives_iff`): this is the closure
  adjunction stated in core's `System.Sound`.
* Witness derivations erase to the closure of the erased witness system
  (`nonempty_wderives_iff`, over `WSystem.erase`, any witness universe `w`).
* Refutation: a sound checker gives a `System.Sound` relation, and so does its closure; a
  complete checker gives a `System.Complete` one. These use the same exact hypotheses as
  `Silmaril.Logic.Consequence.Refutation.Thms`.
-/

@[expose] public section

namespace Silmaril.Consequence.Structural

universe u v w

variable {C : Type u}

theorem rel_eq_system : Rel C = System (List C) C := rfl

theorem weakensAlong_iff_monoWrt {W : List C → List C → Prop} {R : Rel C} :
    WeakensAlong W R ↔ System.MonoWrt W R :=
  ⟨fun h _ _ hw _ hd => h hw hd, fun h _ _ _ hw hd => h hw hd⟩

theorem weakSubset_iff_monoWrt {R : Rel C} :
    WeakSubset R ↔ System.MonoWrt (fun Γ Δ : List C => Γ ⊆ Δ) R :=
  weakensAlong_iff_monoWrt

/-- The closure adjunction, as core soundness: for a closed `T`, `Derives rs S` is sound for
`T` iff `S` is. -/
theorem sound_derives_iff {rs : Rules C} {S T : System (List C) C} (hT : Closed rs T) :
    System.Sound (Derives rs S) T ↔ System.Sound S T :=
  derives_le_iff hT

/-- Witness derivations exist iff the closure of the erased witness system derives the sequent. -/
theorem nonempty_wderives_iff {rs : Rules C} {W : WSystem.{u, u, w} (List C) C} {Γ : List C}
    {c : C} : Nonempty (WDerives rs W Γ c) ↔ Derives rs W.erase Γ c :=
  WDerives.nonempty_iff

end Silmaril.Consequence.Structural

namespace Silmaril.Consequence.Refutation

open Structural

universe u v

variable {M : Type v} {C : Type u} {sat : M → C → Prop} {neg : C → List C}
  {check : List C → Prop}

theorem sound_viaUnsat (hs : CheckSound sat check) (hn : NegComplete sat neg) :
    System.Sound (viaUnsat check neg) (Entails sat) :=
  viaUnsat_le_entails hs hn

theorem sound_derives_viaUnsat (hs : CheckSound sat check) (hn : NegComplete sat neg) :
    System.Sound (Derives tarskiRules (viaUnsat check neg)) (Entails sat) :=
  derives_viaUnsat_le_entails hs hn

theorem complete_viaUnsat (hc : CheckComplete sat check) (hn : NegSound sat neg) :
    System.Complete (viaUnsat check neg) (Entails sat) :=
  entails_le_viaUnsat hc hn

end Silmaril.Consequence.Refutation
