module

public import Silmaril.Wasi.Component.Accept.Strict.Thms
public import Silmaril.Wasm.Abstract.Accept.Thms
public import Silmaril.Games.Abstract.SigBridge.Thms

/-! # Components: concrete → abstract → acceptor = concrete → acceptor

A component (`Strategy (nsig I) (nsig X)`) is an abstract trace model of the game
`sigGame (nsig I) (nsig X)` through the order isomorphism `SigBridge.strategyIso`. Every
acceptance reading of `Silmaril.Wasi.Component.Accept` is the abstract reading of
`Silmaril.Wasm.Abstract.Accept` on that trace model, through the event view `wev`. The equalities
are exact, so both directions hold:

* import and export acceptance, rejection and never-rejection (`importAccepted_eq_tm`,
  `exportAccepted_eq_tm`, `exportRejected_eq_tm`, `neverFalse_eq_tm`, `neverCalled_eq_tm`);
* the combined verdicts, with one runner (`exportAcceptedNotRejected_eq_tm`,
  `importAcceptedNotRejected_eq_tm`): the concrete runner on events is the image of the
  abstract runner on moves;
* IR components through `Layout.compModel` (`compModel_importAccepted_eq_tm`).

Order and equivalence transport through the isomorphism: `σ ≤ τ` iff
`strategyIso σ ≤ strategyIso τ`, so refinement monotonicity (one-sided verdicts) and equal-model
invariance carry over. The combined verdict is not monotone on either side.
-/

@[expose] public section

namespace Silmaril.Wasi.Accept

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Abstract.Accept
open Silmaril.Wasm.Component (Val Comp CoreModule)

variable {I X : Set FnName} {α : Type} {f acc rej : FnName} {dec : List Val → Option α}

theorem importAccepted_eq_tm (σ : Strategy (nsig I) (nsig X)) :
    importAccepted σ f dec = tmAccepted (SigBridge.strategyIso σ) (importObs f dec ∘ wev) :=
  importAccepted_eq σ

theorem exportAccepted_eq_tm (σ : Strategy (nsig I) (nsig X)) :
    exportAccepted σ f dec = tmAccepted (SigBridge.strategyIso σ) (exportObs f dec ∘ wev) :=
  exportAccepted_eq σ

theorem exportRejected_eq_tm (σ : Strategy (nsig I) (nsig X)) :
    exportRejected σ f dec = tmAccepted (SigBridge.strategyIso σ) (exportFalseObs f dec ∘ wev) :=
  exportRejected_eq σ

theorem neverFalse_eq_tm (σ : Strategy (nsig I) (nsig X)) :
    neverFalse σ f dec = (tmAccepted (SigBridge.strategyIso σ) (exportFalseObs f dec ∘ wev))ᶜ := by
  rw [neverFalse, exportRejected_eq_tm]

theorem neverCalled_eq_tm (σ : Strategy (nsig I) (nsig X)) :
    neverCalled σ f dec = (tmAccepted (SigBridge.strategyIso σ) (importObs f dec ∘ wev))ᶜ := by
  rw [neverCalled, importRejected, importAccepted_eq_tm]

/-- The concrete event runner is the image of the abstract move runner. -/
theorem exportRun_eq_image (σ : Strategy (nsig I) (nsig X)) (a : α) :
    exportRun σ dec a = wev '' tmRun (SigBridge.strategyIso σ) (retValue dec ∘ wev) a := by
  ext e
  constructor
  · rintro ⟨⟨_, ⟨s, hs, rfl⟩, he⟩, hv⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 he
    exact ⟨m, ⟨⟨s, hs, hm⟩, hv⟩, rfl⟩
  · rintro ⟨m, ⟨⟨s, hs, hm⟩, hv⟩, rfl⟩
    exact ⟨⟨_, ⟨s, hs, rfl⟩, List.mem_map.2 ⟨m, hm, rfl⟩⟩, hv⟩

theorem importRun_eq_image (σ : Strategy (nsig I) (nsig X)) (a : α) :
    importRun σ dec a = wev '' tmRun (SigBridge.strategyIso σ) (reqValue dec ∘ wev) a := by
  ext e
  constructor
  · rintro ⟨⟨_, ⟨s, hs, rfl⟩, he⟩, hv⟩
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 he
    exact ⟨m, ⟨⟨s, hs, hm⟩, hv⟩, rfl⟩
  · rintro ⟨m, ⟨⟨s, hs, hm⟩, hv⟩, rfl⟩
    exact ⟨⟨_, ⟨s, hs, rfl⟩, List.mem_map.2 ⟨m, hm, rfl⟩⟩, hv⟩

/-- **The exported combined verdict is the abstract combined verdict.** -/
theorem exportAcceptedNotRejected_eq_tm (σ : Strategy (nsig I) (nsig X)) :
    exportAcceptedNotRejected σ acc rej dec =
      tmAcceptsSafely (SigBridge.strategyIso σ) (retValue dec ∘ wev)
        (wev ⁻¹' retWith acc true) (wev ⁻¹' retWith rej false) := by
  rw [exportAcceptedNotRejected_eq_acceptsSafely]
  exact (acceptsSafely_congr (exportRun_eq_image σ) _ _).trans (acceptsSafely_image _ _ _ _)

/-- **The imported combined verdict is the abstract combined verdict.** -/
theorem importAcceptedNotRejected_eq_tm (σ : Strategy (nsig I) (nsig X)) :
    importAcceptedNotRejected σ acc rej dec =
      tmAcceptsSafely (SigBridge.strategyIso σ) (reqValue dec ∘ wev)
        (wev ⁻¹' reqOf acc) (wev ⁻¹' reqOf rej) := by
  rw [importAcceptedNotRejected_eq_acceptsSafely]
  exact (acceptsSafely_congr (importRun_eq_image σ) _ _).trans (acceptsSafely_image _ _ _ _)

/-- IR components, through their WASI model. -/
theorem compModel_importAccepted_eq_tm {M : Type} [CoreModule M]
    (C : Silmaril.Wasm.Component.CoreSem M) (L : Layout) (c : Comp M) :
    importAccepted (L.compModel C c) f dec =
      tmAccepted (SigBridge.strategyIso (L.compModel C c)) (importObs f dec ∘ wev) :=
  importAccepted_eq_tm _

/-- Refinement transports through the isomorphism. -/
theorem strategyIso_le_iff {σ τ : Strategy (nsig I) (nsig X)} :
    SigBridge.strategyIso σ ≤ SigBridge.strategyIso τ ↔ σ ≤ τ :=
  SigBridge.strategyIso.le_iff_le

end Silmaril.Wasi.Accept
