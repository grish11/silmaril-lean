module

public import Silmaril.Wasm.Component.Binary.Lower.SemI.Defs
public import Silmaril.Wasm.Component.Binary.Lower.Sem.Thms
public import Silmaril.Proofs.Wasm.Component.InstExport.Basic

/-! # Lowered core modules with their start functions: proofs

On start-free lowered modules `coreModSemI` is bounded by `coreModSem` ready at once
(`coreModSemI_le_toI`), agrees with it after instantiation (`coreModSemI_after_iff`), and its
export phase is `coreModSem` (`exportPhase_coreModSemI`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Binary.SemI

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Binary
open Silmaril.Proofs.Wasm.Component.InstEngine Silmaril.Proofs.Wasm.Component.InstExport
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (liftMove)

variable {P : Profile} {cm : CoreMod}

theorem coreModSem_eq {J : IInstance (core3P P)}
    (hJ : instOfI (core3P P) (coreModule cm) (CoreModule.imports cm) (CoreModule.exports cm) =
      some J) (hs : J.start = none) :
    (coreModSem P).sem cm = engineStrategy _ J.toE (CoreModule.imports cm)
      (CoreModule.exports cm) :=
  coreModSem_sem_of_inst P (instOf_of_instOfI hJ hs)

theorem coreModSemI_le_toI (h : StartFree P cm) :
    (coreModSemI P).sem cm ≤ (coreModSem P).toI.sem cm := by
  obtain ⟨J, hJ, hs⟩ := h
  show engineStrategyI _ _ _ _ ≤ withReady ((coreModSem P).sem cm)
  rw [coreModSem_eq hJ hs]
  exact engine_le_withReady hJ hs

theorem coreModSemI_after_iff (h : StartFree P cm)
    (cs : List (Σ _ : (sigN (CoreModule.imports cm).length).Op, Option Payload))
    (p : List (Move (sigN (CoreModule.imports cm).length) (sigN (CoreModule.exports cm).length))) :
    instPlay (F := sigN (CoreModule.exports cm).length) cs .ready ++ p.map liftMove ∈
        (coreModSemI P).sem cm ↔ cs = [] ∧ p ∈ (coreModSem P).sem cm := by
  obtain ⟨J, hJ, hs⟩ := h
  rw [coreModSem_eq hJ hs]
  exact engine_after_noStart_iff hJ hs cs p

theorem exportPhase_coreModSemI (h : StartFree P cm) :
    exportPhase ((coreModSemI P).sem cm) = (coreModSem P).sem cm := by
  obtain ⟨J, hJ, hs⟩ := h
  rw [coreModSem_eq hJ hs]
  exact exportPhase_engine_noStart hJ hs

theorem denX_coreModSemI_le {c : Comp CoreMod} (hc : c.AllCore (StartFree P)) :
    c.denX (coreModSemI P) ≤ c.denU (coreModSem P) :=
  denX_le_denU (fun _ h => coreModSemI_le_toI h) hc

end Silmaril.Proofs.Wasm.Component.Binary.SemI
