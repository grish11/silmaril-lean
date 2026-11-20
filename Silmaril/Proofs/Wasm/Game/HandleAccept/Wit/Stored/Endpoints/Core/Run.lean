module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core

theorem runLocal_steps {E : CoreEngine} {Value : Type} (program : P E Unit Value)
    (store updated : CStore E) (value : Value) (finish : Value → P E Unit (Ret E))
    (ready : HostReady Unit) (dispatch : Call E → P E Unit (Ret E))
    (success : runLocal program store = (updated, .ok value)) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps .deterministic ready dispatch
        { store, host := (), ctl := [.ofProg none (program >>= finish)] } labels
        { store := updated, host := (), ctl := [.ofProg none (finish value)] } := by
  induction program generalizing store with
  | pure result =>
    simp only [runLocal, Prod.mk.injEq, Except.ok.injEq] at success
    obtain ⟨rfl, rfl⟩ := success
    exact ⟨[], rfl, .refl _⟩
  | op op next ih =>
    cases op <;> simp only [runLocal] at success
    case get =>
      obtain ⟨labels, hTau, tail⟩ := ih store store success
      exact ⟨.tau :: labels, hTau, .cons (.get rfl) tail⟩
    case modify update =>
      obtain ⟨labels, hTau, tail⟩ := ih () (update store) success
      exact ⟨.tau :: labels, hTau, .cons (.modify rfl) tail⟩
    all_goals cases success

theorem runLocal_trap_steps {E : CoreEngine} {Value : Type} (program : P E Unit Value)
    (store updated : CStore E) (reason : TrapReason) (finish : Value → P E Unit (Ret E))
    (ready : HostReady Unit) (dispatch : Call E → P E Unit (Ret E))
    (failure : runLocal program store = (updated, .error (.trapped reason))) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps .deterministic ready dispatch
        { store, host := (), ctl := [.ofProg none (program >>= finish)] } (labels ++ [.trap reason])
        { store := Machine.StepDefs.lockdownSt updated, host := (), ctl := [] } := by
  induction program generalizing store with
  | pure result => cases failure
  | op op next ih =>
    cases op <;> simp only [runLocal] at failure
    case get =>
      obtain ⟨labels, hTau, tail⟩ := ih store store failure
      exact ⟨.tau :: labels, hTau, .cons (.get rfl) tail⟩
    case modify update =>
      obtain ⟨labels, hTau, tail⟩ := ih () (update store) failure
      exact ⟨.tau :: labels, hTau, .cons (.modify rfl) tail⟩
    case trap localReason =>
      cases failure
      exact ⟨[], rfl, .cons (.trap rfl) (.refl _)⟩
    all_goals cases failure

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core
