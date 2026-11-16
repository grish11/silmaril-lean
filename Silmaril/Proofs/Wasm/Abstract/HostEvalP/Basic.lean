module

public import Silmaril.Wasm.Abstract.HostEvalP.Defs
public import Silmaril.Wasm.Abstract.XRecursionP.Thms
public import Silmaril.Wasm.Binaryen.Behaviour

/-!
# The host oracle for the canonical relation (proofs)
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEvalP

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel hostAns)
open Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.XRecursionP
open Silmaril.Wasm.Abstract.HostEvalP

variable {H : Type}

theorem hostCallXP_fixpoint (host : HostSemantics H) :
    hostCallXP host = bodyCallXP (hostCallXP host) ⊔ hostAns host :=
  ((hostCallXPOp host).map_lfp).symm

theorem hostCallXP_mono_host {host host' : HostSemantics H}
    (h : ∀ hh s vs o, host hh s vs o → host' hh s vs o) : hostCallXP host ≤ hostCallXP host' := by
  refine OrderHom.lfp_le _ ?_
  rintro s a args out (hb | ⟨fi, hh, r, hfi, hcode, hhost, hfl⟩)
  · rw [hostCallXP_fixpoint host']
    exact .inl hb
  · rw [hostCallXP_fixpoint host']
    exact .inr ⟨fi, hh, r, hfi, hcode, h _ _ _ _ hhost, hfl⟩

theorem hostAns_closedHost : hostAns (Binaryen.closedHost : HostSemantics H) = ⊥ := by
  funext s a args out
  apply propext
  constructor
  · rintro ⟨_, _, _, _, _, h, _⟩
    exact h.elim
  · intro h
    exact h.elim

theorem hostCallXP_closedHost :
    hostCallXP (Binaryen.closedHost : HostSemantics H) = closedCallXP := by
  apply le_antisymm
  · refine OrderHom.lfp_le _ ?_
    rintro s a args out (h | h)
    · rw [closedCallXP_fixpoint]
      exact h
    · rw [hostAns_closedHost] at h
      exact h.elim
  · refine OrderHom.lfp_le _ ?_
    intro s a args out h
    rw [hostCallXP_fixpoint]
    exact .inl h

end Silmaril.Proofs.Wasm.Abstract.HostEvalP
