module

public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Event
public import Silmaril.Proofs.Wasm.Cfg.CfgInst

@[expose] public section

/-!
# The relaxed invariant along labelled runs (proofs)

`HostTypedD host`: every answer keeps the store and has values of the callee's result types; a
thrown address is unconstrained. This is `HostTyped` without its exception clause, restricted to
store-keeping hosts. `ConfigOkD.evRun`: labelled Core runs against such a host keep `ConfigOkD`.
Every restricted universal host of an instance, `CfgInst.instHostU I` included, is such a host
(`hostTypedD_instHostQ`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Games.Abstract (Call)
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- **A store-keeping host whose values are typed**, any exception address allowed. -/
def HostTypedD (host : HostSemantics H) : Prop :=
  ∀ (hh : H) (s : Store H) (us : List Val) (s' : Store H) (r : Result),
    host hh s us (.returned s' r) → s' = s ∧ ∀ fi ∈ s.funcs, fi.code = .host hh →
      ∀ ps rs, Expand fi.type (.func ps rs) → ResultTypedD s r rs.toList

/-- **Labelled runs keep the relaxed invariant.** -/
theorem ConfigOkD.evRun {host : HostSemantics H} (hT : HostTypedD host) {c c' : Config H}
    {cs : List (Call (Abstract.wasmHostSig H))} (hc : ConfigOkD c)
    (h : Abstract.EvRun P host c cs c') : ConfigOkD c' := by
  induction h with
  | refl => exact hc
  | silent hs _ ih =>
    rcases hs with hs | ⟨rfl, -⟩
    · exact ih (hc.step hs)
    · exact ih hc
  | @event c₁ c₂ c₃ e cs hs _ ih =>
    obtain ⟨E, a, hdec, hst, hhost, hc₂⟩ := hs
    obtain ⟨hsp, hres⟩ := hT _ _ _ _ _ hhost
    refine ih (hc.event (P := P) (e := e) ⟨E, a, hdec, hst, hhost, hc₂⟩ (by rw [hsp, hst]) ?_)
    intro fi hfi hcode ps rs hexp
    exact hres fi hfi hcode ps rs hexp

section Inst

variable {I : Game.ScalarInstance}

/-- **Every restricted universal host of an instance keeps the relaxed invariant**, in particular
the unrestricted `instHostU I`. -/
theorem hostTypedD_instHostQ {Q : Store Nat → Result → Prop} :
    HostTypedD (CfgInst.instHostQ I Q) := by
  intro hh s us s' r h
  obtain ⟨rfl, hIT, -, e, he, v, rfl⟩ := Proofs.CfgInst.instHostQ_returned h
  refine ⟨rfl, fun fi hfi hcode ps rs hexp => ?_⟩
  have hrs := Proofs.CfgInst.results_of_importTyped hIT hfi hcode
    (Proofs.CfgInst.importOp?_fst he) hexp
  cases v with
  | values ws =>
    show List.Forall₂ (ValOk _) ws.1 rs.toList
    rw [hrs]
    exact Proofs.Session.forall₂_valOk_of_hasVal _ ws.2
  | trap => trivial
  | throw t => trivial

theorem hostTypedD_instHostU : HostTypedD (CfgInst.instHostU I) := hostTypedD_instHostQ

end Inst

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
