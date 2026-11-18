module

public import Silmaril.Wasm.Cfg.DanglingExn.Defs
public import Silmaril.Proofs.Wasm.Cfg.CfgInst

@[expose] public section

/-!
# Dangling exception addresses: the forward direction (proofs)

The forward (native to Core) theorems of the bridge need no typed host answers: a host in the
typed host slice `HostSliceT` whose answers keep the checker's invariants (`HostSliceE`) is
enough, and the unrestricted universal host `instHostU I` is such a host. Componentwise from
`wasmEvFunXPS_vals_evRun`, `wasmEvFunXPS_throw_evRun`, `wasmEvFunXPS_trap_evRun`,
`wasmEvFunDXP_div_evRun`, `wasmEvPendXP_evRun` and `hostObsInf_wasmEvInfNXP_coreInf`; then through
the view, with `coreBehSXP_Q_iff`/`coreCallout_Q_iff`/`coreInf_Q_iff` at `Q = True`.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingExn

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Cfg.CfgInst Silmaril.Wasm.Cfg.DanglingExn
open Silmaril.Wasm.Abstract (wasmHostSig coreHostRel CoreBehSXP InvOkXP sessionTripleXP)
open Silmaril.Wasm.Abstract.NodeBridge (instHost qOf viewTriple CoreCallout coreTripleSO)
open Silmaril.Wasm.Abstract.InstSession (instTripleS)
open Silmaril.Wasm.Interp (HostSliceT HostSliceE)
open Silmaril.Games.Abstract.StratSession (eraseEnd)

section Session

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H} {tags : List TagInst}
  {s : Store H} {q : Nat × List Val}

theorem fin_sub (hH : HostSliceT host) (hE : HostSliceE tags host) (hok : InvOkXP tags s q)
    {x : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit)}
    (hx : x ∈ (openRestrict (coreHostRel host) sessionTripleXP).1 s q) :
    x ∈ (coreTripleSO P host).1 s q := by
  obtain ⟨_, hS, hts, hinv⟩ := hok
  obtain ⟨hx, hc⟩ := hx
  obtain ⟨a, vs⟩ := q
  refine ⟨trivial, ?_⟩
  obtain ⟨cs, e⟩ := x
  rcases hx with hx | ⟨he, hx⟩
  · rcases e with ⟨(ws | t) | u, s₂⟩ | _ | _
    · exact Abstract.wasmEvFunXPS_vals_evRun hH hE hts hS hinv hx hc
    · exact Abstract.wasmEvFunXPS_throw_evRun hH hE hts hS hinv hx hc
    · exact Abstract.wasmEvFunXPS_trap_evRun hH hE hts hS hinv hx hc
    · exact absurd hx Abstract.wasmEvFunXPS_ne_trap
    · exact absurd (Abstract.wasmEvFunXPS_erase_le hx) Abstract.wasmEvFunXP_ne_div
  · dsimp only at he
    subst he
    exact Abstract.wasmEvFunDXP_div_evRun hH hE hts hS hinv hx hc

theorem pend_sub (hH : HostSliceT host) (hE : HostSliceE tags host) (hok : InvOkXP tags s q)
    {x : List (Call (wasmHostSig H)) × (wasmHostSig H).Op}
    (hx : x ∈ (openRestrict (coreHostRel host) sessionTripleXP).2.1 s q) :
    x ∈ (coreTripleSO P host).2.1 s q := by
  obtain ⟨_, hS, hts, hinv⟩ := hok
  obtain ⟨hx, hc⟩ := hx
  obtain ⟨a, vs⟩ := q
  obtain ⟨cs, m⟩ := x
  have hx' : (cs, m) ∈ Abstract.wasmEvPendXP s (a, vs) := by
    rw [← Abstract.wasmEvPendXPS_eq]; exact hx
  exact Abstract.wasmEvPendXP_evRun hH hE hts hS hinv hx' hc

theorem inf_sub (hH : HostSliceT host) (hE : HostSliceE tags host) (hok : InvOkXP tags s q)
    {ω : Nat → Call (wasmHostSig H)}
    (hx : ω ∈ (openRestrict (coreHostRel host) sessionTripleXP).2.2 s q) :
    ω ∈ (coreTripleSO P host).2.2 s q := by
  obtain ⟨_, hS, hts, hinv⟩ := hok
  obtain ⟨a, vs⟩ := q
  exact ⟨trivial, Abstract.hostObsInf_wasmEvInfNXP_coreInf hH hE hts hS hinv hx⟩

end Session

section Inst

variable {I : ScalarInstance} {P : Numerics.Profile}

theorem hostSliceT_instHostU : HostSliceT (instHostU I) := Proofs.CfgInst.hostSliceT_instHostQ

theorem hostSliceE_instHostU (tags : List TagInst) : HostSliceE tags (instHostU I) :=
  Proofs.CfgInst.hostSliceE_instHostQ tags

/-- **Every CFG instance behaviour at the unrestricted host is an instance behaviour**, on the
domain: finished behaviours, pending calls and productive streams. -/
theorem cfgInstTripleU_sub {s : Store Nat} (hd : InstDom I s) (a : I.F.Op) :
    (cfgInstTripleU I).1 s a ⊆ (instTripleS I P).1 s a ∧
      (cfgInstTripleU I).2.1 s a ⊆ (instTripleS I P).2.1 s a ∧
      (cfgInstTripleU I).2.2 s a ⊆ (instTripleS I P).2.2 s a := by
  have hok := Proofs.CfgInst.invOkXP_of_dom hd a
  have hI := Proofs.CfgInst.importsTyped_of_wf hd.wf
  rw [Abstract.NodeBridge.instTripleS_eq_viewTriple]
  unfold cfgInstTripleU
  rw [CfgClosure.cfgSessionTripleC_eq]
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨y, hy, hv⟩
    have h := fin_sub (P := P) hostSliceT_instHostU (hostSliceE_instHostU _) hok hy
    exact ⟨y, ⟨trivial, ((Proofs.CfgInst.coreBehSXP_Q_iff (Q := fun _ _ => True) hI).1 h.2).1⟩,
      hv⟩
  · rintro x ⟨y, hy, hv⟩
    have h := pend_sub (P := P) hostSliceT_instHostU (hostSliceE_instHostU _) hok hy
    exact ⟨y, ((Proofs.CfgInst.coreCallout_Q_iff (Q := fun _ _ => True) hI).1 h).1, hv⟩
  · rintro ω ⟨ω', hω, hv⟩
    have h := inf_sub (P := P) hostSliceT_instHostU (hostSliceE_instHostU _) hok hω
    exact ⟨ω', ⟨trivial, ((Proofs.CfgInst.coreInf_Q_iff (Q := fun _ _ => True) hI).1 h.2).1⟩,
      hv⟩

end Inst

end Silmaril.Wasm.Cfg.Proofs.DanglingExn
