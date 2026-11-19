module

public import Silmaril.Wasm.Cfg.DanglingBack.Defs
public import Silmaril.Wasm.Cfg.DanglingExn.Thms
public import Silmaril.Wasm.Abstract.BackInv.Thms
public import Silmaril.Proofs.Wasm.Cfg.CfgInst

@[expose] public section

/-!
# The reverse inclusion for dangling host exceptions (proofs)

At a deterministic profile `profile o`, on a well-formed instance store whose functions are in
the checker's instruction profile, every Core behaviour of an export question against the
universal host `instHost I` (dangling host throws included) is a behaviour of the CFG instance
triple at the unrestricted host `instHostU I`, componentwise:

* the Core behaviour, pending call or productive stream at `instHost I` is one at `instHostU I`
  (`coreBehSXP_Q_iff`, `coreCallout_Q_iff`, `coreInf_Q_iff` at `Q = True`: the store's host
  functions are typed imports);
* it is a session behaviour (`BackInv.coreBehSXP_mem`, `coreCallout_mem`, `coreInf_mem`) for the
  relaxed instance `backD` (`ConfigOkD` against `HostTypedD`): the question enters `ConfigOkD`
  (`configOkD_of_supported`), `instHostU I` is `HostTypedD` and in the host slices;
* its log is allowed by `instHostU I` (`evRun_consistent`, `coreInf_consistent`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingBack

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Cfg.CfgInst Silmaril.Wasm.Cfg.DanglingExn Silmaril.Wasm.Cfg.DanglingBack
open Silmaril.Wasm.Abstract (wasmHostSig coreHostRel CoreBehSXP)
open Silmaril.Wasm.Abstract.NodeBridge (instHost qOf viewTriple CoreCallout)
open Silmaril.Wasm.Abstract.InstSession (instTripleS)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

theorem coreBehSXP_consistent {s : Store H} {q : Nat × List Val}
    {y : CallBeh (wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit)}
    (hy : CoreBehSXP P host s q y) : (coreHostRel host).Consistent y.1 := by
  obtain ⟨cs, e⟩ := y
  rcases e with ⟨(ws | t) | u, s₂⟩ | _ | _
  · exact Abstract.evRun_consistent hy
  · exact Abstract.evRun_consistent hy
  · exact Abstract.evRun_consistent hy
  · exact hy.elim
  · obtain ⟨c', hrun, -⟩ := hy
    exact Abstract.evRun_consistent hrun

variable {I : ScalarInstance} {o : GrowOracle}

/-- **Every instance behaviour is a CFG behaviour at the unrestricted host**, on well-formed
stores in the checker's profile, at a deterministic profile. -/
theorem instTripleS_sub_cfgInstTripleU {s : Store Nat} (hw : I.WellFormed s)
    (hsup : Interp.CheckComplete.StoreSupported s.funcs) (a : I.F.Op) :
    (instTripleS I (profile o)).1 s a ⊆ (cfgInstTripleU I).1 s a ∧
      (instTripleS I (profile o)).2.1 s a ⊆ (cfgInstTripleU I).2.1 s a ∧
      (instTripleS I (profile o)).2.2 s a ⊆ (cfgInstTripleU I).2.2 s a := by
  have hd := instDom_of_supported hw hsup
  obtain ⟨-, hS, hts, hok⟩ := Proofs.CfgInst.invOkXP_of_dom hd a
  have hct := DanglingTyped.configOkD_of_supported hw hsup a
  have hI := Proofs.CfgInst.importsTyped_of_wf hw
  have hT : (backD (H := Nat)).HostOk (instHostU I) := DanglingTyped.hostTypedD_instHostU
  have hH : Interp.HostSliceT (instHostU I) := Proofs.CfgInst.hostSliceT_instHostQ
  have hE : Interp.HostSliceE s.tags (instHostU I) := Proofs.CfgInst.hostSliceE_instHostQ _
  rw [Abstract.NodeBridge.instTripleS_eq_viewTriple]
  unfold cfgInstTripleU
  rw [CfgClosure.cfgSessionTripleC_eq]
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨y, ⟨-, hy⟩, hv⟩
    have hyU : CoreBehSXP (profile o) (instHostU I) s (qOf I a) y :=
      (Proofs.CfgInst.coreBehSXP_Q_iff (Q := fun _ _ => True) hI).2 ⟨hy, fun _ _ => trivial⟩
    exact ⟨y, ⟨backD.coreBehSXP_mem hT hH hE hct hS hts hok hyU, coreBehSXP_consistent hyU⟩, hv⟩
  · rintro x ⟨y, hy, hv⟩
    have hyU : CoreCallout (profile o) (instHostU I) s (qOf I a) y :=
      (Proofs.CfgInst.coreCallout_Q_iff (Q := fun _ _ => True) hI).2 ⟨hy, fun _ _ => trivial⟩
    obtain ⟨c, E, a', hrun, -, -⟩ := id hyU
    exact ⟨y, ⟨backD.coreCallout_mem hT hH hE hct hS hts hok hyU,
      Abstract.evRun_consistent hrun⟩, hv⟩
  · rintro ω ⟨ω', ⟨-, hω⟩, hv⟩
    have hωU : Abstract.CoreInf (profile o) (instHostU I) (invoke s (qOf I a).1 (qOf I a).2) ω' :=
      (Proofs.CfgInst.coreInf_Q_iff (Q := fun _ _ => True) hI).2 ⟨hω, fun _ => trivial⟩
    exact ⟨ω', ⟨backD.coreInf_mem hT hH hE hct hS hts hok hωU,
      fun n => Abstract.coreInf_consistent hωU n⟩, hv⟩

/-- **Per question, the instance triple is the CFG instance triple at the unrestricted host**,
on well-formed stores in the checker's profile, at a deterministic profile. -/
theorem instTripleS_agree_cfgInstTripleU {s : Store Nat} (hw : I.WellFormed s)
    (hsup : Interp.CheckComplete.StoreSupported s.funcs) (a : I.F.Op) :
    AgreeAt (instTripleS I (profile o)) (cfgInstTripleU I) s a := by
  obtain ⟨b₁, b₂, b₃⟩ := instTripleS_sub_cfgInstTripleU (o := o) hw hsup a
  obtain ⟨f₁, f₂, f₃⟩ := cfgInstTripleU_sub (P := profile o) (instDom_of_supported hw hsup) a
  exact ⟨Set.Subset.antisymm b₁ f₁, Set.Subset.antisymm b₂ f₂, Set.Subset.antisymm b₃ f₃⟩

end Silmaril.Wasm.Cfg.Proofs.DanglingBack
