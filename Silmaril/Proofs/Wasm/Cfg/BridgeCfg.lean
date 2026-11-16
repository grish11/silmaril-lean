module

public import Silmaril.Wasm.Cfg.BridgeBwd.Thms
public import Silmaril.Wasm.Cfg.Bridge.Thms
public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Proofs.Wasm.Cfg.Bridge

@[expose] public section

/-!
# The block-CFG machine against native trees (proofs)

`machine_native`: a run of the machine with oracle `C` from the CFG entry of the lowering of typed
trees without tail calls to a sink is a native run with the same oracle (`run_sound_initialC`,
then `bridge_bwd_tailFree`). `native_machine`: a typed checked native run is a machine run from the CFG
entry to a sink, unless the region ends in a branch out of the body (`bridge_fwd`, then
`run_complete_initialC`, or `run_complete_tail_initialC` for a pending tail call, whose oracle
answer `ResOut` provides).
-/

namespace Silmaril.Wasm.Cfg.Proofs.BridgeCfg

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Cfg.Bridge
  Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Binaryen

variable {H : Type} {C : Abstract.CallRel H}

theorem machine_native {o : SingleThreaded.GrowOracle} {P₀ : Profile}
    (hC : Interp.OracleSoundT P₀ Interp.noHostX C) (hCk : Abstract.CallXT.KeepsTy C)
    {s : Store H} {f : Frame} {es : List BExpr} {st' : MState H}
    (ht : Interp.TypedT s f [] es) (hx : tailFreeL es = true)
    (h : Relation.ReflTransGen (MStepC (SingleThreaded.profile o) Interp.noHostX C
      (BExpr.lowerList es)) (initial (BExpr.lowerList es) s f) st')
    (hs : st'.node.IsSink) :
    ∃ out s₂ f₂ r, EndsC C st' s₂ f₂ out ∧ Abstract.CallX.EvalOX C s f [] es r ∧
      ResOut C s₂ f₂ out r := by
  obtain ⟨out, s₂, f₂, hE, hR⟩ := run_sound_initialC h hs
  obtain ⟨r, hr, hres⟩ := bridge_bwd_tailFree hC hCk ht hx hR
  exact ⟨out, s₂, f₂, r, hE, hr, hres⟩

theorem native_machine {P₀ : Profile} {host₀ : HostSemantics H}
    (hC : Interp.OracleSoundT P₀ host₀ C) (P : Profile) (host : HostSemantics H)
    {s : Store H} {f : Frame} {es : List BExpr} {r : Store H × Frame × Flow}
    (h : Abstract.CallXT.EvalOXT C s f [] es r) {labels : List Nat} {ret : Nat}
    {out : Option Nat} (hS : Interp.StoreChkE Interp.tExt s.funcs)
    (hchk : Interp.chkE Interp.tExt s.funcs f.module f.locals.length ret labels (some 0) es =
      some out) :
    ∃ s' f' o, ResOut C s' f' o r ∧
      ((∃ k us, o = .br k us) ∨
        ∃ st', Relation.ReflTransGen (MStepC P host C (BExpr.lowerList es))
          (initial (BExpr.lowerList es) s f) st' ∧ EndsC C st' s' f' o) := by
  obtain ⟨s', f', o, hR, hres⟩ := bridge_fwd (P := P) (host := host) hC h hS hchk
  refine ⟨s', f', o, hres, ?_⟩
  by_cases hb : ∃ k us, o = .br k us
  · exact .inl hb
  right
  simp only [not_exists] at hb
  cases o with
  | tail W a c =>
    obtain ⟨fi, ps, rs, W₀, args, fl, hfi, hty, hW, hn, hcall, hfl, -, -⟩ := hres
    obtain ⟨st', hst'⟩ : ∃ st', tailEnd rs.length r.1 f' fl = some st' := by
      rcases hfl with ⟨vs, hvs⟩ | habr
      · cases fl <;> simp_all [tailEnd, Flow.retVals]
      · cases fl <;> simp_all [tailEnd, Flow.Abrupt]
    exact ⟨st', run_complete_tail_initialC hR hfi hty hW hn hcall hst',
      fi, ps, rs, W₀, args, fl, r.1, hfi, hty, hW, hn, hcall, hst'⟩
  | br k us => exact absurd rfl (hb k us)
  | _ =>
    obtain ⟨st', hrun, hE, hs, hf⟩ := run_complete_initialC hR (by simp) (by simp)
    exact ⟨st', hrun, hE, hs, hf⟩

theorem machine_native_closedX {o : SingleThreaded.GrowOracle} {s : Store H} {f : Frame}
    {es : List BExpr} {st' : MState H}
    (ht : Interp.TypedT s f [] es) (hx : tailFreeL es = true)
    (h : Relation.ReflTransGen (MStepC (SingleThreaded.profile o) Interp.noHostX closedXOk
      (BExpr.lowerList es)) (initial (BExpr.lowerList es) s f) st')
    (hs : st'.node.IsSink) :
    ∃ out s₂ f₂ r, EndsC closedXOk st' s₂ f₂ out ∧ Abstract.CallX.EvalOX closedXOk s f [] es r ∧
      ResOut closedXOk s₂ f₂ out r :=
  machine_native (Proofs.Bridge.oracleSoundT_closedXOk (SingleThreaded.profile o))
    Proofs.Bridge.keepsTy_closedXOk ht hx h hs

theorem native_machine_closedX (P : Profile) {s : Store H} {f : Frame} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : Abstract.CallX.EvalOX closedXOk s f [] es r)
    (ht : Interp.TypedT s f [] es) :
    ∃ s' f' o, ResOut closedXOk s' f' o r ∧
      ((∃ k us, o = .br k us) ∨
        ∃ st', Relation.ReflTransGen (MStepC P Interp.noHostX closedXOk (BExpr.lowerList es))
          (initial (BExpr.lowerList es) s f) st' ∧ EndsC closedXOk st' s' f' o) := by
  obtain ⟨_, labels, ret, out, hS, hchk, -⟩ := id ht
  exact native_machine (Proofs.Bridge.oracleSoundT_closedXOk P) P Interp.noHostX
    (Interp.OracleX.evalOXT_of_typedT (Proofs.Bridge.oracleSoundT_closedXOk P)
      Proofs.Bridge.keepsTy_closedXOk h ht) hS hchk

end Silmaril.Wasm.Cfg.Proofs.BridgeCfg
