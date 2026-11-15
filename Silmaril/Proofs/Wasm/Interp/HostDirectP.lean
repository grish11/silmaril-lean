module

public import Silmaril.Proofs.Wasm.Interp.PendClose
public import Silmaril.Wasm.Abstract.HostEvalP.Thms
public import Silmaril.Wasm.Abstract.XRecursion.Thms
public import Silmaril.Wasm.Abstract.CallXE.Thms

/-!
# The host oracle for the canonical relation on direct, exception-free code (proofs)

On stores whose Wasm functions have neither the extended call forms nor the exception forms
(`StoreDirect`), and for hosts keeping that (`HostKeepsDirect`), the canonical host oracle
`HostEvalP.hostCallXP host` is the native one `HostEval.hostCall host` (`hostCallXP_iff_hostCall`),
and on such code the canonical runs against it are the native runs with host calls
(`evalOXP_host_iff_evalH`). Both directions are least-fixpoint inductions, keeping `StoreDirect`
along the runs (`EvalOXP.restrictI`), and translating runs by `CallXP.evalOXP_iff_evalOXE`,
`CallXE.evalOXE_iff_evalOX` and `CallX.evalOX_iff_evalO`.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel EvalO EvalH hostAns hostCall hostCallOp bodyCall)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXE Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.HostEvalP

variable {H : Type} {host : HostSemantics H}

/-- **Direct, exception-free stores**: every Wasm function's body has no extended call form
(`xFreeL`) and no `throw`, `throw_ref` or `try_table` (`ehFreeL`). -/
def StoreDirect (s : Store H) : Prop :=
  ∀ (a : Nat) (fi : FuncInst H) (fn : Func), s.funcs[a]? = some fi → fi.code = .wasm fn →
    xFreeL (liftInstrs fn.body) = true ∧ ehFreeL (liftInstrs fn.body) = true

/-- **Hosts keeping stores direct**: what a host appends is direct, exception-free code. -/
def HostKeepsDirect (host : HostSemantics H) : Prop :=
  ∀ h s vs s' r, host h s vs (.returned s' r) → StoreDirect s → StoreDirect s'

theorem storeDirect_of_funcs {s s' : Store H} (h : s'.funcs = s.funcs) (hs : StoreDirect s) :
    StoreDirect s' := fun a fi fn hfi hc => hs a fi fn (h ▸ hfi) hc

/-- On direct, exception-free code, the canonical flow runs are the native ones, any oracle. -/
theorem evalOXP_flow_iff_evalO {C : CallRel H} {s : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {s' : Store H} {f' : Frame} {fl : Flow} (hx : xFreeL es = true)
    (he : ehFreeL es = true) :
    EvalOXP C s f stk es (s', f', .flow fl) ↔ EvalO C s f stk es (s', f', fl) :=
  (evalOXP_iff_evalOXE hx).trans ((evalOXE_iff_evalOX he).trans (evalOX_iff_evalO hx))

/-- Restricting a canonical run to direct stores, for an oracle keeping them. -/
theorem EvalOXP.restrictDirect {C : CallRel H}
    (hC : ∀ s a us out, C s a us out → StoreDirect s → StoreDirect out.1) {s : Store H}
    {f : Frame} {stk : List Val} {es : List BExpr} {r : Store H × Frame × POut}
    (h : EvalOXP C s f stk es r) (hs : StoreDirect s) :
    StoreDirect r.1 ∧ EvalOXP (fun s a us out => StoreDirect s ∧ C s a us out) s f stk es r :=
  EvalOXP.restrictI (I := StoreDirect)
    (fun hf hi => storeDirect_of_funcs (Abstract.XRecursion.evalFlat_funcs hf) hi)
    (fun _ _ _ hi => hi) hC h hs

/-- On direct stores, the canonical host oracle answers as the native one, keeping them. -/
theorem hostCallXP_le_hostCall (hD : HostKeepsDirect host) :
    hostCallXP host ≤ fun s a args out => StoreDirect s → hostCall host s a args out ∧
      StoreDirect out.1 := by
  refine OrderHom.lfp_le _ ?_
  rintro s a args ⟨s', fl'⟩ (⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, d, hfr⟩ | hh) hs
  · obtain ⟨hs₁, d'⟩ := EvalOXP.restrictDirect (fun _ _ _ _ hq hs => (hq hs).2) d hs
    have hx := hs a fi fn hfi hcode
    cases hfr with
    | tail => exact absurd d (evalOXP_not_tail hx.1)
    | flow =>
      have d₂ := (evalOXP_flow_iff_evalO hx.1 hx.2).1
        (d'.mono fun _ _ _ _ h => (h.2 h.1).1)
      refine ⟨?_, hs₁⟩
      rw [show hostCall host = hostCallOp host (hostCall host) from (OrderHom.map_lfp _).symm]
      exact .inl ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, d₂⟩
  · obtain ⟨fi, h, r, hfi, hcode, hhost, hfl⟩ := hh
    refine ⟨?_, hD _ _ _ _ _ hhost hs⟩
    rw [show hostCall host = hostCallOp host (hostCall host) from (OrderHom.map_lfp _).symm]
    exact .inr ⟨fi, h, r, hfi, hcode, hhost, hfl⟩

/-- On direct stores, the native host oracle answers as the canonical one, keeping them. -/
theorem hostCall_le_hostCallXP (hD : HostKeepsDirect host) :
    hostCall host ≤ fun s a args out => StoreDirect s → hostCallXP host s a args out ∧
      StoreDirect out.1 := by
  refine OrderHom.lfp_le _ ?_
  rintro s a args out (⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, d⟩ | hh) hs
  · have hx := hs a fi fn hfi hcode
    obtain ⟨hs₁, d'⟩ := EvalOXP.restrictDirect (fun _ _ _ _ hq hs => (hq hs).2)
      ((evalOXP_flow_iff_evalO hx.1 hx.2).2 d) hs
    refine ⟨?_, hs₁⟩
    rw [hostCallXP_fixpoint]
    exact .inl ⟨fi, fn, ps, rs, f₂, out.1, .flow out.2, hfi, hcode, hty,
      d'.mono fun _ _ _ _ h => (h.2 h.1).1, .flow⟩
  · obtain ⟨fi, h, r, hfi, hcode, hhost, hfl⟩ := hh
    refine ⟨?_, hD _ _ _ _ _ hhost hs⟩
    rw [hostCallXP_fixpoint]
    exact .inr ⟨fi, h, r, hfi, hcode, hhost, hfl⟩

theorem evalOXP_host_iff_evalH (hD : HostKeepsDirect host) {s : Store H} (hs : StoreDirect s)
    {f : Frame} {stk : List Val} {es : List BExpr} {s' : Store H} {f' : Frame} {fl : Flow}
    (hx : xFreeL es = true) (he : ehFreeL es = true) :
    EvalOXP (hostCallXP host) s f stk es (s', f', .flow fl) ↔ EvalH host s f stk es (s', f', fl) := by
  constructor
  · intro d
    obtain ⟨-, d'⟩ := EvalOXP.restrictDirect
      (fun _ _ _ _ hq hs => (hostCallXP_le_hostCall hD _ _ _ _ hq hs).2) d hs
    exact (evalOXP_flow_iff_evalO hx he).1
      (d'.mono fun _ _ _ _ h => (hostCallXP_le_hostCall hD _ _ _ _ h.2 h.1).1)
  · intro d
    obtain ⟨-, d'⟩ := EvalOXP.restrictDirect
      (fun _ _ _ _ hq hs => (hostCall_le_hostCallXP hD _ _ _ _ hq hs).2)
      ((evalOXP_flow_iff_evalO hx he).2 d) hs
    exact d'.mono fun _ _ _ _ h => (hostCall_le_hostCallXP hD _ _ _ _ h.2 h.1).1

theorem bodyCallXP_host_iff (hD : HostKeepsDirect host) {s : Store H} (hs : StoreDirect s)
    {a : Nat} {args : List Val} {out : Store H × Flow} :
    bodyCallXP (hostCallXP host) s a args out ↔ bodyCall (hostCall host) s a args out := by
  constructor
  · rintro ⟨fi, fn, ps, rs, f₂, s₁, o, hfi, hcode, hty, d, hfr⟩
    have hx := hs a fi fn hfi hcode
    cases hfr with
    | tail => exact absurd d (evalOXP_not_tail hx.1)
    | flow => exact ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, (evalOXP_host_iff_evalH hD hs hx.1 hx.2).1 d⟩
  · rintro ⟨fi, fn, ps, rs, f₂, hfi, hcode, hty, d⟩
    have hx := hs a fi fn hfi hcode
    exact ⟨fi, fn, ps, rs, f₂, out.1, .flow out.2, hfi, hcode, hty,
      (evalOXP_host_iff_evalH hD hs hx.1 hx.2).2 d, .flow⟩

end Silmaril.Wasm.Interp
