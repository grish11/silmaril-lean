module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.TrapClose
public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.BackDet

/-!
# A callee's trap in the exact store of the trap (proofs)

The cases of `close_le_trapC` (`body_trap_callee`, `body_cut_callee`, `body_tail_callee`,
`host_trap_callee`), with the trap in the exact store where it happens, for a module whose
callees' traps carry their store (a session closure):

* `evalLXPh_trap_exact`: a body trapping itself traps in the store its logged run ends in;
* `evalLXPh_cut_exact`: a body whose call's callee traps in `s₂` traps in `s₂`;
* `evalLXPh_tail_exact`: a body whose pending tail call's callee traps in `s₂` traps in `s₂`;
* `host_trap_exact`: a host function answering a trap leaving `s'` traps in `s'`;
* `invoke_trap_exact`: an invocation whose function traps in `s₂`;
* `evRun_trap_det`: in the deterministic profile, two runs with the same log to a trap end in the
  same store and frame.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type} {P : Silmaril.Wasm.Numerics.Profile} {host : HostSemantics H}
  {tags : List TagInst} {s : Store H} {a : Nat} {us : List Val} {fi : FuncInst H}
  {ps rs : List Validation.CValType}

/-- A callee trapping in exactly `s₂`, for typed arguments on checked stores, is `TrapAt` with
the store `s₂`. -/
theorem trapAt_exact {g : Nat} {args : List Val} {s₁ s₂ s₂' : Store H} {b : List Val ⊕ Nat}
    {c₁ : List (Call (wasmHostSig H))}
    (hz : ∀ (fi' : FuncInst H) (ps' rs' : List Validation.CValType), s₁.funcs[g]? = some fi' →
      Validation.DefType.funcType? fi'.type = some (ps', rs') → TagsOk tags s₁ →
      StoreChkE (ehExt tags) s₁.funcs → args.length = ps'.length →
      ∀ (f : Frame) (c : Admin), c.IsCallRef →
        EvRun P host ⟨s₁, f, vals args ++ [.ref (.func g), c]⟩ c₁ ⟨s₂, f, [.trap]⟩) :
    TrapAt tags P host (OCall.mk g args s₁ b s₂') c₁ (· = s₂) := by
  intro a' args' s₁' b' s₂'' h fi' ps' rs' hfi hty hts hS hn f c hcr
  obtain ⟨rfl, rfl, rfl⟩ := mk_inj h.symm
  exact ⟨s₂, rfl, hz fi' ps' rs' hfi hty hts hS hn f c hcr⟩

theorem evalLXPh_trap_exact (hH : HostSliceT host) (hE : HostSliceE tags host) {fn : Func}
    {s' : Store H} {f₂ : Frame} {l : List (OCall H)} {q : List (Call (wasmHostSig H))}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (hts : TagsOk tags s) (hSt : StoreChkE (ehExt tags) s.funcs)
    (hE' : EvalLXPh s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) l
      (s', f₂, .flow .trap))
    (hp : Shape.SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q) (hq : Cons host q)
    (f : Frame) (c : Admin) (hcr : c.IsCallRef) :
    EvRun P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ q ⟨s', f, [.trap]⟩ := by
  obtain ⟨_, rfl, h⟩ := body_trap_callee (P := P) hH hE hfi hcode hty hn hts hSt hE' hp hq f c hcr
  exact h

theorem evalLXPh_cut_exact (hH : HostSliceT host) (hE : HostSliceE tags host) {fn : Func}
    {l l₁ l₂ : List (OCall H)} {r : Store H × Frame × POut} {g : Nat} {args : List Val}
    {s₁ s₂ s₂' : Store H} {b : List Val ⊕ Nat} {q c₁ : List (Call (wasmHostSig H))}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (hts : TagsOk tags s) (hSt : StoreChkE (ehExt tags) s.funcs)
    (hE' : EvalLXPh s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) l r)
    (hl : l = l₁ ++ OCall.mk g args s₁ b s₂' :: l₂)
    (hp : Shape.SubstPre (Shape.close wasmHOpenXP) (l₁.map OCall.lift) q)
    (hz : ∀ (fi' : FuncInst H) (ps' rs' : List Validation.CValType), s₁.funcs[g]? = some fi' →
      Validation.DefType.funcType? fi'.type = some (ps', rs') → TagsOk tags s₁ →
      StoreChkE (ehExt tags) s₁.funcs → args.length = ps'.length →
      ∀ (f : Frame) (c : Admin), c.IsCallRef →
        EvRun P host ⟨s₁, f, vals args ++ [.ref (.func g), c]⟩ c₁ ⟨s₂, f, [.trap]⟩)
    (hq : Cons host (q ++ c₁)) (f : Frame) (c : Admin) (hcr : c.IsCallRef) :
    EvRun P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ (q ++ c₁) ⟨s₂, f, [.trap]⟩ := by
  obtain ⟨_, rfl, h⟩ := body_cut_callee (P := P) hH hE hfi hcode hty hn hts hSt hE' hl hp
    (trapAt_exact hz) hq f c hcr
  exact h

theorem evalLXPh_tail_exact (hH : HostSliceT host) (hE : HostSliceE tags host) {fn : Func}
    {l : List (OCall H)} {s₁ s₂ : Store H} {f₂ : Frame} {a' n : Nat} {args : List Val}
    {q c₁ : List (Call (wasmHostSig H))}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (hts : TagsOk tags s) (hSt : StoreChkE (ehExt tags) s.funcs)
    (hE' : EvalLXPh s (Frame.forCall fi.module us fn.locals) [] (Binaryen.liftInstrs fn.body) l
      (s₁, f₂, .tail a' args n))
    (hp : Shape.SubstPre (Shape.close wasmHOpenXP) (l.map OCall.lift) q)
    (hz : ∀ (fi' : FuncInst H) (ps' rs' : List Validation.CValType), s₁.funcs[a']? = some fi' →
      Validation.DefType.funcType? fi'.type = some (ps', rs') → TagsOk tags s₁ →
      StoreChkE (ehExt tags) s₁.funcs → args.length = ps'.length →
      ∀ (f : Frame) (c : Admin), c.IsCallRef →
        EvRun P host ⟨s₁, f, vals args ++ [.ref (.func a'), c]⟩ c₁ ⟨s₂, f, [.trap]⟩)
    (hq : Cons host (q ++ c₁)) (f : Frame) (c : Admin) (hcr : c.IsCallRef) :
    EvRun P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ (q ++ c₁) ⟨s₂, f, [.trap]⟩ := by
  obtain ⟨_, rfl, h⟩ := body_tail_callee (P := P) (b := .inl []) (s₂ := s₂) hH hE hfi hcode hty
    hn hts hSt hE' hp (trapAt_exact hz) hq f c hcr
  exact h

theorem host_trap_exact {hh : H} {s' : Store H} (hfi : s.funcs[a]? = some fi)
    (hcode : fi.code = .host hh) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hn : us.length = ps.length) (hm : host hh s us (.returned s' .trap)) (f : Frame) (c : Admin)
    (hcr : c.IsCallRef) :
    EvRun P host ⟨s, f, vals us ++ [.ref (.func a), c]⟩ [⟨(hh, s, us), (s', .trap)⟩]
      ⟨s', f, [.trap]⟩ := by
  obtain ⟨_, rfl, h⟩ := host_trap_callee (P := P) hfi hcode hty hn hm f c hcr
  exact h

theorem invoke_trap_exact {vs : List Val} {s₂ : Store H} {cs : List (Call (wasmHostSig H))}
    (hfi : s.funcs[a]? = some fi)
    (h : ∀ (f : Frame) (c : Admin), c.IsCallRef →
      EvRun P host ⟨s, f, vals vs ++ [.ref (.func a), c]⟩ cs ⟨s₂, f, [.trap]⟩) :
    EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ := by
  rw [invoke_eq hfi]
  exact h {} _ trivial

theorem evRun_trap_det {o : SingleThreaded.GrowOracle} {K : Config H}
    {q : List (Call (wasmHostSig H))} {s₁ s₂ : Store H} {f₁ f₂ : Frame}
    (h₁ : EvRun (SingleThreaded.profile o) host K q ⟨s₁, f₁, [.trap]⟩)
    (h₂ : EvRun (SingleThreaded.profile o) host K q ⟨s₂, f₂, [.trap]⟩) : s₁ = s₂ ∧ f₁ = f₂ := by
  obtain ⟨n, hn⟩ := evRunN_of_evRun h₂
  have := evRun_det_end h₁ (ends_stuck (o := .trap) rfl s₁ f₁) hn
    (ends_stuck (o := .trap) rfl s₂ f₂)
  simp only [Config.mk.injEq] at this
  exact ⟨this.1.symm, this.2.1.symm⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
