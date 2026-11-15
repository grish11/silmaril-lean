module

public import Silmaril.Proofs.Wasm.Interp.XNoOutcome
public import Silmaril.Proofs.Wasm.Interp.Termination

/-!
# Core 3.0 divergence is extended divergence, both ways (proofs)

`invoke_diverges_iff_funDivX`: for a typed invocation of a `tExt`-checked typed store of Wasm
functions, in a deterministic profile, Core 3.0 divergence is exactly the coinductive divergence
of the callee body in the closed extended semantics (`FunDivX`), every call form included.

* `FunDivX → Diverges`: the forward simulation of divergence (`invoke_diverges_of_funDivT`).
* `Diverges → FunDivX`: otherwise the callee body has a closed extended outcome
  (`evalDivX_of_noOutcome`, contraposed); the typed closure is a sound oracle
  (`oracleSoundT_typedClosed`), so Core runs the invocation to values or a trap, a normal form;
  a typed configuration that reaches a normal form does not diverge in a deterministic profile
  (`not_diverges_typed`).
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.XRecursion
open Silmaril.Wasm.Abstract.XDiverge Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-- **Core 3.0 divergence is extended divergence**, for typed invocations of `tExt`-checked
typed stores of Wasm functions, in every deterministic profile. -/
theorem invoke_diverges_iff_funDivX {o : GrowOracle} {s : Store H} {a : Nat} {vs : List Val}
    (hs : StoreOk s) (hok : InvokeOk s a vs) (hS : StoreChkE tExt s.funcs) (hW : WasmFuncsT s) :
    Diverges (profile o) noHostX (invoke s a vs) ↔ FunDivX s a vs := by
  refine ⟨fun hD => ?_, invoke_diverges_of_funDivT hs hok hS⟩
  by_contra hnd
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := id hok
  obtain ⟨fn, -, -, hcode, -⟩ := hW a fi hfi
  have hty : Validation.DefType.funcType? fi.type = some (ps.toList, rs.toList) := by
    unfold Validation.DefType.funcType?; rw [Validation.Expand.iff.mp he]
  have hE := entry_of_invokeOk (P := profile o) hs hok
  have hn : vs.length = ps.toList.length := hvs.length_eq
  have ht := callee_typedT hS hE hfi hcode hty hn
  by_cases hex : ∃ r, EvalOX closedCallX s (Frame.forCall fi.module vs fn.locals) []
      (Binaryen.liftInstrs fn.body) r
  swap
  · exact hnd ⟨fi, fn, hfi, hcode, evalDivX_of_noOutcome ht hW hex⟩
  obtain ⟨⟨s₂, f₂, fl⟩, d⟩ := hex
  have hcall : closedCallX s a vs (s₂, fl) := by
    rw [closedCallX_fixpoint]; exact ⟨fi, fn, _, _, f₂, hfi, hcode, hty, d⟩
  obtain ⟨⟨ob, -, hfok, -⟩, hret, htr⟩ := oracleSoundT_typedClosed (P := profile o) s s₂ {} a fi
    ps.toList rs.toList vs fl (.callRefType fi.type) hS hfi hty hn trivial ⟨hE, hcall⟩
  have hc : invoke s a vs = ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [invoke, hfi]
  obtain ⟨_, _, _, _, _, hcfg⟩ := invoke_ok hs hok
  rcases calleeX_flow (P := profile o) hS hfi hcode hty hn hE hcall with ⟨ws, hws⟩ | rfl | ⟨t, rfl⟩
  · have hst := hret ws hws
    rw [← hc] at hst
    exact not_diverges_typed hcfg hst
      (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.values _, rfl⟩ hx) hD
  · have hst := htr rfl
    rw [← hc] at hst
    exact not_diverges_typed hcfg hst
      (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.trap, rfl⟩ hx) hD
  · exact hfok

/-- **Completeness for terminating runs**: a Core 3.0 run of a typed invocation (of a
`tExt`-checked typed store of Wasm functions, deterministic profile) to a terminal
configuration is the end of a closed extended outcome of the callee: its values, or a trap. -/
theorem invoke_terminal_closedCallX {o : GrowOracle} {s : Store H} {a : Nat} {vs : List Val}
    {fi : FuncInst H} {ps rs : List Validation.CValType} {c' : Config H}
    (hs : StoreOk s) (hok : InvokeOk s a vs) (hS : StoreChkE tExt s.funcs) (hW : WasmFuncsT s)
    (hfi : s.funcs[a]? = some fi) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hst : Steps (profile o) noHostX (invoke s a vs) c') (hterm : c'.Terminal) :
    ∃ (s₂ : Store H) (fl : Binaryen.Flow), closedCallX s a vs (s₂, fl) ∧
      ((∃ ws, fl.retVals = some ws ∧ c' = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
        (fl = .trap ∧ c' = ⟨s₂, {}, [.trap]⟩)) := by
  obtain ⟨fn, -, -, hcode, -⟩ := hW a fi hfi
  have hE := entry_of_invokeOk (P := profile o) hs hok
  obtain ⟨fi', ps', rs', hfi', he', hvs⟩ := id hok
  rw [hfi] at hfi'; cases hfi'
  have hty' : Validation.DefType.funcType? fi.type = some (ps'.toList, rs'.toList) := by
    unfold Validation.DefType.funcType?; rw [Validation.Expand.iff.mp he']
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
  have hn : vs.length = ps'.toList.length := hvs.length_eq
  have hnf' : ∀ x, ¬ Step (profile o) noHostX c' x :=
    fun x hx => Exec.BehaviourRefinement.not_step_of_terminal hterm hx
  obtain ⟨_, _, _, _, _, hcfg⟩ := invoke_ok hs hok
  by_cases hex : ∃ r, EvalOX closedCallX s (Frame.forCall fi.module vs fn.locals) []
      (Binaryen.liftInstrs fn.body) r
  swap
  · exact absurd (invoke_diverges_of_funDivT (P := profile o) hs hok hS
      ⟨fi, fn, hfi, hcode, evalDivX_of_noOutcome (callee_typedT hS hE hfi hcode hty hn) hW hex⟩)
      (not_diverges_typed hcfg hst hnf')
  obtain ⟨⟨s₂, f₂, fl⟩, d⟩ := hex
  have hcall : closedCallX s a vs (s₂, fl) := by
    rw [closedCallX_fixpoint]; exact ⟨fi, fn, _, _, f₂, hfi, hcode, hty, d⟩
  obtain ⟨⟨ob, -, hfok, -⟩, hret, htr⟩ := oracleSoundT_typedClosed (P := profile o) s s₂ {} a fi
    ps'.toList rs'.toList vs fl (.callRefType fi.type) hS hfi hty hn trivial ⟨hE, hcall⟩
  have hc : invoke s a vs = ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ := by
    simp [invoke, hfi]
  refine ⟨s₂, fl, hcall, ?_⟩
  rcases calleeX_flow (P := profile o) hS hfi hcode hty hn hE hcall with ⟨ws, hws⟩ | rfl | ⟨t, rfl⟩
  · have h₂ := hret ws hws
    rw [← hc] at h₂
    exact .inl ⟨ws, hws, Exec.BehaviourRefinement.eq_of_steps_of_nf hst h₂ hnf'
      (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.values _, rfl⟩ hx)⟩
  · have h₂ := htr rfl
    rw [← hc] at h₂
    exact .inr ⟨rfl, Exec.BehaviourRefinement.eq_of_steps_of_nf hst h₂ hnf'
      (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.trap, rfl⟩ hx)⟩
  · exact hfok.elim

end Silmaril.Wasm.Interp
