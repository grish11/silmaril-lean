module

public import Silmaril.Proofs.Wasm.Interp.PNoOutcome
public import Silmaril.Proofs.Wasm.Interp.Termination

/-!
# Core 3.0 divergence is divergence with exceptions and pending tail calls, both ways (proofs)

For a typed invocation of an `ehExt tags`-checked typed store of Wasm functions with the tag
invariants, in a deterministic profile with the closed host:

* `invoke_diverges_iff_funDivXP`: Core 3.0 divergence is exactly `FunDivXP`, the coinductive
  divergence of the call with pending tail calls and exceptions.
  `FunDivXP → Diverges` is `invoke_diverges_of_funDivXP`. Conversely, otherwise the call has a
  closed answer (`funDivXP_of_noAnswer`, contraposed), which returns, traps or throws
  (`calleeP_flow`); the closure's answers are sound (`closedCallXP_sound`), so Core runs the
  invocation to values, a trap or an uncaught exception, a normal form, and a typed configuration
  that reaches a normal form does not diverge (`not_diverges_typed`).
* `invoke_nf_terminalP`: every normal form reached is terminal.
* `invoke_terminal_closedCallXP`: a terminal run ends as a closed answer does: its values, a trap,
  or the uncaught exception it throws (determinism, `eq_of_steps_of_nf`).
* `invoke_closedXP_adequacy`: the bundle.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.CallXT Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.XRecursionP Silmaril.Wasm.Abstract.XDivergeP Silmaril.Wasm.SingleThreaded

variable {H : Type}

section Invoke

variable {tags : List TagInst} {s : Store H} {a : Nat} {vs : List Val}

/-- The invocation's code. -/
theorem invoke_eqP {fi : FuncInst H} (hfi : s.funcs[a]? = some fi) :
    invoke s a vs = ⟨s, {}, vals vs ++ [.ref (.func a), .callRefType fi.type]⟩ := by
  simp [invoke, hfi]

/-- **A typed invocation is a typed call.** -/
theorem invoke_callTyped (hs : StoreOk s) (hok : InvokeOk s a vs)
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) : CallTypedP tags s a vs := by
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := id hok
  have hty : Validation.DefType.funcType? fi.type = some (ps.toList, rs.toList) := by
    unfold Validation.DefType.funcType?; rw [Validation.Expand.iff.mp he]
  obtain ⟨_, _, _, _, _, hcfg⟩ := invoke_ok hs hok
  have hct := Sim.ContextTyped.of_configOk hcfg
  rw [invoke_eqP hfi] at hct
  exact ⟨⟨hS, hts, fi, _, _, hfi, hty, hvs.length_eq⟩, {}, .callRefType fi.type, [], [], trivial,
    by simpa [callCode, vals] using hct⟩

/-- **An invocation in an invariant is a call in it.** -/
theorem CtxInv.invoke_callTyped (K : CtxInv H) (hct : K.CT (invoke s a vs))
    (hok : InvokeOk s a vs) (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) :
    K.CallTypedP tags s a vs := by
  obtain ⟨fi, ps, rs, hfi, he, hvs⟩ := id hok
  have hty : Validation.DefType.funcType? fi.type = some (ps.toList, rs.toList) := by
    unfold Validation.DefType.funcType?; rw [Validation.Expand.iff.mp he]
  rw [invoke_eqP hfi] at hct
  exact ⟨⟨hS, hts, fi, _, _, hfi, hty, hvs.length_eq⟩, {}, .callRefType fi.type, [], [], trivial,
    by simpa [callCode, vals] using hct⟩

/-- **The Core runs of an invocation's closed answer**: values, a trap, or an uncaught
exception. -/
theorem invoke_answer_steps {P : Numerics.Profile} {host : HostSemantics H} {fi : FuncInst H}
    {ps rs : List Validation.CValType} {s₂ : Store H} {fl : Binaryen.Flow}
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) (hn : vs.length = ps.length)
    (hcall : closedCallXP s a vs (s₂, fl)) :
    (∀ ws, fl.retVals = some ws →
      Steps P host (invoke s a vs) ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∧
    (fl = .trap → Steps P host (invoke s a vs) ⟨s₂, {}, [.trap]⟩) ∧
    (∀ t, fl = .throw t → Steps P host (invoke s a vs) ⟨s₂, {}, throwing t⟩) := by
  obtain ⟨-, hsnd⟩ := closedCallXP_sound (P := P) (host := host) tags s a vs (s₂, fl) hcall hts
  obtain ⟨-, hret, htr, hth⟩ := hsnd {} fi ps rs (.callRefType fi.type) hS hfi hty hn trivial
  rw [invoke_eqP hfi]
  exact ⟨hret, htr, hth⟩

end Invoke

/-- **Core 3.0 divergence is divergence with pending tail calls and exceptions**, for typed
invocations of `ehExt tags`-checked typed stores of Wasm functions with the tag invariants, in
every deterministic profile. -/
theorem invoke_diverges_iff_funDivXP {tags : List TagInst} {o : GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} (hs : StoreOk s) (hok : InvokeOk s a vs) (hS : StoreChkE (ehExt tags) s.funcs)
    (hW : WasmFuncsT s) (hts : TagsOk tags s) :
    Diverges (profile o) noHostX (invoke s a vs) ↔ FunDivXP s a vs := by
  refine ⟨fun hD => ?_, invoke_diverges_of_funDivXP hS hts hok⟩
  by_contra hnd
  have hct := invoke_callTyped hs hok hS hts
  obtain ⟨⟨-, -, fi, ps, rs, hfi, hty, hn⟩, -⟩ := id hct
  obtain ⟨_, _, _, _, _, hcfg⟩ := invoke_ok hs hok
  by_cases hex : ∃ out, closedCallXP s a vs out
  swap
  · exact hnd (funDivXP_of_noAnswer hct hW hex)
  obtain ⟨⟨s₂, fl⟩, hcall⟩ := hex
  obtain ⟨hret, htr, hth⟩ := invoke_answer_steps (P := profile o) (host := noHostX) hS hts hfi hty
    hn hcall
  rcases calleeP_flow hct.1 hcall with ⟨ws, hws⟩ | hab
  · exact not_diverges_typed hcfg (hret ws hws)
      (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.values _, rfl⟩ hx) hD
  · cases fl with
    | trap =>
      exact not_diverges_typed hcfg (htr rfl)
        (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.trap, rfl⟩ hx) hD
    | throw t =>
      exact not_diverges_typed hcfg (hth t rfl)
        (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.throw t, rfl⟩ hx) hD
    | _ => exact hab.elim

/-- **Completeness for terminating runs**: a Core 3.0 run of a typed invocation to a terminal
configuration is the end of a closed answer of the call: its values, a trap, or the uncaught
exception it throws. -/
theorem invoke_terminal_closedCallXP {tags : List TagInst} {o : GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} {fi : FuncInst H} {ps rs : List Validation.CValType} {c' : Config H}
    (hs : StoreOk s) (hok : InvokeOk s a vs) (hS : StoreChkE (ehExt tags) s.funcs)
    (hW : WasmFuncsT s) (hts : TagsOk tags s) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hst : Steps (profile o) noHostX (invoke s a vs) c') (hterm : c'.Terminal) :
    ∃ (s₂ : Store H) (fl : Binaryen.Flow), closedCallXP s a vs (s₂, fl) ∧
      ((∃ ws, fl.retVals = some ws ∧ c' = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
        (fl = .trap ∧ c' = ⟨s₂, {}, [.trap]⟩) ∨
        (∃ t, fl = .throw t ∧ c' = ⟨s₂, {}, throwing t⟩)) := by
  have hct := invoke_callTyped hs hok hS hts
  obtain ⟨⟨-, -, fi', ps', rs', hfi', hty', hn⟩, -⟩ := id hct
  rw [hfi] at hfi'; cases hfi'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
  have hnf' : ∀ x, ¬ Step (profile o) noHostX c' x :=
    fun x hx => Exec.BehaviourRefinement.not_step_of_terminal hterm hx
  obtain ⟨_, _, _, _, _, hcfg⟩ := invoke_ok hs hok
  by_cases hex : ∃ out, closedCallXP s a vs out
  swap
  · exact absurd (invoke_diverges_of_funDivXP (P := profile o) (host := noHostX) hS hts hok
      (funDivXP_of_noAnswer hct hW hex)) (not_diverges_typed hcfg hst hnf')
  obtain ⟨⟨s₂, fl⟩, hcall⟩ := hex
  obtain ⟨hret, htr, hth⟩ := invoke_answer_steps (P := profile o) (host := noHostX) hS hts hfi hty
    hn hcall
  refine ⟨s₂, fl, hcall, ?_⟩
  rcases calleeP_flow hct.1 hcall with ⟨ws, hws⟩ | hab
  · exact .inl ⟨ws, hws, Exec.BehaviourRefinement.eq_of_steps_of_nf hst (hret ws hws) hnf'
      (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.values _, rfl⟩ hx)⟩
  · cases fl with
    | trap =>
      exact .inr (.inl ⟨rfl, Exec.BehaviourRefinement.eq_of_steps_of_nf hst (htr rfl) hnf'
        (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.trap, rfl⟩ hx)⟩)
    | throw t =>
      exact .inr (.inr ⟨t, rfl, Exec.BehaviourRefinement.eq_of_steps_of_nf hst (hth t rfl) hnf'
        (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.throw t, rfl⟩ hx)⟩)
    | _ => exact hab.elim

/-- **No stuck ends**: a Core 3.0 run of a typed invocation that reaches a normal form reaches a
terminal configuration (values, a trap, or an uncaught exception). -/
theorem invoke_nf_terminalP {tags : List TagInst} {o : GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} {c' : Config H} (hs : StoreOk s) (hok : InvokeOk s a vs)
    (hS : StoreChkE (ehExt tags) s.funcs) (hW : WasmFuncsT s) (hts : TagsOk tags s)
    (hst : Steps (profile o) noHostX (invoke s a vs) c')
    (hnf : ∀ x, ¬ Step (profile o) noHostX c' x) : c'.Terminal := by
  have hct := invoke_callTyped hs hok hS hts
  obtain ⟨⟨-, -, fi, ps, rs, hfi, hty, hn⟩, -⟩ := id hct
  obtain ⟨_, _, _, _, _, hcfg⟩ := invoke_ok hs hok
  by_cases hex : ∃ out, closedCallXP s a vs out
  swap
  · exact absurd (invoke_diverges_of_funDivXP (P := profile o) (host := noHostX) hS hts hok
      (funDivXP_of_noAnswer hct hW hex)) (not_diverges_typed hcfg hst hnf)
  obtain ⟨⟨s₂, fl⟩, hcall⟩ := hex
  obtain ⟨hret, htr, hth⟩ := invoke_answer_steps (P := profile o) (host := noHostX) hS hts hfi hty
    hn hcall
  rcases calleeP_flow hct.1 hcall with ⟨ws, hws⟩ | hab
  · rw [Exec.BehaviourRefinement.eq_of_steps_of_nf hst (hret ws hws) hnf
      (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.values _, rfl⟩ hx)]
    exact ⟨.values _, rfl⟩
  · cases fl with
    | trap =>
      rw [Exec.BehaviourRefinement.eq_of_steps_of_nf hst (htr rfl) hnf
        (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.trap, rfl⟩ hx)]
      exact ⟨.trap, rfl⟩
    | throw t =>
      rw [Exec.BehaviourRefinement.eq_of_steps_of_nf hst (hth t rfl) hnf
        (fun x hx => Exec.BehaviourRefinement.not_step_of_terminal ⟨.throw t, rfl⟩ hx)]
      exact ⟨.throw t, rfl⟩
    | _ => exact hab.elim

/-- **Core 3.0 adequacy of the closed semantics with exceptions and pending tail calls**, for
typed invocations of `ehExt tags`-checked typed stores of Wasm functions with the tag invariants,
closed host, every deterministic profile:

1. Core diverges iff the call diverges coinductively (`FunDivXP`);
2. a Core run that stops, stops at a terminal configuration, the end of a closed answer (values,
   a trap, or an uncaught exception);
3. every closed answer is a Core run (values, a trap, or an uncaught exception). -/
theorem invoke_closedXP_adequacy {tags : List TagInst} {o : GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} {fi : FuncInst H} {ps rs : List Validation.CValType}
    (hs : StoreOk s) (hok : InvokeOk s a vs) (hS : StoreChkE (ehExt tags) s.funcs)
    (hW : WasmFuncsT s) (hts : TagsOk tags s) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs)) :
    (Diverges (profile o) noHostX (invoke s a vs) ↔ FunDivXP s a vs) ∧
    (∀ c', Steps (profile o) noHostX (invoke s a vs) c' → (∀ x, ¬ Step (profile o) noHostX c' x) →
      c'.Terminal ∧ ∃ (s₂ : Store H) (fl : Binaryen.Flow), closedCallXP s a vs (s₂, fl) ∧
        ((∃ ws, fl.retVals = some ws ∧ c' = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
          (fl = .trap ∧ c' = ⟨s₂, {}, [.trap]⟩) ∨
          (∃ t, fl = .throw t ∧ c' = ⟨s₂, {}, throwing t⟩))) ∧
    (∀ (s₂ : Store H) (fl : Binaryen.Flow), closedCallXP s a vs (s₂, fl) →
      (∀ ws, fl.retVals = some ws →
        Steps (profile o) noHostX (invoke s a vs) ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∧
      (fl = .trap → Steps (profile o) noHostX (invoke s a vs) ⟨s₂, {}, [.trap]⟩) ∧
      (∀ t, fl = .throw t → Steps (profile o) noHostX (invoke s a vs) ⟨s₂, {}, throwing t⟩)) := by
  refine ⟨invoke_diverges_iff_funDivXP hs hok hS hW hts, fun c' hst hnf => ?_,
    fun s₂ fl hcall => ?_⟩
  · have hterm := invoke_nf_terminalP hs hok hS hW hts hst hnf
    exact ⟨hterm, invoke_terminal_closedCallXP hs hok hS hW hts hfi hty hst hterm⟩
  · obtain ⟨⟨-, -, fi', ps', rs', hfi', hty', hn⟩, -⟩ := invoke_callTyped hs hok hS hts
    rw [hfi] at hfi'; cases hfi'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hty.symm.trans hty'))
    exact invoke_answer_steps hS hts hfi hty hn hcall

end Silmaril.Wasm.Interp
