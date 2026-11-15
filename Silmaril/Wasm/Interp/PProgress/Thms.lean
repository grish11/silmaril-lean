module

public import Silmaril.Proofs.Wasm.Interp.PDivCore
public import Silmaril.Proofs.Wasm.Interp.PNoOutcome
public import Silmaril.Proofs.Wasm.Interp.PDivIff

/-!
# Divergence and adequacy with exceptions and pending tail calls (F5): theorems

The closed semantics with pending tail calls and exceptions (`CallXP.EvalOXP`,
`XRecursionP.closedCallXP`) and its coinductive divergence (`XDivergeP.EvalDivXP` for problems,
`XDivergeP.FunDivXP` for calls, a pending tail call's callee descended into at the frame), against
Core 3.0 with exceptions, every call form included.

**Divergence is Core divergence** (checked code, `CheckedP tags`: `ehExt tags`-checked in a
checked store with the tag invariants `TagsOk tags`; every profile and host, no typing):

* `diverges_of_evalDivXP`: a diverging problem diverges in Core in any context, a diverging
  `try_table` body inside its handler;
* `invoke_diverges_of_funDivXP`: a diverging call makes its invocation diverge, including a body
  ending in a pending tail call whose callee diverges, made when the frame is left.

**Progress** (typed problems, `TypedP tags`; typed calls, `CallTypedP tags`; stores of Wasm
functions with function types, `WasmFuncsT`): no closed outcome means divergence
(`evalDivXP_of_noOutcome`, `funDivXP_of_noAnswer`). `throw`, `throw_ref` and `try_table` always
progress: the tag comes from the check and the tag invariants, the `throw_ref` operand from
typing (`throwRef_top`), a thrown exception is always resolved by the clauses.

**The converse, for invocations** (typed invocation `StoreOk`, `InvokeOk`; `ehExt tags`-checked
store `StoreChkE (ehExt tags)`, `WasmFuncsT`, `TagsOk tags`; every deterministic profile
`profile o`, closed host `noHostX`):

* `invoke_diverges_iff_funDivXP`: Core 3.0 divergence is exactly `FunDivXP`;
* `invoke_nf_terminalP`: every normal form reached is terminal (values, a trap, or an uncaught
  exception `throwing t`);
* `invoke_terminal_closedCallXP`: a terminal run ends as a closed answer does;
* `invoke_closedXP_adequacy`: the bundle, every closed answer (the throw case included) being a
  Core run.

Out of scope: hosts, observations and infinite traces; only the closed, deterministic setting.
-/

public section

open Silmaril.Wasm.SingleThreaded

namespace Silmaril.Wasm.Interp.PProgress

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp
open Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.XRecursionP Silmaril.Wasm.Abstract.XDivergeP

variable {H : Type}

/-- **Divergence with pending tail calls is Core 3.0 divergence**, for checked problems, in any
context, at every profile and host. -/
theorem diverges_of_evalDivXP {P : Numerics.Profile} {host : HostSemantics H} {tags : List TagInst}
    {s : Store H} {f : Frame} {stk : List Val} {es : List Binaryen.BExpr}
    (hd : EvalDivXP s f stk es) (hc : CheckedP tags s f stk es) (E : Sim.ActiveCtx) :
    Diverges P host (E.plug ⟨s, f, xcode stk es⟩) :=
  Silmaril.Wasm.Interp.diverges_of_evalDivXP hd hc E

/-- **A diverging call makes its invocation diverge**, on an `ehExt tags`-checked store with the
tag invariants, at every profile and host. -/
theorem invoke_diverges_of_funDivXP {P : Numerics.Profile} {host : HostSemantics H}
    {tags : List TagInst} {s : Store H} {a : Nat} {vs : List Val}
    (hS : StoreChkE (ehExt tags) s.funcs) (hts : TagsOk tags s) (hok : InvokeOk s a vs)
    (hd : FunDivXP s a vs) : Diverges P host (invoke s a vs) :=
  Silmaril.Wasm.Interp.invoke_diverges_of_funDivXP hS hts hok hd

/-- **The operand of a typed `throw_ref`** is a null or an exception reference. -/
theorem throwRef_top {s : Store H} {f : Frame} {stk : List Val} {rest : List Admin}
    (ht : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ .plain .throwRef :: rest⟩) :
    ∃ (r : Ref) (stk' : List Val), stk = .ref r :: stk' ∧ (r = .null ∨ ∃ a, r = .exn a) :=
  Silmaril.Wasm.Interp.throwRef_top ht

/-- **A checked call's closed answer returns, traps or throws.** -/
theorem calleeP_flow {tags : List TagInst} {s s₂ : Store H} {a : Nat} {us : List Val}
    {fl : Binaryen.Flow} (hcc : CallChkP tags s a us) (h : closedCallXP s a us (s₂, fl)) :
    (∃ vs, fl.retVals = some vs) ∨ fl.Abrupt :=
  Silmaril.Wasm.Interp.calleeP_flow hcc h

/-- **No closed outcome means divergence**, for typed problems in a store of Wasm functions. -/
theorem evalDivXP_of_noOutcome {tags : List TagInst} {s : Store H} {f : Frame} {stk : List Val}
    {es : List Binaryen.BExpr} (ht : TypedP tags s f stk es) (hW : WasmFuncsT s)
    (hne : ¬ ∃ r, EvalOXP closedCallXP s f stk es r) : EvalDivXP s f stk es :=
  Silmaril.Wasm.Interp.evalDivXP_of_noOutcome ht hW hne

/-- **No closed answer means divergence**, for typed calls in a store of Wasm functions. -/
theorem funDivXP_of_noAnswer {tags : List TagInst} {s : Store H} {a : Nat} {args : List Val}
    (ht : CallTypedP tags s a args) (hW : WasmFuncsT s)
    (hne : ¬ ∃ out, closedCallXP s a args out) : FunDivXP s a args :=
  Silmaril.Wasm.Interp.funDivXP_of_noAnswer ht hW hne

/-- **Core 3.0 divergence is divergence with pending tail calls and exceptions, both ways.** -/
theorem invoke_diverges_iff_funDivXP {tags : List TagInst} {o : GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} (hs : StoreOk s) (hok : InvokeOk s a vs) (hS : StoreChkE (ehExt tags) s.funcs)
    (hW : WasmFuncsT s) (hts : TagsOk tags s) :
    Diverges (profile o) noHostX (invoke s a vs) ↔ FunDivXP s a vs :=
  Silmaril.Wasm.Interp.invoke_diverges_iff_funDivXP hs hok hS hW hts

/-- **No stuck ends**: every normal form reached is terminal. -/
theorem invoke_nf_terminalP {tags : List TagInst} {o : GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} {c' : Config H} (hs : StoreOk s) (hok : InvokeOk s a vs)
    (hS : StoreChkE (ehExt tags) s.funcs) (hW : WasmFuncsT s) (hts : TagsOk tags s)
    (hst : Steps (profile o) noHostX (invoke s a vs) c')
    (hnf : ∀ x, ¬ Step (profile o) noHostX c' x) : c'.Terminal :=
  Silmaril.Wasm.Interp.invoke_nf_terminalP hs hok hS hW hts hst hnf

/-- **Completeness for terminating runs**: values, a trap, or an uncaught exception. -/
theorem invoke_terminal_closedCallXP {tags : List TagInst} {o : GrowOracle} {s : Store H} {a : Nat}
    {vs : List Val} {fi : FuncInst H} {ps rs : List Validation.CValType} {c' : Config H}
    (hs : StoreOk s) (hok : InvokeOk s a vs) (hS : StoreChkE (ehExt tags) s.funcs)
    (hW : WasmFuncsT s) (hts : TagsOk tags s) (hfi : s.funcs[a]? = some fi)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hst : Steps (profile o) noHostX (invoke s a vs) c') (hterm : c'.Terminal) :
    ∃ (s₂ : Store H) (fl : Binaryen.Flow), closedCallXP s a vs (s₂, fl) ∧
      ((∃ ws, fl.retVals = some ws ∧ c' = ⟨s₂, {}, vals (ws.take rs.length).reverse⟩) ∨
        (fl = .trap ∧ c' = ⟨s₂, {}, [.trap]⟩) ∨
        (∃ t, fl = .throw t ∧ c' = ⟨s₂, {}, throwing t⟩)) :=
  Silmaril.Wasm.Interp.invoke_terminal_closedCallXP hs hok hS hW hts hfi hty hst hterm

/-- **Core 3.0 adequacy of the closed semantics with exceptions and pending tail calls.** -/
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
      (∀ t, fl = .throw t → Steps (profile o) noHostX (invoke s a vs) ⟨s₂, {}, throwing t⟩)) :=
  Silmaril.Wasm.Interp.invoke_closedXP_adequacy hs hok hS hW hts hfi hty

end Silmaril.Wasm.Interp.PProgress
