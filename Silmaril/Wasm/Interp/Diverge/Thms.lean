module

public import Silmaril.Wasm.Interp.Diverge.Defs
public import Silmaril.Wasm.Interp.Thms
import Silmaril.Proofs.Wasm.Interp.DivergeBasic
import Silmaril.Proofs.Wasm.Interp.DivergeInvoke

/-!
# Coinductive divergence of the native semantics: theorems

Native facts, any store:

* `evalDiv_iff_step`, `evalDiv_of_coind`: unfolding and coinduction;
* `not_evalDiv_of_eval`: a problem that evaluates does not diverge, since the
  semantics is deterministic (`eval_det'`);
* `localDiv_evalDiv`: divergence within a function is divergence.

**Against Core 3.0.** On typed, native, arity-checked stores, every profile:

* `funDiv_iff_invokeRun_none`: the interpreter fails at every fuel exactly
  when the callee body diverges coinductively;
* `core_diverges_iff_funDiv`: **Core 3.0 divergence of an invocation is
  `FunDiv`.**

So in that setting divergence has a structural, positive characterisation.
It is not "no result": it says at every point which part diverges. The
completeness direction uses typed progress (`Total`'s invariants) to rule out
the interpreter getting stuck. No `Step` inversion is used.
-/

public section

namespace Silmaril.Wasm.Interp

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core

variable {H : Type}

/-- The native recursive semantics is deterministic. -/
theorem eval_det' {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r₁ r₂ : Store H × Frame × Flow} (h₁ : Eval s f stk es r₁) (h₂ : Eval s f stk es r₂) :
    r₁ = r₂ :=
  eval_det h₁ h₂

/-- Unfolding divergence once. -/
theorem evalDiv_iff_step {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    EvalDiv s f stk es ↔ DivStep EvalDiv EvalDiv s f stk es :=
  evalDiv_unfold

/-- Unfolding divergence within a function once. -/
theorem localDiv_iff_step {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    LocalDiv s f stk es ↔ DivStep LocalDiv ⊥ s f stk es :=
  localDiv_unfold

/-- Coinduction: a predicate closed under divergence steps diverges. -/
theorem evalDiv_of_coind {X : Problem H}
    (h : ∀ s f stk es, X s f stk es → DivStep X X s f stk es) : X ≤ EvalDiv :=
  evalDiv_coind h

/-- Coinduction for divergence within a function. -/
theorem localDiv_of_coind {X : Problem H}
    (h : ∀ s f stk es, X s f stk es → DivStep X ⊥ s f stk es) : X ≤ LocalDiv :=
  localDiv_coind h

/-- **A problem that evaluates does not diverge.** -/
theorem not_evalDiv_of_eval {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {r : Store H × Frame × Flow} (h : Eval s f stk es r) : ¬ EvalDiv s f stk es :=
  eval_not_evalDiv h

/-- Divergence within a function is divergence. -/
theorem localDiv_evalDiv : (LocalDiv : Problem H) ≤ EvalDiv := localDiv_le_evalDiv

/-- **The interpreter fails at every fuel exactly when the body diverges.** -/
theorem funDiv_iff_invokeRun_none {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : StoreChk s.funcs) (hok : InvokeOk s a vs) :
    FunDiv s a vs ↔ ∀ fuel, invokeRun fuel s a vs = none :=
  (invokeRun_none_iff_funDiv hs hF hS hok).symm

/-- **Core 3.0 divergence of a typed invocation is native coinductive
divergence of the callee body**, every profile. -/
theorem core_diverges_iff_funDiv {s : Store H} {a : Nat} {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : StoreChk s.funcs) (hok : InvokeOk s a vs)
    (P : Numerics.Profile) : Diverges P closedHost (invoke s a vs) ↔ FunDiv s a vs :=
  diverges_iff_funDiv hs hF hS hok P

end Silmaril.Wasm.Interp
