module

public import Silmaril.Wasm.Abstract.XDivergeP.Defs
import Silmaril.Proofs.Wasm.Abstract.XDivergeP.Basic

/-!
# Coinductive divergence with exceptions and pending tail calls: theorems

* Unfolding: `evalDivXP_iff_step`, `funDivXP_iff_step`; the frame-level reading of a call's
  divergence, `funDivXP_iff`: the body diverges, or it ends in a pending tail call (made when the
  frame is left) whose own call diverges.
* Joint coinduction: `evalDivXP_of_coind`.
-/

public section

namespace Silmaril.Wasm.Abstract.XDivergeP

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Interp (Problem)
open Silmaril.Wasm.Abstract.CallXP Silmaril.Wasm.Abstract.XRecursionP

variable {H : Type}

theorem evalDivXP_iff_step {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr} :
    EvalDivXP s f stk es ↔ DivStepXP EvalDivXP FunDivXP s f stk es :=
  Silmaril.Proofs.Wasm.Abstract.XDivergeP.evalDivXP_unfold

theorem funDivXP_iff_step {s : Store H} {a : Nat} {vs : List Val} :
    FunDivXP s a vs ↔ CallStepXP EvalDivXP FunDivXP s a vs :=
  Silmaril.Proofs.Wasm.Abstract.XDivergeP.funDivXP_unfold

/-- **Joint coinduction** for the divergence of problems and of calls. -/
theorem evalDivXP_of_coind {X : Problem H} {Y : CallProblem H}
    (hX : ∀ s f stk es, X s f stk es → DivStepXP X Y s f stk es)
    (hY : ∀ s a vs, Y s a vs → CallStepXP X Y s a vs) : X ≤ EvalDivXP ∧ Y ≤ FunDivXP :=
  Silmaril.Proofs.Wasm.Abstract.XDivergeP.coind hX hY

/-- **A call diverges at the frame**: its body diverges, or the body ends in a pending tail
call, made when the frame is left, whose own call diverges. -/
theorem funDivXP_iff {s : Store H} {a : Nat} {vs : List Val} :
    FunDivXP s a vs ↔ ∃ (fi : FuncInst H) (fn : Func), s.funcs[a]? = some fi ∧ fi.code = .wasm fn ∧
      (EvalDivXP s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body) ∨
        ∃ (s₁ : Store H) (f₂ : Frame) (a' : Nat) (args' : List Val) (n : Nat),
          EvalOXP closedCallXP s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body)
            (s₁, f₂, .tail a' args' n) ∧ FunDivXP s₁ a' args') :=
  Silmaril.Proofs.Wasm.Abstract.XDivergeP.funDivXP_iff

end Silmaril.Wasm.Abstract.XDivergeP
