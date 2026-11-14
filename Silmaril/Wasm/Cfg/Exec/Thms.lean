module

public import Silmaril.Wasm.Cfg.Exec.Defs

@[expose] public section

/-!
# The position invariant: first facts

* `resid_start`: a body's code on entry (`expression body`) is at its first instruction;
* `resid_done`: the values a sequence returns are at its end;
* `inFrame_entry`: the code `Step/call_ref-func` produces for a call of the body is `InFrame`
  at the first instruction.
-/

namespace Silmaril.Wasm.Cfg

open Silmaril.Wasm.Execution.Core

theorem resid_start (is : List Instr) : Resid is (.at 0) (expression is) := by
  simpa [vals] using Resid.at (is := is) [] (Nat.zero_le _)

theorem resid_done (is : List Instr) (vs : List Val) : Resid is (.at is.length) (vals vs) := by
  simpa [expression] using Resid.at (is := is) vs (le_refl _)

theorem inFrame_entry (body : Expr) (n m : Nat) (fr : Frame) :
    InFrame body (.at 0) [.frame n fr [.label m [] (expression body)]] :=
  .frame (resid_start body)

end Silmaril.Wasm.Cfg
