module

public import Silmaril.Wasm.Cfg.Exec.Defs
import Silmaril.Proofs.Wasm.Cfg.Exec

@[expose] public section

/-!
# The position invariant: first facts

* `resid_start`: a body's code on entry (`expression body`) is at its first instruction;
* `resid_done`: the values a sequence returns are at its end;
* `inFrame_entry`: the code `Step/call_ref-func` produces for a call of the body is `InFrame`
  at the first instruction.
* `parametric_res` … `aggregate_res`: every rule of the eight non-control reduction families
  (`ParametricStep`, `NumericStep`, `VectorStep`, `VariableStep`, `TableStep`, `MemoryStep`,
  `RefStep`, `AggregateStep`) leaves only values and non-control instructions, or a trap
  (`SimpleRes`). This is the per-family half of milestone 2: a straight-line step never
  creates a label, handler, frame, branch or exception.
* `step_noncontrol`: lifted to `Step` itself (every rule, any host): a Core step from
  `val* a`, `a` of a non-control family, leaves simple code or `val* trap` (`StepRes`).
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

section
variable {H : Type} {P : Numerics.Profile}

theorem parametric_res {l is' : List Admin} (h : ParametricStep l is') : SimpleRes is' :=
  Proofs.Exec.parametric_res h
theorem numeric_res {l is' : List Admin} (h : NumericStep P l is') : SimpleRes is' :=
  Proofs.Exec.numeric_res h
theorem vector_res {l is' : List Admin} (h : VectorStep P l is') : SimpleRes is' :=
  Proofs.Exec.vector_res h
theorem variable_res {c c' : Config H} (h : VariableStep c c') : SimpleRes c'.code :=
  Proofs.Exec.variable_res h
theorem table_res {c c' : Config H} (h : TableStep P c c') : SimpleRes c'.code :=
  Proofs.Exec.table_res h
theorem memory_res {c c' : Config H} (h : MemoryStep P c c') : SimpleRes c'.code :=
  Proofs.Exec.memory_res h
theorem ref_res {c c' : Config H} (h : RefStep c c') : SimpleRes c'.code :=
  Proofs.Exec.ref_res h
theorem aggregate_res {c c' : Config H} (h : AggregateStep c c') : SimpleRes c'.code :=
  Proofs.Exec.aggregate_res h

/-- **A straight-line step leaves straight-line code or a trap**: any Core 3.0 step (any host)
from `val* a` with `a` of a non-control family. -/
theorem step_noncontrol {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    (us : List Val) (a : Admin) (hc : c.code = vals us ++ [a])
    (hk : SingleThreaded.Det.famOf a ≠ .control) : StepRes c'.code :=
  Proofs.Exec.step_noncontrol h us a hc hk

end

end Silmaril.Wasm.Cfg
