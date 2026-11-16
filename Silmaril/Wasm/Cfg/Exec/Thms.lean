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
* `resid_at_step`: at position `j` of a sequence whose instruction `j` is non-control, a Core
  step stays at `j` mid-instruction or exits by trap.
* `resid_mid_step`: mid-instruction, either only values are left (the position is `j + 1`), or a
  step stays mid-instruction or exits by trap.

  These two are stated for code that *is* the sequence's residual. Lifting them through
  enclosing `LABEL`/`HANDLER` contexts, and the control instructions, is the rest of
  milestone 2.
* **Entering structured instructions** (milestone 3a): at a `block`, `loop` or `try_table`
  the only step enters arm `0` at its start (`resid_at_block_step`, `…_loop_…`,
  `…_tryTable_…`); at an `if` it chooses an arm (`resid_at_if_step`), and the next step enters
  it (`resid_ifArm_step`). Store and frame are unchanged. These are proved against `Step`
  through the inversions of `Execution.Core.Inversion`.
* **Falling out of an arm** (`resid_inArm_done_step`): when a `block`, `loop` or `if` arm has
  run to its end, the step leaves the label, to the instruction after it.
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

/-- **Straight-line progress at a position**: a step of non-control instruction `j` stays at `j`
(mid-instruction) or exits by trap. -/
theorem resid_at_step {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    {is : List Instr} {j : Nat} {i : Instr} (hi : is[j]? = some i)
    (hk : SingleThreaded.Det.famOf (.plain i) ≠ .control) (hr : Resid is (.at j) c.code) :
    Resid is (.mid j) c'.code ∨ Resid is .exiting c'.code :=
  Proofs.Exec.resid_at_step h hi hk hr

/-- **Mid-instruction**: only values left (the position is `j + 1`), or a step stays
mid-instruction or exits by trap. -/
theorem resid_mid_step {host : HostSemantics H} {is : List Instr} {j : Nat} {code : List Admin}
    (hr : Resid is (.mid j) code) :
    Resid is (.at (j + 1)) code ∨
      ∀ {c c' : Config H}, c.code = code → Step P host c c' →
        Resid is (.mid j) c'.code ∨ Resid is .exiting c'.code :=
  Proofs.Exec.resid_mid_step hr

/-- **Entering a block**: the step from a `block` enters its body at the start. -/
theorem resid_at_block_step {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    {is b : List Instr} {j : Nat} {bt : BlockType} (hi : is[j]? = some (.block bt b))
    (hr : Resid is (.at j) c.code) :
    Resid is (.inArm j 0 (.at 0)) c'.code ∧ c'.store = c.store ∧ c'.frame = c.frame :=
  Proofs.Exec.resid_at_block_step h hi hr

/-- **Entering a loop**: the step from a `loop` enters its body at the start. -/
theorem resid_at_loop_step {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    {is b : List Instr} {j : Nat} {bt : BlockType} (hi : is[j]? = some (.loop bt b))
    (hr : Resid is (.at j) c.code) :
    Resid is (.inArm j 0 (.at 0)) c'.code ∧ c'.store = c.store ∧ c'.frame = c.frame :=
  Proofs.Exec.resid_at_loop_step h hi hr

/-- **Entering a `try_table`**: its handler and label are installed, at the body's start. -/
theorem resid_at_tryTable_step {host : HostSemantics H} {c c' : Config H}
    (h : Step P host c c') {is b : List Instr} {j : Nat} {bt : BlockType} {cs : List Catch}
    (hi : is[j]? = some (.tryTable bt cs b)) (hr : Resid is (.at j) c.code) :
    Resid is (.inArm j 0 (.at 0)) c'.code ∧ c'.store = c.store ∧ c'.frame = c.frame :=
  Proofs.Exec.resid_at_tryTable_step h hi hr

/-- **`if` chooses an arm**: the step pops the condition and leaves the chosen arm as a
`block`. -/
theorem resid_at_if_step {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    {is t e : List Instr} {j : Nat} {bt : BlockType} (hi : is[j]? = some (.if_ bt t e))
    (hr : Resid is (.at j) c.code) :
    ∃ a, Resid is (.ifArm j a) c'.code ∧ c'.store = c.store ∧ c'.frame = c.frame :=
  Proofs.Exec.resid_at_if_step h hi hr

/-- **Entering the chosen arm** of an `if`. -/
theorem resid_ifArm_step {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    {is : List Instr} {k a : Nat} (hr : Resid is (.ifArm k a) c.code) :
    Resid is (.inArm k a (.at 0)) c'.code ∧ c'.store = c.store ∧ c'.frame = c.frame :=
  Proofs.Exec.resid_ifArm_step h hr

/-- **Falling out of an arm**: a `block`, `loop` or `if` arm run to its end (`m` its length)
steps out of its label to the next instruction (`label-vals`). -/
theorem resid_inArm_done_step {host : HostSemantics H} {c c' : Config H} (h : Step P host c c')
    {is : List Instr} {k a m : Nat}
    (hlen : ∀ i b, is[k]? = some i → armOf i a = some b → m = b.length)
    (hnt : ∀ bt cs b, is[k]? ≠ some (.tryTable bt cs b))
    (hr : Resid is (.inArm k a (.at m)) c.code) :
    Resid is (.at (k + 1)) c'.code ∧ c'.store = c.store ∧ c'.frame = c.frame :=
  Proofs.Exec.resid_inArm_done_step h hlen hnt hr

end

end Silmaril.Wasm.Cfg
