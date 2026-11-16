module

public import Silmaril.Project.Shapes.WasmWast.Defs
import Silmaril.Proofs.Project.Shapes.WasmWast

/-!
# Standard problem shapes: WAST script commands (transfer lemmas)

* `ScriptHolds.of_kernel h`: every command of the script `m`, `cmds` holds, from one kernel
  evaluation `h : scriptK o fuel m cmds = true` (`decide +kernel`). The kernel validates and
  instantiates `m` and runs the commands in order with the kernel-evaluable interpreter
  `runInvokeK`; the claims are about Core reduction, through the interpreter's soundness and
  stopping theorems and determinism at `profile o`.
* `ScriptHolds.returnsOnly`, `ScriptHolds.trapsOnly`: the row of command `k`.
* `ReturnsOnly.returns`, `TrapsOnly.traps`: the weaker existence shapes;
  `ReturnsOnly.not_traps`, `TrapsOnly.not_returns`: an `…_only` claim excludes the other
  outcome.
* `Only.unique`: under `profile o`, a script and an action have at most one outcome.

Proofs: `Silmaril.Proofs.Project.Shapes.WasmWast`.
-/

@[expose] public section

namespace Silmaril.Project.Shapes.WasmWast

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded

/-- **Every command of a script, from one kernel evaluation.** -/
theorem ScriptHolds.of_kernel {o : GrowOracle} {fuel : Nat} {m : Module} {cmds : List Cmd}
    (h : scriptK o fuel m cmds = true) : ScriptHolds o m cmds :=
  Silmaril.Proofs.Project.Shapes.WasmWast.scriptHolds_of_kernel h

/-- The row of an `assert_return` command `k`. -/
theorem ScriptHolds.returnsOnly {o : GrowOracle} {m : Module} {cmds : List Cmd}
    (h : ScriptHolds o m cmds) (k : Nat) {act : Action} {vs : List Val}
    (hk : cmds[k]? = some ⟨act, some (.values vs)⟩) : ReturnsOnly o m (pre cmds k) act vs :=
  h k _ hk

/-- The row of an `assert_trap` command `k`. -/
theorem ScriptHolds.trapsOnly {o : GrowOracle} {m : Module} {cmds : List Cmd}
    (h : ScriptHolds o m cmds) (k : Nat) {act : Action}
    (hk : cmds[k]? = some ⟨act, some .trap⟩) : TrapsOnly o m (pre cmds k) act :=
  h k _ hk

theorem ReturnsOnly.returns {o : GrowOracle} {m : Module} {pre : List Action} {act : Action}
    {vs : List Val} (h : ReturnsOnly o m pre act vs) : Returns o m pre act vs := h.1

theorem TrapsOnly.traps {o : GrowOracle} {m : Module} {pre : List Action} {act : Action}
    (h : TrapsOnly o m pre act) : Traps o m pre act := h.1

/-- If every normal form has the outcome `r` and some normal form has `r'`, then `r' = r`. -/
theorem Only.unique {o : GrowOracle} {m : Module} {pre : List Action} {act : Action}
    {r r' : Result} (h : Only o m pre act r) (h' : Reaches o m pre act r') : r' = r := by
  obtain ⟨mi, s, a, c, hS, ha, hc, hr⟩ := h'
  have := h mi s a c hS ha hc
  rw [hr] at this
  exact Option.some.inj this

theorem ReturnsOnly.not_traps {o : GrowOracle} {m : Module} {pre : List Action} {act : Action}
    {vs : List Val} (h : ReturnsOnly o m pre act vs) : ¬ Traps o m pre act :=
  fun ht => nomatch h.2.unique ht

theorem TrapsOnly.not_returns {o : GrowOracle} {m : Module} {pre : List Action} {act : Action}
    {vs : List Val} (h : TrapsOnly o m pre act) : ¬ Returns o m pre act vs :=
  fun hr => nomatch h.2.unique hr

end Silmaril.Project.Shapes.WasmWast

end
