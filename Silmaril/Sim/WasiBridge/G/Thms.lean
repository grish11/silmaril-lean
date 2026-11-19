module

public import Silmaril.Proofs.Sim.WasiBridge.G.Hello
public import Silmaril.Proofs.Sim.WasiBridge.G.Steps
public import Silmaril.Proofs.Sim.WasiBridge.G.Lps

/-!
# The G simulator with `syscall`, and hello world end to end: results

Definitions in `Silmaril.Sim.WasiBridge.G.Defs`; proofs in `Silmaril.Proofs.Sim.WasiBridge.G.*`.

* **`enc_sysStore`**: the `syscall` method (calls of the opaque imports `sys.syscall`,
  `nd.undef`) is sound for LPS's syscall step: the store after it encodes the core LPS resumes
  with, for every flag completion.
* **`procRun_wrun`**: every run of LPS's x86 user machine with an `EnvS1` environment, on a
  program of G instructions and syscalls, is an interaction run of the simulator code with the
  `sys2wasi` adapter's answers, with the same observables (up to the end of the program).
* **`hello_wrun`**: every interaction run of the simulator code of `hello` produces a prefix of
  "write `msg.take k` to fd 1, exit 0".
* **`hello_equiv`**: for the actual bytes of `hello` (`examples/wasm-sim/wasi-bridge/progs/
  hello-g.S`): process ≡ simulator runs ≡ WASI hello (`ElfWasiEquiv … helloWasi S1`), for every
  environment meeting `EnvS1`.

* **`sys_steps`**, **`wrun_steps`**: the interaction runs are runs of the Wasm small-step
  semantics (`Silmaril.Wasm.Execution.Core.Step`; the imports are host functions of the relation
  `s1Host mem`: `sys.syscall` answers as `sys2wasi`, `nd.undef` anything).

* **`lpsEnv_S1`**: LPS's proved syscall arms (`IoSpec.lpsEnv`: exit, write, read) meet `EnvS1`;
  **`hello_equiv_lps`**: `hello_equiv` under LPS's Linux model, with no environment assumption.
-/

/-- info: 'Silmaril.Sim.WasiBridge.G.hello_equiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.WasiBridge.G.hello_equiv

/-- info: 'Silmaril.Sim.WasiBridge.G.procRun_wrun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.WasiBridge.G.procRun_wrun

/-- info: 'Silmaril.Sim.WasiBridge.G.wrun_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.WasiBridge.G.wrun_steps

/-- info: 'Silmaril.Sim.WasiBridge.G.hello_equiv_lps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Silmaril.Sim.WasiBridge.G.hello_equiv_lps
