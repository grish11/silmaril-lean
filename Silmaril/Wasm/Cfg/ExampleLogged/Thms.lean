module

public import Silmaril.Wasm.Cfg.ExampleLogged.Defs
public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Wasm.Cfg.Machine.Thms
import Silmaril.Proofs.Wasm.Cfg.ExampleLogged

@[expose] public section

/-!
# The logged machine: native against Core conventions (regression fixtures)

On the invalid body `bodyExtra` (`block (i32.const 1; i32.const 2); i32.const 3`, empty block
type), the two machines part:

* `logged_run`: the logged machine `MStepL` (native conventions) runs from the CFG entry to `exit`
  with the stack `3`, logging no call; `logged_native`: by `MachineL.forward_sink`, the body runs
  natively (`EvalLXPS`) to a flow returning `3`.
* `core_run`: the Core machine `MStepC` runs to `exit` with the whole stack `1, 2, 3`.

No untyped correspondence between `MStepL` and `MStepC` is claimed; on valid code they agree
(the typed projection is separate work).
-/

namespace Silmaril.Wasm.Cfg.ExampleLogged

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS)

variable {H : Type}

/-- **The logged machine exits with `3`.** -/
theorem logged_run (s : Store H) (f : Frame) :
    MRunL bodyExtra (initial bodyExtra s f) [] ⟨.exit, [.i32 3], [], s, f⟩ :=
  Proofs.ExampleLogged.logged_run s f

/-- **The body runs natively to a flow returning `3`**, with no open call. -/
theorem logged_native (s : Store H) (f : Frame) :
    ∃ r, EvalLXPS s f [] (liftInstrs bodyExtra) [] r ∧
      EndRel (⟨.exit, [.i32 3], [], s, f⟩ : MState H) r :=
  Proofs.ExampleLogged.logged_native s f

/-- **The Core machine exits with `1, 2, 3`.** -/
theorem core_run {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H} (s : Store H)
    (f : Frame) :
    Relation.ReflTransGen (MStepC P host C bodyExtra) (initial bodyExtra s f)
      ⟨.exit, [.i32 1, .i32 2, .i32 3], [], s, f⟩ :=
  Proofs.ExampleLogged.core_run s f

end Silmaril.Wasm.Cfg.ExampleLogged
