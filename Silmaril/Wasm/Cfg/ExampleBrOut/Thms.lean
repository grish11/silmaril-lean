module

public import Silmaril.Wasm.Cfg.ExampleBrOut.Defs
public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Wasm.Cfg.Region.Thms
public import Silmaril.Wasm.Validation.Check.Validate
import Silmaril.Proofs.Wasm.Cfg.ExampleBrOut

@[expose] public section

/-!
# Branches to the function label: regression fixtures

`brOutMod` validates (`brOutMod_valid`). Each of its five bodies branches to the function label
(`body2` only when its condition is nonzero, which it is not), and the extracted CFG resolves that
label to the `exit` sink (`labels_exit`). Core 3.0 returns the expected results under the function
label `LABEL_n{}` (`core0` … `core4`).

**The block-CFG machine leaves the function there** (the fixed regression: its branch rules used
to need a label frame for the target, and the function label has none, so the machine was stuck;
`MStepC.brOut`, `brIfOut`, `brDataOut` now go to `exit` for a branch whose label index is the
number of frames):

* `machine_exit0`, `machine_exit1`, `machine_exit4`: from the CFG entry of `body0`, `body1`,
  `body4` the machine steps to `exit` with Core's results;
* `machine_enter3`, `machine_exit3`: `body3` enters its block, then its `br_table` steps to `exit`
  with Core's result `5`.

`body2` is the control: its `br_if` is not taken.
-/

namespace Silmaril.Wasm.Cfg.ExampleBrOut

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

theorem brOutMod_valid : (Validation.validate? brOutMod).isSome = true :=
  Proofs.ExampleBrOut.brOutMod_valid

/-- Every fixture's outermost label is the `exit` sink of the extracted CFG. -/
theorem labels_exit :
    labels body0 [] = [.exit] ∧ labels body1 [] = [.exit] ∧ labels body2 [] = [.exit] ∧
      labels body3 [] = [.exit] ∧ labels body4 [] = [.exit] := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem core0 (s : Store H) (f : Frame) :
    Steps P host ⟨s, f, [.label 1 [] (expression body0)]⟩ ⟨s, f, vals [.i32 1]⟩ :=
  Proofs.ExampleBrOut.core0 s f

theorem core1 (s : Store H) (f : Frame) :
    Steps P host ⟨s, f, [.label 1 [] (expression body1)]⟩ ⟨s, f, vals [.i32 7]⟩ :=
  Proofs.ExampleBrOut.core1 s f

theorem core2 (s : Store H) (f : Frame) :
    Steps P host ⟨s, f, [.label 1 [] (expression body2)]⟩ ⟨s, f, vals [.i32 9]⟩ :=
  Proofs.ExampleBrOut.core2 s f

theorem core3 (s : Store H) (f : Frame) :
    Steps P host ⟨s, f, [.label 1 [] (expression body3)]⟩ ⟨s, f, vals [.i32 5]⟩ :=
  Proofs.ExampleBrOut.core3 s f

theorem core4 (s : Store H) (f : Frame) :
    Steps P host ⟨s, f, [.label 2 [] (expression body4)]⟩ ⟨s, f, vals [.i32 1, .i32 2]⟩ :=
  Proofs.ExampleBrOut.core4 s f

/-- **`body0` leaves the function at its `br 0`**: the machine steps from the CFG entry to `exit`
with Core's result `1`. -/
theorem machine_exit0 (s : Store H) (f : Frame) :
    MStepC P host C body0 (initial body0 s f) ⟨.exit, [.i32 1], [], s, f⟩ :=
  Proofs.ExampleBrOut.exit0 s f

/-- **`body1` leaves the function at its taken `br_if`**, with Core's result `7`. -/
theorem machine_exit1 (s : Store H) (f : Frame) :
    MStepC P host C body1 (initial body1 s f) ⟨.exit, [.i32 7], [], s, f⟩ :=
  Proofs.ExampleBrOut.exit1 s f

/-- **`body4` leaves the function at its `br 0`**, with Core's results `1, 2`. -/
theorem machine_exit4 (s : Store H) (f : Frame) :
    MStepC P host C body4 (initial body4 s f) ⟨.exit, [.i32 1, .i32 2], [], s, f⟩ :=
  Proofs.ExampleBrOut.exit4 s f

theorem machine_enter3 (s : Store H) (f : Frame) :
    MStepC P host C body3 (initial body3 s f)
      ⟨.block ⟨[(0, 0)], 0⟩, [], [frame3], s, f⟩ :=
  Proofs.ExampleBrOut.enter3 s f

/-- **`body3` leaves the function from inside its block at the `br_table`**, with Core's result
`5`. -/
theorem machine_exit3 (s : Store H) (f : Frame) :
    MStepC P host C body3 ⟨.block ⟨[(0, 0)], 0⟩, [], [frame3], s, f⟩ ⟨.exit, [.i32 5], [], s, f⟩ :=
  Proofs.ExampleBrOut.exit3 s f

end Silmaril.Wasm.Cfg.ExampleBrOut
