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

**The block-CFG machine is stuck there** (the regression these fixtures record): its branch rules
need a label frame for the target (`ls[l]? = some L`), and the function label has none, so

* `machine_stuck0`, `machine_stuck1`, `machine_stuck4`: from the CFG entry of `body0`, `body1`,
  `body4` the machine has no step, and so reaches no sink (`machine_no_sink0` …);
* `machine_enter3`, `machine_stuck3`: `body3` enters its block and is then stuck at the
  `br_table` whose target is the function label.

`body2` is the control: its `br_if` is not taken. These are statements about the machine as it is
defined now; the fix (a transition to `exit` for a branch whose depth is the function boundary)
is to restate them as machine runs to `exit` with Core's results.
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

theorem machine_stuck0 (s : Store H) (f : Frame) (st' : MState H) :
    ¬ MStepC P host C body0 (initial body0 s f) st' := Proofs.ExampleBrOut.stuck0 s f st'

theorem machine_stuck1 (s : Store H) (f : Frame) (st' : MState H) :
    ¬ MStepC P host C body1 (initial body1 s f) st' := Proofs.ExampleBrOut.stuck1 s f st'

theorem machine_stuck4 (s : Store H) (f : Frame) (st' : MState H) :
    ¬ MStepC P host C body4 (initial body4 s f) st' := Proofs.ExampleBrOut.stuck4 s f st'

theorem machine_no_sink0 (s : Store H) (f : Frame) (st' : MState H)
    (h : Relation.ReflTransGen (MStepC P host C body0) (initial body0 s f) st') :
    ¬ st'.node.IsSink :=
  Proofs.ExampleBrOut.no_sink_of_stuck (Proofs.ExampleBrOut.stuck0 s f)
    (Proofs.ExampleBrOut.initial_not_sink body0 _ rfl s f) st' h

theorem machine_no_sink1 (s : Store H) (f : Frame) (st' : MState H)
    (h : Relation.ReflTransGen (MStepC P host C body1) (initial body1 s f) st') :
    ¬ st'.node.IsSink :=
  Proofs.ExampleBrOut.no_sink_of_stuck (Proofs.ExampleBrOut.stuck1 s f)
    (Proofs.ExampleBrOut.initial_not_sink body1 _ rfl s f) st' h

theorem machine_no_sink4 (s : Store H) (f : Frame) (st' : MState H)
    (h : Relation.ReflTransGen (MStepC P host C body4) (initial body4 s f) st') :
    ¬ st'.node.IsSink :=
  Proofs.ExampleBrOut.no_sink_of_stuck (Proofs.ExampleBrOut.stuck4 s f)
    (Proofs.ExampleBrOut.initial_not_sink body4 _ rfl s f) st' h

theorem machine_enter3 (s : Store H) (f : Frame) :
    MStepC P host C body3 (initial body3 s f)
      ⟨.block ⟨[(0, 0)], 0⟩, [], [frame3], s, f⟩ :=
  Proofs.ExampleBrOut.enter3 s f

theorem machine_stuck3 (s : Store H) (f : Frame) (st' : MState H) :
    ¬ MStepC P host C body3 ⟨.block ⟨[(0, 0)], 0⟩, [], [frame3], s, f⟩ st' :=
  Proofs.ExampleBrOut.stuck3 s f st'

end Silmaril.Wasm.Cfg.ExampleBrOut
