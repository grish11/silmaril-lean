module

public import Silmaril.Wasm.Cfg.ExampleExitStack.Defs
public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Wasm.Validation.Check.Validate
import Silmaril.Proofs.Wasm.Cfg.ExampleExitStack

@[expose] public section

/-!
# Leaving the function from inside a block: regression fixtures

The machine's exit state carries the whole frame stack (`Machine.brVals`: the label frames'
outer values under the block's), so the function's answer, its top result values, is read off
the exit state. For the valid bodies of `exitMod` (type `[] → [i32 i32]`, the value `1` pushed
outside a block) and every profile, host and oracle:

* `machine_ret`, `machine_br`, `machine_brIf_taken`, `machine_table`: `return`, `br 1`, a taken
  `br_if 1` and `br_table [1] 1` from inside the block exit with `1, 2, 3`; Core 3.0 returns the
  top two, `2, 3` (`core_ret`, `core_br`, `core_brIf_taken`, `core_table`);
* `machine_brIf_not`: the untaken `br_if` falls through both sequences and exits with `4, 5`,
  Core's answer (`core_brIf_not`).

`bodyLoss` (`i32.const 1; block (i32.const 2; return)`) is not valid (`lossMod_invalid`), but
Core 3.0 returns `1, 2` (`core_loss`): the values `return` takes reach below the block. The
machine exits with `1, 2` (`machine_loss`); an exit keeping only the block's own stack would have
lost the `1`. This is about the exit state only: untyped code is not claimed in general (pending
tail calls need `Region.TailWF`).
-/

namespace Silmaril.Wasm.Cfg.ExampleExitStack

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Cfg.Machine

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

theorem exitMod_valid : (Validation.validate? exitMod).isSome = true :=
  Proofs.ExampleExitStack.exitMod_valid

theorem lossMod_invalid :
    (Validation.validate? ({ types := [resI32x2], funcs := [⟨⟨0⟩, [], bodyLoss⟩] } : Module)).isSome =
      false := Proofs.ExampleExitStack.lossMod_invalid

theorem machine_ret (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C bodyRet) (initial bodyRet s f)
      ⟨.exit, [.i32 1, .i32 2, .i32 3], [], s, f⟩ := Proofs.ExampleExitStack.machine_ret s f

theorem machine_br (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C bodyBr) (initial bodyBr s f)
      ⟨.exit, [.i32 1, .i32 2, .i32 3], [], s, f⟩ := Proofs.ExampleExitStack.machine_br s f

theorem machine_brIf_taken (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C (bodyBrIf 1)) (initial (bodyBrIf 1) s f)
      ⟨.exit, [.i32 1, .i32 2, .i32 3], [], s, f⟩ := Proofs.ExampleExitStack.machine_brIf_taken s f

theorem machine_brIf_not (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C (bodyBrIf 0)) (initial (bodyBrIf 0) s f)
      ⟨.exit, [.i32 4, .i32 5], [], s, f⟩ := Proofs.ExampleExitStack.machine_brIf_not s f

theorem machine_table (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C bodyTable) (initial bodyTable s f)
      ⟨.exit, [.i32 1, .i32 2, .i32 3], [], s, f⟩ := Proofs.ExampleExitStack.machine_table s f

theorem machine_loss (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C bodyLoss) (initial bodyLoss s f)
      ⟨.exit, [.i32 1, .i32 2], [], s, f⟩ := Proofs.ExampleExitStack.machine_loss s f

theorem core_ret (s : Store H) (f g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression bodyRet)]]⟩
      ⟨s, g, vals [.i32 2, .i32 3]⟩ := Proofs.ExampleExitStack.core_ret s f g

theorem core_br (s : Store H) (f g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression bodyBr)]]⟩
      ⟨s, g, vals [.i32 2, .i32 3]⟩ := Proofs.ExampleExitStack.core_br s f g

theorem core_brIf_taken (s : Store H) (f g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression (bodyBrIf 1))]]⟩
      ⟨s, g, vals [.i32 2, .i32 3]⟩ := Proofs.ExampleExitStack.core_brIf_taken s f g

theorem core_brIf_not (s : Store H) (f g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression (bodyBrIf 0))]]⟩
      ⟨s, g, vals [.i32 4, .i32 5]⟩ := Proofs.ExampleExitStack.core_brIf_not s f g

theorem core_table (s : Store H) (f g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression bodyTable)]]⟩
      ⟨s, g, vals [.i32 2, .i32 3]⟩ := Proofs.ExampleExitStack.core_table s f g

theorem core_loss (s : Store H) (f g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression bodyLoss)]]⟩
      ⟨s, g, vals [.i32 1, .i32 2]⟩ := Proofs.ExampleExitStack.core_loss s f g

end Silmaril.Wasm.Cfg.ExampleExitStack
