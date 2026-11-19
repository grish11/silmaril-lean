module

public import Silmaril.Wasm.Cfg.ExampleCatchExit.Defs
public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Wasm.Validation.Check.Validate
import Silmaril.Proofs.Wasm.Cfg.ExampleCatchExit

@[expose] public section

/-!
# Leaving the function through a caught exception: regression fixtures

CHECKED (standard axioms) for the machine exit by a caught exception branching to the function
label (`MStepC.catchOut`), the exit case the whole-frame-stack correction covers with no
fixture so far. The tag hypotheses: tag `0` of the frame's module is the store tag `ta`, whose
type expands to `ts → []` with two parameters; they hold at the instance of `catchMod`
(`catch_tag`).

* `catchMod_valid`: the module validates (typed clauses carry exactly the label's values).
* `machine_catch`: the machine exits `bodyCatch` with the whole stack `1, 3, 4` (the
  `try_table`'s outer value under the payload), in the store with the new exception.
* `machine_catchNest`: the machine exits `bodyCatchNest` with the whole stack `1, 2, 3, 4` (the
  outer values of the `try_table` and of the enclosing block it leaves).
* `core_catch`, `core_catchNest`: Core 3.0 returns the top two values `3, 4` from the function's
  frame, in the same store.

Not claimed: exception handling at the function or session level. These bodies are outside the
`tExt`-checked fragment of `Function` and `Session`; covering exceptions there is the XP/EH
extension.
-/

namespace Silmaril.Wasm.Cfg.ExampleCatchExit

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
  {s : Store H} {f : Frame} {ta : Nat} {ti : TagInst} {ts : Validation.Ty (.list .val)}

theorem catchMod_valid : (Validation.validate? catchMod).isSome = true :=
  Proofs.ExampleCatchExit.catchMod_valid

/-- **The tag hypotheses hold at the instance of `catchMod`.** -/
theorem catch_tag : ∃ (ta : Nat) (ti : TagInst) (ts : Validation.Ty (.list .val)),
    catchMI.tags[0]? = some ta ∧ catchStore.tags[ta]? = some ti ∧
    Validation.Expand ti.type (.func ts .nil) ∧ ts.length = 2 :=
  Proofs.ExampleCatchExit.catch_tag

/-- **`bodyCatch`: the exit stack is `1, 3, 4`.** -/
theorem machine_catch (hmod : f.module.tags[0]? = some ta) (hti : s.tags[ta]? = some ti)
    (hexp : Validation.Expand ti.type (.func ts .nil)) (hts : ts.length = 2) :
    Relation.ReflTransGen (MStepC P host C bodyCatch) (initial bodyCatch s f)
      ⟨.exit, [.i32 1, .i32 3, .i32 4], [], s.addExn ⟨ta, [.i32 3, .i32 4]⟩, f⟩ :=
  Proofs.ExampleCatchExit.machine_catch hmod hti hexp hts

/-- **`bodyCatchNest`: the exit stack is the whole frame stack `1, 2, 3, 4`.** -/
theorem machine_catchNest (hmod : f.module.tags[0]? = some ta) (hti : s.tags[ta]? = some ti)
    (hexp : Validation.Expand ti.type (.func ts .nil)) (hts : ts.length = 2) :
    Relation.ReflTransGen (MStepC P host C bodyCatchNest) (initial bodyCatchNest s f)
      ⟨.exit, [.i32 1, .i32 2, .i32 3, .i32 4], [], s.addExn ⟨ta, [.i32 3, .i32 4]⟩, f⟩ :=
  Proofs.ExampleCatchExit.machine_catchNest hmod hti hexp hts

/-- **`bodyCatch` returns `3, 4` in Core 3.0.** -/
theorem core_catch (hmod : f.module.tags[0]? = some ta) (hti : s.tags[ta]? = some ti)
    (hexp : Validation.Expand ti.type (.func ts .nil)) (hts : ts.length = 2) (g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression bodyCatch)]]⟩
      ⟨s.addExn ⟨ta, [.i32 3, .i32 4]⟩, g, vals [.i32 3, .i32 4]⟩ :=
  Proofs.ExampleCatchExit.core_catch hmod hti hexp hts g

/-- **`bodyCatchNest` returns `3, 4` in Core 3.0.** -/
theorem core_catchNest (hmod : f.module.tags[0]? = some ta) (hti : s.tags[ta]? = some ti)
    (hexp : Validation.Expand ti.type (.func ts .nil)) (hts : ts.length = 2) (g : Frame) :
    Steps P host ⟨s, g, [.frame 2 f [.label 2 [] (expression bodyCatchNest)]]⟩
      ⟨s.addExn ⟨ta, [.i32 3, .i32 4]⟩, g, vals [.i32 3, .i32 4]⟩ :=
  Proofs.ExampleCatchExit.core_catchNest hmod hti hexp hts g

end Silmaril.Wasm.Cfg.ExampleCatchExit
