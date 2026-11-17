module

public import Silmaril.Wasm.Cfg.ExampleNested.Defs
public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Wasm.Validation.Check.Validate
import Silmaril.Proofs.Wasm.Cfg.ExampleNested

@[expose] public section

/-!
# Validated typed nested fixtures for the block-CFG machines

On the three bodies of the validated module `nestMod` (`nestMod_valid`), the logged machine
`MStepL` (`MRunL`, native stack conventions, no call so the log is `[]`) and the Core-convention
machine `MStepC` (every profile, host and call oracle) run from the CFG entry to the **same**
`exit` state, stack, store and frame included:

* `bodyNest` (`block`, `loop`, `if`; a `br 2` from the `if` arm leaves the `if` and the `loop`
  for the `block`): exit stack `9, 42` (`nest_logged`, `nest_core`, `nest_agree`).
* `bodyLoops` (nested loops; the inner loop's `br_if 1` re-enters the outer loop once, a counter
  in local `0` going `0, 1, 2`): exit stack `2`, frame `frameK 2 mi`, from `frameK 0 mi`
  (`loops_logged`, `loops_core`, `loops_agree`). Both runs take the outer re-entry
  (`loops_logged_via`, `loops_core_via`): a step from the inner loop's body `innerAt s 0 mi`
  (frames `[loop, loop]`) to the outer loop's body `outerAt s 1 mi` (frames `[loop]`).
* `bodyTry` (`try_table (catch 0 0)` around a nested `block` whose `throw 0` it catches; the
  clause branches to the outer `block`, then `i32.add`): exit stack `4`, in the store with the
  new exception (`try_logged`, `try_core`, `try_agree`). The tag hypotheses (tag `0` of the
  frame's module is the store tag `ta`, of type `[i32] → []`) hold at the instance of `nestMod`
  (`nest_tag`).

The exit stacks agree exactly, not only on their top result values: no fixture leaves the
function by a branch, `return` or catch to the function label from inside frames holding outer
values, where `MStepC` keeps them (`brVals`) and `MStepL` does not (`brVals_junk`).

`nest_native`, `loops_native`, `try_native`: by `MachineL.forward_sink`, each body runs natively
(`EvalLXPS` of `liftInstrs body`, empty log) to a flow returning the exit stack (`EndRel`).

These are fixtures, proved by running both machines; they are not derived from the stepwise
projection (`MachineLProj.proj_step`, `proj_initial_closedX`). `bodyTry` is outside the `tExt`-checked fragment (`tExt` rejects `throw` and
`try_table`).
-/

namespace Silmaril.Wasm.Cfg.ExampleNested

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS)

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

theorem nestMod_valid : (Validation.validate? nestMod).isSome = true :=
  Proofs.ExampleNested.nestMod_valid

/-! ## `bodyNest` -/

/-- **The logged machine exits `bodyNest` with `9, 42`.** -/
theorem nest_logged (s : Store H) (f : Frame) :
    MRunL bodyNest (initial bodyNest s f) [] ⟨.exit, [.i32 9, .i32 42], [], s, f⟩ :=
  Proofs.ExampleNested.nest_logged s f

/-- **The Core machine exits `bodyNest` with `9, 42`.** -/
theorem nest_core (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C bodyNest) (initial bodyNest s f)
      ⟨.exit, [.i32 9, .i32 42], [], s, f⟩ :=
  Proofs.ExampleNested.nest_core s f

/-- **Both machines reach the same exit state on `bodyNest`.** -/
theorem nest_agree (s : Store H) (f : Frame) :
    ∃ st : MState H, st.node = .exit ∧ st.stk = [.i32 9, .i32 42] ∧
      MRunL bodyNest (initial bodyNest s f) [] st ∧
      Relation.ReflTransGen (MStepC P host C bodyNest) (initial bodyNest s f) st :=
  ⟨_, rfl, rfl, nest_logged s f, nest_core s f⟩

/-- **`bodyNest` runs natively to a flow returning `9, 42`.** -/
theorem nest_native (s : Store H) (f : Frame) :
    ∃ r, EvalLXPS s f [] (liftInstrs bodyNest) [] r ∧
      EndRel (⟨.exit, [.i32 9, .i32 42], [], s, f⟩ : MState H) r :=
  forward_sink (nest_logged s f) trivial

/-! ## `bodyLoops` -/

/-- **The logged machine exits `bodyLoops` with the counter `2`.** -/
theorem loops_logged (s : Store H) (mi : ModuleInst) :
    MRunL bodyLoops (initial bodyLoops s (frameK 0 mi)) [] ⟨.exit, [.i32 2], [], s, frameK 2 mi⟩ :=
  Proofs.ExampleNested.loops_logged s mi

/-- **The Core machine exits `bodyLoops` with the counter `2`.** -/
theorem loops_core (s : Store H) (mi : ModuleInst) :
    Relation.ReflTransGen (MStepC P host C bodyLoops) (initial bodyLoops s (frameK 0 mi))
      ⟨.exit, [.i32 2], [], s, frameK 2 mi⟩ :=
  Proofs.ExampleNested.loops_core s mi

/-- **The logged run takes the outer re-entry**: it reaches the inner loop's body on the counter
`0` (frames `[loop, loop]`), steps from there to the outer loop's body on the counter `1`
(frames `[loop]`, the inner loop's `br_if 1` to the outer label), and then exits. -/
theorem loops_logged_via (s : Store H) (mi : ModuleInst) :
    MRunL bodyLoops (initial bodyLoops s (frameK 0 mi)) [] (innerAt s 0 mi) ∧
      MStepL bodyLoops (innerAt s 0 mi) [] (outerAt s 1 mi) ∧
      MRunL bodyLoops (outerAt s 1 mi) [] ⟨.exit, [.i32 2], [], s, frameK 2 mi⟩ :=
  Proofs.ExampleNested.loops_logged_via s mi

/-- **The Core run takes the outer re-entry**, through the same states. -/
theorem loops_core_via (s : Store H) (mi : ModuleInst) :
    Relation.ReflTransGen (MStepC P host C bodyLoops) (initial bodyLoops s (frameK 0 mi))
        (innerAt s 0 mi) ∧
      MStepC P host C bodyLoops (innerAt s 0 mi) (outerAt s 1 mi) ∧
      Relation.ReflTransGen (MStepC P host C bodyLoops) (outerAt s 1 mi)
        ⟨.exit, [.i32 2], [], s, frameK 2 mi⟩ :=
  Proofs.ExampleNested.loops_core_via s mi

/-- **Both machines reach the same exit state on `bodyLoops`.** -/
theorem loops_agree (s : Store H) (mi : ModuleInst) :
    ∃ st : MState H, st.node = .exit ∧ st.stk = [.i32 2] ∧
      MRunL bodyLoops (initial bodyLoops s (frameK 0 mi)) [] st ∧
      Relation.ReflTransGen (MStepC P host C bodyLoops) (initial bodyLoops s (frameK 0 mi)) st :=
  ⟨_, rfl, rfl, loops_logged s mi, loops_core s mi⟩

/-- **`bodyLoops` runs natively to a flow returning `2`.** -/
theorem loops_native (s : Store H) (mi : ModuleInst) :
    ∃ r, EvalLXPS s (frameK 0 mi) [] (liftInstrs bodyLoops) [] r ∧
      EndRel (⟨.exit, [.i32 2], [], s, frameK 2 mi⟩ : MState H) r :=
  forward_sink (loops_logged s mi) trivial

/-! ## `bodyTry` -/

/-- **The tag hypotheses hold at the instance of `nestMod`.** -/
theorem nest_tag : ∃ (ta : Nat) (ti : TagInst) (ts : Validation.Ty (.list .val)),
    nestMI.tags[0]? = some ta ∧ nestStore.tags[ta]? = some ti ∧
    Validation.Expand ti.type (.func ts .nil) ∧ ts.length = 1 :=
  Proofs.ExampleNested.nest_tag

section Tag

variable {s : Store H} {f : Frame} {ta : Nat} {ti : TagInst} {ts : Validation.Ty (.list .val)}

/-- **The logged machine exits `bodyTry` with `4`**, in the store with the caught exception. -/
theorem try_logged (hmod : f.module.tags[0]? = some ta) (hti : s.tags[ta]? = some ti)
    (hexp : Validation.Expand ti.type (.func ts .nil)) (hts : ts.length = 1) :
    MRunL bodyTry (initial bodyTry s f) [] ⟨.exit, [.i32 4], [], s.addExn ⟨ta, [.i32 3]⟩, f⟩ :=
  Proofs.ExampleNested.try_logged hmod hti hexp hts

/-- **The Core machine exits `bodyTry` with `4`**, in the store with the caught exception. -/
theorem try_core (hmod : f.module.tags[0]? = some ta) (hti : s.tags[ta]? = some ti)
    (hexp : Validation.Expand ti.type (.func ts .nil)) (hts : ts.length = 1) :
    Relation.ReflTransGen (MStepC P host C bodyTry) (initial bodyTry s f)
      ⟨.exit, [.i32 4], [], s.addExn ⟨ta, [.i32 3]⟩, f⟩ :=
  Proofs.ExampleNested.try_core hmod hti hexp hts

/-- **Both machines reach the same exit state on `bodyTry`.** -/
theorem try_agree (hmod : f.module.tags[0]? = some ta) (hti : s.tags[ta]? = some ti)
    (hexp : Validation.Expand ti.type (.func ts .nil)) (hts : ts.length = 1) :
    ∃ st : MState H, st.node = .exit ∧ st.stk = [.i32 4] ∧
      MRunL bodyTry (initial bodyTry s f) [] st ∧
      Relation.ReflTransGen (MStepC P host C bodyTry) (initial bodyTry s f) st :=
  ⟨_, rfl, rfl, try_logged hmod hti hexp hts, try_core hmod hti hexp hts⟩

/-- **`bodyTry` runs natively to a flow returning `4`.** -/
theorem try_native (hmod : f.module.tags[0]? = some ta) (hti : s.tags[ta]? = some ti)
    (hexp : Validation.Expand ti.type (.func ts .nil)) (hts : ts.length = 1) :
    ∃ r, EvalLXPS s f [] (liftInstrs bodyTry) [] r ∧
      EndRel (⟨.exit, [.i32 4], [], s.addExn ⟨ta, [.i32 3]⟩, f⟩ : MState H) r :=
  forward_sink (try_logged hmod hti hexp hts) trivial

end Tag

end Silmaril.Wasm.Cfg.ExampleNested
