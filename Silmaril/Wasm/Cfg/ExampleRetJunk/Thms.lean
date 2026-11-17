module

public import Silmaril.Wasm.Cfg.ExampleRetJunk.Defs
public import Silmaril.Wasm.Cfg.MachineL.Thms
public import Silmaril.Wasm.Cfg.Machine.Thms
public import Silmaril.Wasm.Cfg.MachineLProj.Thms
public import Silmaril.Wasm.Validation.Check.Validate
import Silmaril.Proofs.Wasm.Cfg.ExampleRetJunk

@[expose] public section

/-!
# A validated exit from a frame holding outer values

`retMod` validates (`retMod_valid`). In `bodyRet` (`[] → [i32]`), the `return` leaves the `block`
whose label frame holds the outer value `1`:

* the logged machine exits with the branch-site stack `2` (`ret_logged`; natively, a `return` of
  `2`, `ret_native`);
* `MStepC` exits with `1, 2` (`ret_core`), keeping the outer value of the frame left
  (`brVals`).

The two exit states are **different** (`ret_ne`). They are related by the stepwise projection's
`ProjRel`, with the junk `1` (`ret_projRel`), and agree on the function's result, the top value
(`ret_top`).

So the junk case of `ProjRel` (`MachineLProj.brVals_junk`) is reachable on valid, typed code: an
exit through `return` (or a branch to the function label) from inside frames holding outer values.
It is not unreachable under the typed projection invariant. The fixtures of `ExampleNested` do not
reach this case.
-/

namespace Silmaril.Wasm.Cfg.ExampleRetJunk

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Abstract (EvalLXPS)

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

theorem retMod_valid : (Validation.validate? retMod).isSome = true :=
  Proofs.ExampleRetJunk.retMod_valid

/-- **The logged machine exits `bodyRet` with the branch-site stack `2`.** -/
theorem ret_logged (s : Store H) (f : Frame) :
    MRunL bodyRet (initial bodyRet s f) [] ⟨.exit, [.i32 2], [], s, f⟩ :=
  Proofs.ExampleRetJunk.ret_logged s f

/-- **`MStepC` exits `bodyRet` with `1, 2`.** -/
theorem ret_core (s : Store H) (f : Frame) :
    Relation.ReflTransGen (MStepC P host C bodyRet) (initial bodyRet s f)
      ⟨.exit, [.i32 1, .i32 2], [], s, f⟩ :=
  Proofs.ExampleRetJunk.ret_core s f

/-- The two exit states are related by `ProjRel`, with the junk `1`. -/
theorem ret_projRel (s : Store H) (f : Frame) :
    ProjRel (⟨.exit, [.i32 2], [], s, f⟩ : MState H) ⟨.exit, [.i32 1, .i32 2], [], s, f⟩ :=
  Proofs.ExampleRetJunk.ret_projRel s f

/-- **They are different states.** -/
theorem ret_ne (s : Store H) (f : Frame) :
    (⟨.exit, [.i32 2], [], s, f⟩ : MState H) ≠ ⟨.exit, [.i32 1, .i32 2], [], s, f⟩ :=
  Proofs.ExampleRetJunk.ret_ne s f

/-- **They agree on the function's result**, the top value. -/
theorem ret_top : topVals 1 [Val.i32 2] = topVals 1 [Val.i32 1, Val.i32 2] :=
  Proofs.ExampleRetJunk.ret_top

/-- The native run of `bodyRet`: a `return` of `2`. -/
theorem ret_native (s : Store H) (f : Frame) :
    ∃ r, EvalLXPS s f [] (liftInstrs bodyRet) [] r ∧
      EndRel (⟨.exit, [.i32 2], [], s, f⟩ : MState H) r :=
  Proofs.ExampleRetJunk.ret_native s f

end Silmaril.Wasm.Cfg.ExampleRetJunk
