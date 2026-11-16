module

public import Silmaril.Wasm.Interp.Closed.Thms
public import Silmaril.Wasm.Wat

/-!
# Closed modules through the native interpreter: examples

Each example is checked by kernel evaluation (`decide +kernel`; no native evaluation).

* `maxMod`: a supported module. `max_7_3` and `max_neg`: its exact Core behaviours at every
  profile, from `Closed.behaviours_eq`.
* `divMod`: a supported module whose call traps. `div_by_zero`: the behaviour set is exactly
  `{traps}` at every profile (division by zero traps in every profile).
* `floatMod`: **unsupported** (an `f32.add`): `nativeCheck floatMod = false`, so the entry point
  does not apply and nothing is claimed.
* `loopMod`: a call that does not return within the fuel: `run loopMod 50 0 [] = none`. That
  proves nothing (neither divergence nor termination); `behaviours_eq` needs a `some`.
-/

@[expose] public section

namespace Silmaril.Wasm.Interp.Closed.Examples

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Interp.Closed

/-- Signed maximum of two `i32`s. -/
def maxMod : Module := wat3! r#"
(module
  (func (export "max") (param $x i32) (param $y i32) (result i32)
    (select (local.get $x) (local.get $y) (i32.gt_s (local.get $x) (local.get $y)))))
"#

theorem maxMod_export : export? maxMod "max" = some 0 := by decide +kernel

theorem max_7_3 (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost (store maxMod) 0 [Val.i32 7, Val.i32 3] =
      {.returns [Val.i32 7]} :=
  behaviours_eq (fuel := 20) (by decide +kernel) (by decide +kernel) P

theorem max_neg (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost (store maxMod) 0 [Val.i32 (-5), Val.i32 2] =
      {.returns [Val.i32 2]} :=
  behaviours_eq (fuel := 20) (by decide +kernel) (by decide +kernel) P

/-- Unsigned division. -/
def divMod : Module := wat3! r#"
(module
  (func (export "div") (param $x i32) (param $y i32) (result i32)
    (i32.div_u (local.get $x) (local.get $y))))
"#

theorem div_by_zero (P : Numerics.Profile) :
    behaviours P Binaryen.closedHost (store divMod) 0 [Val.i32 1, Val.i32 0] = {.traps} :=
  behaviours_eq (fuel := 20) (by decide +kernel) (by decide +kernel) P

/-- A float addition: outside the native fragment. -/
def floatMod : Module := wat3! r#"
(module
  (func (export "add") (param $x f32) (param $y f32) (result f32)
    (f32.add (local.get $x) (local.get $y))))
"#

theorem floatMod_unsupported : nativeCheck floatMod = false := by decide +kernel

/-- An infinite loop. -/
def loopMod : Module := wat3! r#"
(module
  (func (export "spin") (loop $l (br $l))))
"#

theorem loopMod_checked : callOk loopMod 0 [] = true := by decide +kernel

theorem loopMod_out_of_fuel : run loopMod 50 0 [] = none := by decide +kernel

end Silmaril.Wasm.Interp.Closed.Examples
