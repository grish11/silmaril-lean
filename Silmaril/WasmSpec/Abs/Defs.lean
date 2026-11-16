module

public import Silmaril.WasmSpec.Common.Defs

/-!
# Wasm specification library: `Abs` v1

The program (`abs.wat`): branch-free absolute value, `m = x >>s 31;
(x ^ m) - m`. Specification: the result is `-x` when `x` is negative (as a
signed integer) and `x` otherwise, modulo `2^32` (so `abs INT_MIN = INT_MIN`).
The verification condition is a pure bit-vector identity, which is where the
modes differ most: a bit-level argument by hand, one `bv_decide` call by SAT.
-/

@[expose] public section

namespace Silmaril.WasmSpec.Abs

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- The program, quoted from `abs.wat`. -/
def program := wat3! r#"
(module
  ;; @requires true
  ;; @ensures (= result (ite (bvslt x #x00000000) (bvneg x) x))
  (func $abs (export "abs") (param $x i32) (result i32) (local $m i32)
    (local.set $m (i32.shr_s (local.get $x) (i32.const 31)))
    (i32.sub (i32.xor (local.get $x) (local.get $m)) (local.get $m))))
"#

/-- The function `$abs`. -/
def absFunc : Func := program.funcs[0]

/-- Wrapping absolute value of a signed `i32`. -/
def absBV (x : BitVec 32) : BitVec 32 := if x.slt 0#32 then -x else x

/-- **Specification**: `$abs x` returns `absBV x`. -/
def Spec : Prop := ∀ x : BitVec 32, Computes absFunc [.i32 x] [.i32 (absBV x)]

end Silmaril.WasmSpec.Abs
