module

public import Silmaril.WasmSpec.Adder.Defs

/-!
# Wasm specification library: `Add3` v1

The program (`add3.wat`): `add3 x y z` imports an adder `env.add` and returns
`add (add x y) z`. Its specification is **relative to `Adder`'s**: whenever
the imported function satisfies `Silmaril.WasmSpec.Adder.CallSpec`, the body
returns `x + y + z`. `Silmaril.WasmSpec.Add3.Thms` discharges the assumption with
`Adder`'s own implementation (`Adder.callSpec`).
-/

@[expose] public section

namespace Silmaril.WasmSpec.Add3

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Logic.Core

/-- The program, quoted from `add3.wat`. -/
def program := wat3! r#"
(module
  ;; @assume add (= result (bvadd x y))
  (import "env" "add" (func $add (param i32 i32) (result i32)))
  ;; @requires true
  ;; @ensures (= result (bvadd (bvadd x y) z))
  (func $add3 (export "add3") (param $x i32) (param $y i32) (param $z i32) (result i32)
    (call $add (call $add (local.get $x) (local.get $y)) (local.get $z))))
"#

/-- The function `$add3` (the import `$add` is function index `0`). -/
def add3Func : Func := program.funcs[0]

/-- **Specification**: in an instance whose function `0` is at an address `a`
satisfying `Adder.CallSpec` in every store satisfying `Inv`, the body of
`$add3` on `x, y, z` returns `x + y + z` from any such store, unchanged. -/
def Spec : Prop :=
  ∀ {H : Type} (P : Profile) (host : HostSemantics H) (a : Nat) (Inv : Store H → Prop)
    (s : Store H) (m : ModuleInst), Adder.CallSpec P host a Inv → m.funcs[0]? = some a →
    (s.funcs[a]?).isSome → Inv s → ∀ x y z : BitVec 32,
    WP P host s (Frame.forCall m [.i32 x, .i32 y, .i32 z] add3Func.locals)
      (expression add3Func.body) (funcPost P host 1 fun s' r => s' = s ∧ r = [.i32 (x + y + z)])

end Silmaril.WasmSpec.Add3
