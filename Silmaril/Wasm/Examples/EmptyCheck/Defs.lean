module

public import Silmaril.Wasm.Examples.Verified.Defs
public import Silmaril.Wasm.Game.SpecInst.Defs
public import Silmaril.Wasm.Game.Accept.Export.Defs

/-! # The empty checker as a core Wasm module: definitions

`prog` is a core Wasm module (quoted with `wat3!`, so it is silmaril-lean's `Module` AST) with
one memory and one exported function `check(ptr: i32, len: i32) -> i32` whose body is
`i32.const 0`: it rejects every input. Read through the export embedding of
`Silmaril.Wasm.Game.Accept.Export` (`exportAccepted P Hosts prog "check"`), it is the **empty
checker** of the consequence protocols, as an actual module verified against Core execution.

* `bytes`: its 45-byte binary.
* `spec`: the `FnSpec` of `check`: on in-bounds arguments it returns `0` and leaves memory
  unchanged.
* `specMT`, `specPrep`, `specInst`: the validated type, the specification's allocation and the
  scalar instance of `prog` (no imports; one export `[i32, i32] → [i32]` at address `0`).

This is a core module. No component wraps it here: a component exporting
`check(ax, stmt) -> bool` over it would need the canonical-ABI lowering (`CanonLowerAccept`-style
correspondence), which is not established.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.EmptyCheck

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Verify Silmaril.Wasm.Validation
  Silmaril.Wasm.Game

/-- **The empty checker module.** -/
def prog : Module := wat3! r#"
(module
  (memory 1)
  (func $check (export "check") (param $p i32) (param $n i32) (result i32)
    (i32.const 0)))
"#

/-- **The bytes of `prog`**, as silmaril-lean's encoder produces them (`encodeModule_eq`). -/
def bytes : List UInt8 :=
  [0, 97, 115, 109, 1, 0, 0, 0, 1, 7, 1, 96, 2, 127, 127, 1, 127, 3, 2, 1, 0, 5, 3, 1, 0, 1, 7, 9,
    1, 5, 99, 104, 101, 99, 107, 0, 0, 10, 6, 1, 4, 0, 65, 0, 11]

/-- **The specification of `check`**: on in-bounds, non-wrapping arguments it returns `0` and
leaves memory unchanged. -/
def spec : FnSpec (BitVec 32 × BitVec 32) :=
  .mem (fun (p, n) => [.i32 p, .i32 n])
    (pre := fun (p, n) B => p.toNat + n.toNat ≤ B.size ∧ p.toNat + n.toNat < 2 ^ 32)
    (fun _ _ res => res = [.i32 0])

/-- The validated type of `prog`. -/
def specMT : CModuleType := (Validation.validate? prog).getD ⟨[], []⟩

/-- The spec's allocation of `prog`. -/
def specPrep : Config Nat × Option FuncIdx :=
  (prepare? evalConst? (importStore (CExternType.funcs specMT.imports)) prog
    (importAddrs specMT)).getD (⟨{}, {}, []⟩, none)

/-- The scalar instance of `prog`. -/
def specInst : ScalarInstance where
  imports := []
  exports := [⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩]
  addrs := [0]
  store := specPrep.1.store

end Silmaril.Wasm.Examples.EmptyCheck
