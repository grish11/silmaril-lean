module

public import Silmaril.Wasm.Examples.JsonAccept.Defs
public import Silmaril.Wasm.Game.SpecInst.Defs
public import Silmaril.Wasm.Game.Accept.Export.Defs

/-! # The JSON-subset acceptor, instantiated: definitions

* `specMT`: the validated type of `prog`.
* `specPrep`: the specification's allocation of `prog` (`prepare?` into the store of fresh host
  functions for its imports, which are none).
* `specInst`: its scalar instance: no imports, one export `[i32, i32] → [i32]` at address `0`.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.JsonAccept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game

/-- The validated type of `prog`. -/
def specMT : CModuleType := (validate? prog).getD ⟨[], []⟩

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

end Silmaril.Wasm.Examples.JsonAccept
