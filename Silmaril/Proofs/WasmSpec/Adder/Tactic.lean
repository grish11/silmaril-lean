module

public import Silmaril.WasmSpec.Adder.Defs
import Silmaril.Wasm.Logic.Tactic.Defs

/-!
# `Adder` v1, mode `tactic`

`spec_tactic : Spec`: unfold the quoted body to its instruction list
(`addFunc_body`, by `rfl`), run it symbolically with `wasm_step` and close the
arithmetic by `simp`. Kernel-checked; no solver.
-/

@[expose] public section

namespace Silmaril.WasmSpec.Adder

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Logic.Core

/-- The quoted body, as an instruction list. -/
theorem addFunc_body :
    addFunc.body = [.localGet ⟨0⟩, .localGet ⟨1⟩, .intBinOp .i32 .add] := rfl

/-- `$add` declares no locals besides its parameters. -/
theorem addFunc_locals : addFunc.locals = [] := rfl

/-- Mode `tactic`: symbolic execution and `simp`. -/
theorem spec_tactic : Spec := by
  intro x y H P host s m
  rw [addFunc_body, addFunc_locals]
  simp only [args, res, Frame.forCall, List.map_cons, List.map_nil, List.append_nil]
  wasm_step
  simp [Idx.toNat, funcPost, intBinOp_i32_add]

end Silmaril.WasmSpec.Adder
