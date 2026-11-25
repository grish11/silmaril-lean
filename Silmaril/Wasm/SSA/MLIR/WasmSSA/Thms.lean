module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Defs
import Silmaril.Wasm.Validation.Intrinsic.Thms
import Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA.Validation

public section

namespace Silmaril.MLIR.WasmSSA

open Silmaril.Wasm (TypeIdx)
open Silmaril.Wasm.Validation (Context DefType Expand ExprOk FuncOk)

/-- The emitted code validates with one integer result in its declared Core
body context. -/
theorem Func.toWasm_exprOk {params : List IntType} {result : IntType} (f : Func params result)
    (C : Context) (type : TypeIdx) (fits : f.Fits) :
    ExprOk (f.bodyContext C) (f.toWasm C type fits).body [result.closed] :=
  (f.toBody C fits).sound

/-- Package body validation as `FuncOk` when the supplied Core type index
resolves to the function's signature. -/
theorem Func.toWasm_funcOk {params : List IntType} {result : IntType} (f : Func params result)
    (C : Context) (type : TypeIdx) (fits : f.Fits) {d : DefType}
    (resolves : C.type? type = some d) (expands : Expand d (Func.coreSignature params result)) :
    FuncOk C (f.toWasm C type fits) d :=
  Proofs.Wasm.SSA.MLIR.WasmSSA.toWasm_funcOk f C type fits resolves expands

theorem Func.toWasm?_isSome_iff {params : List IntType} {result : IntType}
    (f : Func params result) (C : Context) (type : TypeIdx) :
    (f.toWasm? C type).isSome = true ↔ f.Fits := by
  by_cases fits : f.Fits <;> simp [Func.toWasm?]

theorem Func.toWasm?_funcOk {params : List IntType} {result : IntType} (f : Func params result)
    {C : Context} {type : TypeIdx} {raw : Silmaril.Wasm.Func} {d : DefType}
    (resolves : C.type? type = some d) (expands : Expand d (Func.coreSignature params result))
    (compiled : f.toWasm? C type = some raw) : FuncOk C raw d := by
  unfold Func.toWasm? at compiled
  split at compiled <;> cases compiled
  exact f.toWasm_funcOk C type ‹_› resolves expands

end Silmaril.MLIR.WasmSSA
