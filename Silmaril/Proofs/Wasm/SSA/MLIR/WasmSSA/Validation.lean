module

public import Silmaril.Wasm.SSA.MLIR.WasmSSA.Defs
public import Silmaril.Wasm.Validation.Intrinsic.Thms

public section

namespace Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA

open Silmaril.MLIR.WasmSSA
open Silmaril.Wasm (TypeIdx)
open Silmaril.Wasm.Validation (Context DefType Expand FuncOk LocalOk Ty)

private theorem locals_ok (C : Context) (types : List IntType) :
    List.Forall₂ (LocalOk C) (types.map IntType.valType) (types.map IntType.localType) := by
  induction types with
  | nil => exact .nil
  | cons t _ ih => exact .cons (.set (.num (.int t.toWasm)) trivial) ih

theorem toWasm_funcOk {params : List IntType} {result : IntType} (f : Func params result)
    (C : Context) (type : TypeIdx) (fits : f.Fits) {d : DefType}
    (resolves : C.type? type = some d) (expands : Expand d (Func.coreSignature params result)) :
    FuncOk C (f.toWasm C type fits) d := by
  refine .mk resolves expands (locals_ok C f.bindingTypes) ?_
  simpa only [Func.bodyContext, Func.toWasm, Wasm.Validation.ExprOk, Ty.toList_ofList] using (f.toBody C fits).sound

end Silmaril.Proofs.Wasm.SSA.MLIR.WasmSSA
