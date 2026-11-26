module

public import Silmaril.Wasm.SSA.MLIRMath.Defs
import Silmaril.SSA.MLIR.Complex.Thms
import Silmaril.Numeric.Libm.Wasm.Thms
import Silmaril.Proofs.Wasm.SSA.MLIRMath.Log

public section

namespace Silmaril.Wasm.SSA.MLIRMath

open Silmaril.MLIR Silmaril.Numeric.Ieee754 Silmaril.Numeric.Libm

theorem ofF64_toF64 (bits : Math.Binary64) : ofF64 (toF64 bits) = bits := rfl

theorem toF64_ofF64 (x : F64) : toF64 (ofF64 x) = x := rfl

theorem absf_fabs_bits (x : F64) :
    (Math.denote .absf).Executes (ofF64 x) (ofF64 (Double.Ref.fabs x)) := rfl

theorem conj_neg_bits (re im : F64) :
    Silmaril.MLIR.Complex.Op.conj.executable (ofF64 re, ofF64 im) =
      (ofF64 re, ofF64 (F64.neg im)) := rfl

theorem complex_create_realizes :
    (Silmaril.MLIR.Complex.denote .create).RealizesOn
      (Silmaril.MLIR.Complex.createObservation decodeFinite)
      (fun bits => ∃ parts, Silmaril.MLIR.Complex.decodeParts decodeFinite bits = some parts)
      (Silmaril.MLIR.Complex.denote .create).Executes :=
  Silmaril.MLIR.Complex.create_realizes decodeFinite

/-- The libm catalogue logarithm and the MLIR exact reference have the same graph. -/
theorem log_exact_iff (bits : Math.Binary64) (result : ℝ) :
    Double.log.exact (toF64 bits) = some result ↔
      ∃ x, decodeFinite bits = some x ∧ (Math.denote .log).reference.Holds x result :=
  Proofs.Wasm.SSA.MLIRMath.log_exact_iff bits result

theorem log_in_catalogue : Double.log.entry ∈ Double.catalogue :=
  Proofs.Wasm.SSA.MLIRMath.log_in_catalogue

/-- The catalogue's correctly-rounded hypothesis yields the MLIR observation. -/
theorem log_node_of_catalogue {impl : LibmImpl}
    (h : Double.ValidLibmDouble .correctlyRounded impl) : LogNode (impl Double.log.entry) :=
  Proofs.Wasm.SSA.MLIRMath.log_node_of_catalogue h

/-- The Wasm value contract transfers the rounding hypothesis to the MLIR observation. -/
theorem log_exports_of_valid {P : Numerics.Profile} {m : Module}
    (h : WasmExport.ExportsValid P m Double.log (Double.level .correctlyRounded Double.log.name)) :
    WasmExport.Exports P m Double.log.name LogNode :=
  WasmExport.Exports.mono h fun _ valid => Proofs.Wasm.SSA.MLIRMath.log_node_of_cr valid.2

/-- A checked single-instruction `fabs` export agrees with the MLIR bit evaluator. -/
theorem absf_build_exports {bytes : ByteArray}
    (h : WasmExport.checkUnopBytes bytes Double.fabs.name .abs = true) :
    WasmExport.BuildExports bytes Double.fabs.name AbsFNode := by
  refine WasmExport.BuildExports.mono (WasmExport.buildExports_unop h) ?_
  intro impl bits x
  rw [bits x]
  exact absf_fabs_bits x

end Silmaril.Wasm.SSA.MLIRMath
