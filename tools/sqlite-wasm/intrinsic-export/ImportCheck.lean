module

import SqliteWasm.IntrinsicExport

open Silmaril.Wasm Silmaril.Wasm.Validation SqliteWasm
open SqliteWasmArtifact (definedFunction?)

example :
    ∃ (inputs : BodyInputs) (signature : DefType) (term : Intrinsic.Function inputs.context signature),
      bodyInputs? sqlite = some inputs ∧ inputs.signatures[2]? = some signature ∧
      ((Binary.Core.decode? originalBytes.toByteArray).bind fun m =>
        (m.exports.find? (·.name == "_initialize")).map Export.index) = some (.func ⟨25⟩) ∧
      ((Binary.Core.decode? originalBytes.toByteArray).bind fun m =>
        definedFunction? m 25) = some term.erase ∧ FuncOk inputs.context term.erase signature := by
  refine ⟨initializerValidationInputs, typedInitializerSignature, typedInitializer,
    originalInitializerContext, initializerSignatureAtOrdinal, ?_, originalIntrinsicInitializer,
    typedInitializer.sound⟩
  rw [originalDecode]
  rfl

#print axioms originalIntrinsicInitializer
#print axioms originalInitializerTyped
