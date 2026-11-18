module

public import Silmaril.Wasm.Region.ByteMap.Produce.Examples.Defs

@[expose] public section
namespace Silmaril.Wasm.Region.ByteMap.Produce.Examples

set_option maxRecDepth 100000

/-- The custom-section decoy is not selected, and a global import does not
shift the function index space. Equal bodies retain different source offsets. -/
theorem duplicate_positions : stats? duplicate = some [(1, 47, 3), (2, 57, 3)] := by decide +kernel

theorem conditional_positions : stats? conditional = some [(0, 22, 3)] := by decide +kernel
theorem handler_positions : stats? handler = some [(0, 22, 2)] := by decide +kernel
theorem prefixed_positions : stats? prefixed = some [(0, 22, 3)] := by decide +kernel
theorem absent_else_positions : stats? noElse = some [(0, 22, 2)] := by decide +kernel

/-- Malformed code-section length cannot be certified by the whole-module API. -/
theorem truncated_module_rejected : (module? duplicate.dropLast).isNone = true := by decide +kernel

/-- No code section is reported as unsupported by this adapter, not as a
successful proof that unknown locations are empty. -/
theorem absent_code_rejected :
    (module? (Silmaril.Wasm.Binary.magic ++ Silmaril.Wasm.Binary.version)).isNone = true := by decide +kernel

theorem wrong_index_rejected : wrongIndexRejected? = some true := by decide +kernel
theorem custom_decoy_rejected : customSectionRejected? = some true := by decide +kernel

theorem empty_code_accepted :
    (module? (Silmaril.Wasm.Binary.magic ++ Silmaril.Wasm.Binary.version ++ [10, 1, 0])).isSome = true := by
  decide +kernel

end Silmaril.Wasm.Region.ByteMap.Produce.Examples
