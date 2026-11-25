module

import SqliteWasm.WholeModule
import SqliteWasm.GetVarintSixByte

namespace SqliteWasm

open Silmaril.Wasm SqliteWasmArtifact

set_option maxRecDepth 65536

private def reader : Func := (definedFunction? sqlite 434).get rfl

-- The complete decoder and the original-byte record selector agree on the exact
-- type index, local declarations and instruction body used in the reader proof.
example :
    ((Binary.Core.decode? originalBytes.toByteArray).bind
      (fun decoded => definedFunction? decoded 434)) = sourceFunction? original 434 := by
  rw [originalDecode, originalGetVarintFunction]
  rfl

example :
    ((Binary.Core.decode? originalBytes.toByteArray).bind
      (fun decoded => definedFunction? decoded 434)) = some reader := by
  rw [originalDecode]
  rfl

#print axioms originalDecode
#print axioms getVarint_sixByte

end SqliteWasm
