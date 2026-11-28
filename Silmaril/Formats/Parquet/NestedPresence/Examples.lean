module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.NestedPresence.Thms
import Silmaril.Formats.Parquet.Page.Defs
import Silmaril.Formats.Parquet.Plain.Defs
meta import Batteries.Data.Except
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.NestedPresence.Defs
meta import Silmaril.Formats.Parquet.Page.Defs
meta import Silmaril.Formats.Parquet.Plain.Defs

namespace Silmaril.Formats.Parquet.NestedPresence

private def source : Bytes := ⟨include_bytes "../../../../data/parquet-nested-footer/optional-point.parquet"⟩

private def observe (column : Nat) : Option (List Presence × List Int × List UInt8) := do
  let snapshot ← (Snapshot.check (Failure := Unit) {} source).toOption
  let selection ← (Footer.NestedLeaf.select {} snapshot column).toOption
  let child ← childOf selection
  let (_, chunk) ← (Footer.NestedLeaf.selectChunk selection 0).toOption
  if chunk.metadata.codec ≠ 0 then none else do
    let span ← Page.columnSpan snapshot.footer.start chunk.metadata
    let [.mk header _ body] ← (Page.readChunk {} snapshot.bytes span).toOption | none
    let output ← (decodeV1 child {} header (Footer.fileBytes source body.start body.stop)).toOption
    let count := output.states.countP Presence.valuePresent
    let values ← match selection.physical with
      | .int32 => (Plain.decodeInt32 count output.scalars).toOption.map (·.map Int32.toInt)
      | .int64 => (Plain.decodeInt64 count output.scalars).toOption.map (·.map Int64.toInt)
      | _ => none
    pure (output.states, values, output.scalars.toList)

#guard observe 0 = some ([.value, .parentAbsent, .value], [-7, 0], [249, 255, 255, 255, 0, 0, 0, 0])
#guard observe 1 = some ([.value, .parentAbsent, .childNull], [4398046511104], [0, 0, 0, 0, 0, 4, 0, 0])

private def optionalBody : Bytes := Bytes.ofList [3, 0, 0, 0, 3, 0x12, 0, 0xff]

#guard decode .optional 3 {} optionalBody =
  .ok ⟨[.value, .parentAbsent, .childNull], Bytes.ofList [0xff]⟩
#guard decode .optional 3 {} (Bytes.ofList [3, 0, 0, 0, 3, 0x13, 0, 0xff]) =
  .error .definitionLevel
#guard decode .optional 3 {} (Bytes.ofList [3, 0, 0, 0, 3, 0x12]) =
  .error (.section .truncatedDefinitions)
#guard decode .optional 3 {} (Bytes.ofList [4, 0, 0, 0, 3, 0x12, 0, 0xff]) =
  .error (.hybrid .trailingBytes)
#guard decode .optional 3 { maxBodyBytes := 7 } optionalBody = .error .bodyLimit
#guard decodeV1 .optional {} ⟨7, 8, none, .dataV1 ⟨3, 0, 3, 3⟩⟩ optionalBody = .error .bodySize
#guard decodeV1 .optional {} ⟨8, 8, none, .dataV1 ⟨3, 0, 4, 3⟩⟩ optionalBody = .error .encoding
#guard decodeV1 .optional {} ⟨8, 8, some 0, .dataV1 ⟨3, 0, 3, 3⟩⟩ optionalBody = .error .crc

end Silmaril.Formats.Parquet.NestedPresence
