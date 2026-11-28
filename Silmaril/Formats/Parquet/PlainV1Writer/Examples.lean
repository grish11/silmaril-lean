module

import Silmaril.Formats.Parquet.PlainV1Writer.Thms
meta import Silmaril.Formats.Parquet.PlainV1Writer.Defs

/-! Read emitted page bytes through Compact and the existing scalar reader. -/

namespace Silmaril.Formats.Parquet.PlainV1Writer

private meta def limits : Limits := ⟨{}, 17, ⟨26, 26, ⟨5, 10⟩, 0⟩⟩

private meta def readback (input : Input) : Option (Nat × Nat × List (Option Int32)) := do
  let page ← (emit limits input).toOption
  let (header, offset) ← (Page.readHeaderPrefix limits.header page.wire).toOption
  let .dataV1 v1 := header.kind | none
  let body ← page.wire.slice? offset none
  let params : ScalarPage.Parameters :=
    ⟨⟨header.compressedSize, header.uncompressedSize⟩, input.schema, v1.numValues, 0, v1.encoding,
      .v1 v1.definitionLevelEncoding v1.repetitionLevelEncoding⟩
  let rows ← (ScalarPage.decode .int32 params limits.scalar body).toOption
  return (offset, body.length, rows)

private meta def mixed : List (Option Int32) := [some 7, none, some (-4), none, some 19]

#guard readback (.required [-2147483648, 0, 2147483647]) =
  some (17, 12, [some (-2147483648), some 0, some 2147483647])

#guard readback (.optional mixed) = some (17, 26, mixed)
#guard readback (.optional [none, none, none]) = some (17, 10, [none, none, none])
#guard readback (.required []) = some (17, 0, [])
#guard readback (.optional []) = some (17, 4, [])

#guard (emit {limits with headerBytes := 16} (.optional mixed)).map (fun _ => ()) = .error .headerBudget
#guard (emit {limits with scalar.compressedBytes := 25} (.optional mixed)).map (fun _ => ()) = .error .bodyBudget
#guard (emit {limits with scalar.uncompressedBytes := 25} (.optional mixed)).map (fun _ => ()) = .error .bodyBudget
#guard (emit {limits with scalar.levels.bytes := 9} (.optional mixed)).map (fun _ => ()) = .error .bodyBudget
#guard (emit {limits with scalar.levels.values := 4} (.optional mixed)).map (fun _ => ()) = .error .bodyBudget
#guard (emit {limits with header.compact.maxStructFields := 3} (.optional mixed)).map (fun _ => ()) =
  .error (.header (.traversal .fieldLimit))

end Silmaril.Formats.Parquet.PlainV1Writer
