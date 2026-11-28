module

import Silmaril.Formats.Parquet.FlatInt32Writer.Thms
meta import Silmaril.Formats.Parquet.FlatInt32Writer.Defs

/-! Exercise the complete file boundary and its admission checks. -/

namespace Silmaril.Formats.Parquet.FlatInt32Writer

private meta def limits : Limits := ⟨16, 4096, {}, ⟨{}, 32, ⟨64, 64, ⟨16, 32⟩, 0⟩⟩⟩

private meta def mixed : Input :=
  ⟨3, [⟨"id", .required [-2147483648, 0, 2147483647]⟩,
    ⟨"café", .optional [some 7, none, some (-4)]⟩,
    ⟨"nulls", .optional [none, none, none]⟩]⟩

private meta def readColumns (input : Input) : Option (List String × Nat × List (List (Option Int32))) := do
  let output ← (emit limits input).toOption
  let (span, metadata) ← (Footer.readFooter limits.footer output.bytes).toOption
  let [group] := metadata.rowGroups | none
  let columns ← (output.chunks.zip group.columns).mapM fun (chunk, column) => do
    let area ← Page.columnSpan span.start column.metadata
    let [frame] ← (Page.readChunk limits.pageReader output.bytes area).toOption | none
    let body := Footer.fileBytes output.bytes frame.payload.start frame.payload.stop
    (ScalarPage.decode .int32 chunk.column.values.parameters limits.page.scalar body).toOption
  return (group.columns.flatMap (·.metadata.pathInSchema), group.numRows.toNat, columns)

#guard readColumns mixed = some (["id", "café", "nulls"], 3,
  [[some (-2147483648), some 0, some 2147483647], [some 7, none, some (-4)], [none, none, none]])

#guard readColumns ⟨0, [⟨"id", .required []⟩, ⟨"text", .optional []⟩]⟩ =
  some (["id", "text"], 0, [[], []])

#guard (emit limits ⟨0, [⟨"x", .required []⟩, ⟨"x", .optional []⟩]⟩).map (fun _ => ()) =
  .error .schemaOrCount
#guard (emit limits ⟨1, [⟨"x", .required [1]⟩, ⟨"y", .optional []⟩]⟩).map (fun _ => ()) =
  .error .schemaOrCount
#guard (emit limits ⟨0, []⟩).map (fun _ => ()) = .error .schemaOrCount
#guard (emit {limits with maxColumns := 2} mixed).map (fun _ => ()) = .error .schemaOrCount
#guard (emit {limits with maxFileBytes := 12} mixed).map (fun _ => ()) = .error .fileLimit
#guard (emit {limits with footer.maxFooterBytes := 4} mixed).map (fun _ => ()) = .error (.compact .byteLimit)
#guard (emit {limits with page.headerBytes := 16} mixed).map (fun _ => ()) = .error .pageBudget

#guard (emit limits mixed).toOption.map (fun file =>
    ((emit {limits with maxFileBytes := file.bytes.length} mixed).toOption.map (·.bytes) == some file.bytes,
     (emit {limits with maxFileBytes := file.bytes.length - 1} mixed).map (fun _ => ()))) =
  some (true, .error (.compact .byteLimit))

end Silmaril.Formats.Parquet.FlatInt32Writer
