module

import Silmaril.Formats.Parquet.FlatScan.Scalar.Defs
import Silmaril.Data.IncludeBytes
import Batteries.Data.Except

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.FlatScan

private def assertThat (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError name)

private def success {α ε : Type} [Repr ε] (label : String) (answer : Except ε α) : IO α :=
  match answer with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {repr error}")

private def expectError {α : Type} (name : String) (result : Except (Error String) α)
    (expected : Error String) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"{name}: unexpected success")
  | .error error => assertThat s!"{name}: got {repr error}, expected {repr expected}" (error == expected)

private def v1 : Bytes := ⟨include_bytes "fixtures/flat-plain-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "fixtures/flat-plain-v2.parquet"⟩

private def requiredValue (row : Nat) : Option Int32 := some (Int32.ofInt (10 * (row : Int) - 17))
private def optionalValue (row : Nat) : Option Int32 :=
  if row % 3 = 0 then none else some (Int32.ofInt (-3 * (row : Int)))

/-- Compare the actual callback bytes to the independent PyArrow/Thrift window
for each page. Return that page's oracle slots without a second wire decoder. -/
private def oracle (source : Bytes) (windows : List (List (List (Nat × Nat)))) : DecodePage String :=
  let pages := windows.zipIdx.flatMap fun (columns, group) => columns.zipIdx.flatMap fun (pages, column) =>
    pages.zipIdx.map fun ((start, stop), page) =>
      let name := if column = 0 then "required_i32" else "optional_i32"
      let value := if column = 0 then requiredValue else optionalValue
      let slots := (List.range 4).map fun n => value (group * 12 + page * 4 + n)
      (name, Footer.fileBytes source start stop, slots)
  fun field _ body =>
    match pages.find? (fun (name, bytes, _) => field.name == name && body == bytes) with
    | some (_, _, slots) => .ok slots
    | none => .error "page bytes differ from the pinned oracle window"

private def v1Windows : List (List (List (Nat × Nat))) := [
  [[(23,39), (58,74), (93,109)], [(128,142), (161,179), (198,216)]],
  [[(235,251), (270,286), (305,321)], [(340,354), (373,391), (410,428)]]]
private def v2Windows : List (List (List (Nat × Nat))) := [
  [[(28,44), (68,84), (108,124)], [(148,158), (182,196), (220,234)]],
  [[(258,274), (298,314), (338,354)], [(378,388), (412,426), (450,464)]]]

private def checkFile (source : Bytes) (windows : List (List (List (Nat × Nat)))) : IO Unit := do
  let scalarLimits : ScalarPage.Limits := ⟨1024, 1024, ⟨48, 1024⟩, 0⟩
  for group in [0, 1] do
    let oracleBatch ← success "checked fixture windows" (scanFileRowGroup {} (oracle source windows) source group)
    let batch ← success "composed scalar scan" (scanFileRowGroup {} (decodeInt32Page scalarLimits) source group)
    assertThat "columns stay in schema order" (batch.columns.map (fun col => col.1.name) ==
      ["required_i32", "optional_i32"])
    assertThat "the scalar adapter agrees with the page-window oracle" (batch.rows == oracleBatch.rows)
    assertThat "twelve oracle rows per group in wire order" (batch.rowCount == 12 && batch.rows ==
      (List.range 12).map fun n => [requiredValue (group * 12 + n), optionalValue (group * 12 + n)])
  expectError "row group out of range" (scanFileRowGroup {} (oracle source windows) source 2) .groupIndex

private def metadataNegatives : IO Unit := do
  let (span, footer) ← success "fixture metadata" (Footer.readFooter {} v2)
  let first :: _ := footer.rowGroups | throw (IO.userError "missing fixture group")
  let [left, right] := first.columns | throw (IO.userError "expected two columns")
  let [root, field, other] := footer.schema | throw (IO.userError "expected two schema leaves")
  let decode := oracle v2 v2Windows
  let scan := scanRowGroup {} decode v2 span.start footer.schema
  let withLeft := fun metadata => scan {first with columns := [{left with metadata}, right]}
  expectError "duplicate column metadata" (scan {first with columns := [left, left]})
    (.columnPath "optional_i32" ["required_i32"])
  expectError "missing column metadata" (scan {first with columns := [left]}) .columnArity
  expectError "reordered metadata" (scan {first with columns := [right, left]})
    (.columnPath "required_i32" ["optional_i32"])
  expectError "nested path" (withLeft {left.metadata with pathInSchema := ["root", "required_i32"]})
    (.columnPath "required_i32" ["root", "required_i32"])
  expectError "wrong physical type" (withLeft {left.metadata with physicalType := .int64})
    (.columnType "required_i32")
  expectError "footer slot count mismatch" (withLeft {left.metadata with numValues := 11})
    (.columnCount "required_i32")
  expectError "unsupported advertised encoding" (withLeft {left.metadata with encodings := [0, 8]})
    (.columnEncoding "required_i32")
  expectError "expected uncompressed column" (withLeft {left.metadata with codec := 1})
    (.columnCodec "required_i32")
  expectError "chunk intersects footer" (withLeft {left.metadata with totalCompressedSize := Int.ofNat span.start})
    (.columnBounds "required_i32")
  expectError "page totals smaller than the footer value count"
    (withLeft {left.metadata with totalCompressedSize := 40}) .pageCount
  expectError "negative row count" (scan {first with numRows := -1}) .rowCount
  expectError "duplicate schema field" (scanRowGroup {} decode v2 span.start [root, field, field] first) .duplicateField
  expectError "repeated schema field" (scanRowGroup {} decode v2 span.start
    [root, {field with repetition := some .repeated}, other] first) .schema
  expectError "row budget before scan" (scanRowGroup {maxRows := 11} decode v2 span.start footer.schema first) .rowLimit
  expectError "cell budget before scan" (scanRowGroup {maxCells := 23} decode v2 span.start footer.schema first) .cellLimit
  expectError "callback slot count" (scanRowGroup {} (fun _ _ _ => .ok []) v2 span.start footer.schema first) .pageCount
  expectError "required callback null" (scanRowGroup {} (fun _ _ _ => .ok [none, none, none, none])
    v2 span.start footer.schema first) .pageNulls
  expectError "V2 callback null count" (scanRowGroup {} (fun _ _ _ => .ok [some 1, some 2, some 3, some 4])
    v2 span.start footer.schema first) .pageNulls
  let zero ← success "zero columns" (scanRowGroup {} decode v2 span.start
    [{root with numChildren := some 0}] {first with numRows := 3, columns := []})
  assertThat "zero columns retain three ordered rows" (zero.columns.isEmpty && zero.rows == [[], [], []])

private def pageNegatives : IO Unit := do
  let (_, footer) ← success "fixture metadata" (Footer.readFooter {} v2)
  let some template := (footer.rowGroups.head?.bind (·.columns.head?)) |
    throw (IO.userError "missing fixture column")
  let run := fun wire =>
    let source := Bytes.ofList ([0,0,0,0] ++ wire)
    let column : Footer.ColumnChunk := {template with metadata :=
      {template.metadata with numValues := 1, dataPageOffset := 4, totalCompressedSize := Int.ofNat wire.length}}
    scanColumn {} (fun _ _ _ => .error "callback unexpectedly called") source source.length
      ⟨"required_i32", .required⟩ 1 column
  expectError "unknown page kind" (run [0x15, 8, 0x15, 0, 0x15, 0, 0]) .unsupportedKind
  expectError "CRC-bearing page" (run [0x15, 8, 0x15, 0, 0x15, 0, 0x15, 0, 0]) .crcUnsupported
  expectError "non-PLAIN data page" (run [0x15, 0, 0x15, 0, 0x15, 0, 0x2c,
    0x15, 2, 0x15, 10, 0x15, 6, 0x15, 6, 0, 0]) .unsupportedPageEncoding

public def main : IO Unit := do
  checkFile v1 v1Windows
  checkFile v2 v2Windows
  metadataNegatives
  pageNegatives
  IO.println "Parquet flat scan: 24 PyArrow page windows, scalar-adapter rows, and rejection checks passed"
