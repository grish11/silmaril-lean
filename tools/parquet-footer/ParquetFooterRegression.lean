module

import Silmaril.Formats.Parquet.Footer.Defs
import Silmaril.Data.IncludeBytes
import Batteries.Data.Except

open Silmaril.Formats Silmaril.Formats.Parquet.Footer

private def syntheticFile (body : List UInt8) : Bytes :=
  magic.append ((Bytes.ofList (body ++ [UInt8.ofNat body.length, 0, 0, 0])).append magic)

example : locate 1 (syntheticFile [0]) = .ok ⟨4, 5⟩ := rfl
example : locate 0 (syntheticFile [0]) = .error .footerLimit := rfl
example : locate 8 (syntheticFile []) = .error .invalidLength := rfl
example : checkDataSpan 12 4 8 = some ⟨4, 12⟩ := rfl
example : checkDataSpan 12 (-1) 8 = none := rfl
example : checkDataSpan 12 4 9 = none := rfl

private def assertThat (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError name)

private def expectError (name : String) (expected : Error) (result : Except Error (Span × Metadata)) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"{name}: accepted malformed footer")
  | .error actual => assertThat s!"{name}: expected {repr expected}, got {repr actual}" (actual == expected)

private def fields : List UInt8 := [0x15, 0x02, 0x19, 0x0c, 0x16, 0x00, 0x19, 0x0c]

-- Unknown field 11 is a struct with an inline bool, a map<bool, set<bool>>, and binary.
private def extension : List UInt8 := [0x7c, 0x11, 0x1b, 0x01, 0x1a, 0x02, 0x21, 0x01, 0x02,
  0x18, 0x02, 0xff, 0x00, 0x00]

private def syntheticChecks : IO Unit := do
  let read := readFooter {}
  let access := fun octets => read (syntheticFile octets)
  let valid := syntheticFile (fields ++ extension ++ [0])
  let .ok (span, metadata) := read valid | throw (IO.userError "unknown nested field")
  assertThat "unknown nested field reached outer STOP" (span.stop == valid.length - 8 && metadata.version == 1)
  let .ok _ := access (fields ++ [0x08, 0xfe, 0xff, 0x03, 2, 0xff, 0x00, 0x00]) |
    throw (IO.userError "binary extension at field 32767")
  assertThat "wire success precedes semantic schema validation" (validate span.start 32 metadata == .error .schema)
  let patch := fun offset byte => (valid.data.extract 0 offset).push byte ++ valid.data.extract (offset + 1) valid.length
  expectError "short file" (.framing .shortFile) (read Bytes.empty)
  expectError "leading magic" (.framing .leadingMagic) (read ⟨patch 0 0⟩)
  expectError "encrypted footer magic PARE" (.framing .trailingMagic) (read ⟨patch (valid.length - 1) 0x45⟩)
  expectError "length overlaps header" (.framing .invalidLength) (read ⟨patch (valid.length - 7) 1⟩)
  expectError "footer cap" (.framing .footerLimit) (readFooter {maxFooterBytes := 8} valid)
  expectError "missing required field" (.metadata (.missingField 1)) (access [0])
  expectError "wrong required wire type" (.metadata (.fieldType 1 .i32 (.payload .i64)))
    (access (0x16 :: fields.drop 1 ++ [0]))
  expectError "wrong empty-list element type" (.metadata (.traversal (.elementType .struct .i64)))
    (access (fields.take 3 ++ [0x06] ++ fields.drop 4 ++ [0]))
  expectError "duplicate required field" (.metadata (.duplicateField 1))
    (access (fields ++ [0x05, 0x02, 0x02, 0x00]))
  expectError "invalid UTF-8 for created_by" (.metadata (.traversal (.compact .invalidUtf8)))
    (access (fields ++ [0x28, 0x01, 0xff, 0x00]))
  expectError "plaintext-footer encryption metadata" (.metadata .encryption) (access (fields ++ [0x4c, 0, 0]))
  expectError "malformed nested boolean" (.metadata (.traversal (.compact .invalidBoolean)))
    (access (fields ++ extension.take 5 ++ [3] ++ extension.drop 6 ++ [0]))
  expectError "truncated binary" (.metadata (.traversal (.compact .truncated)))
    (access (fields ++ [0x68, 3, 0]))
  expectError "missing outer STOP" (.metadata (.traversal (.compact .truncated))) (access (fields ++ extension))
  expectError "bytes after outer STOP" .trailingMetadata (access (fields ++ extension ++ [0, 0]))
  expectError "depth cap" (.metadata (.traversal .depthLimit))
    (readFooter {compact := {maxDepth := 3}} valid)
  expectError "field cap" (.metadata (.traversal .fieldLimit))
    (readFooter {compact := {maxStructFields := 4}} valid)
  expectError "collection cap" (.metadata (.traversal (.compact .lengthLimit)))
    (readFooter {compact := {maxCollectionSize := 1}} valid)
  expectError "binary cap" (.metadata (.traversal (.compact .lengthLimit)))
    (readFooter {compact := {maxBinaryBytes := 1}} valid)

private def fixture : Bytes := ⟨include_bytes "fixtures/alltypes_plain.parquet"⟩

private def fixtureChecks : IO Unit := do
  match readFooter {} fixture with
  | .error error => throw (IO.userError s!"alltypes_plain: {repr error}")
  | .ok (span, metadata) =>
    assertThat "pinned file and footer geometry" (fixture.length == 1851 && span == ⟨1113, 1843⟩)
    assertThat "pinned footer version and row count" (metadata.version == 1 && metadata.numRows == 8)
    assertThat "pinned producer" (metadata.createdBy ==
      some "impala version 1.3.0-INTERNAL (build 8a48ddb1eff84592b3fc06bc6f51ec120e1fffc9)")
    let [group] := metadata.rowGroups | throw (IO.userError "expected one row group")
    assertThat "pinned row group" (group.numRows == 8 && group.totalByteSize == 671)
    let names := ["id", "bool_col", "tinyint_col", "smallint_col", "int_col", "bigint_col",
      "float_col", "double_col", "date_string_col", "string_col", "timestamp_col"]
    let types : List PhysicalType := [.int32, .boolean, .int32, .int32, .int32, .int64, .float,
      .double, .byteArray, .byteArray, .int96]
    assertThat "all pinned schema names and types" (metadata.schema.map (·.name) == "schema" :: names &&
      metadata.schema.map (·.physicalType) == none :: types.map some)
    assertThat "all pinned column paths and sizes" (group.columns.map (·.metadata.pathInSchema) == names.map List.singleton &&
      group.columns.map (·.metadata.totalCompressedSize) == [73, 24, 47, 47, 47, 55, 47, 55, 88, 49, 139])
    assertThat "all pinned data page offsets" (group.columns.map (·.metadata.dataPageOffset) ==
      [49, 109, 189, 277, 366, 458, 545, 639, 766, 863, 1040])
    assertThat "all pinned dictionary page offsets" (group.columns.map (·.metadata.dictionaryPageOffset) ==
      [some 4, none, some 168, some 256, some 345, some 429, some 524, some 610, some 705, some 840, some 929])
    assertThat "all pinned encoding and codec IDs" (group.columns.all fun col =>
      col.metadata.codec == 0 && col.metadata.encodings == [3, 2, 0])
    assertThat "pinned semantic validation" (validate span.start 32 metadata == .ok ())
    assertThat "schema depth cap" (validate span.start 1 metadata == .error .schemaDepth)
    assertThat "mismatched row count" (validate span.start 32 {metadata with numRows := 0} == .error .rowCount)
    let root :: leaf :: schema := metadata.schema | throw (IO.userError "expected schema leaves")
    assertThat "legacy required root repetition" (validate span.start 32 {metadata with schema :=
      {root with repetition := some .required} :: leaf :: schema} == .ok ())
    assertThat "incorrect schema arity" (validate span.start 32 {metadata with schema :=
      {root with numChildren := some 12} :: leaf :: schema} == .error .schema)
    assertThat "column path disagreement" (validate span.start 32 {metadata with schema :=
      root :: {leaf with name := "renamed"} :: schema} == .error .columns)
    let first :: columns := group.columns | throw (IO.userError "expected columns")
    let withColumn := fun col => {metadata with rowGroups := [{group with columns := col :: columns}]}
    let nested := withColumn {first with metadata := {first.metadata with pathInSchema := ["nested", leaf.name]}}
    let nestedGroup : SchemaElement := ⟨none, none, some .optional, "nested", some 1⟩
    assertThat "nested schema and column path" (validate span.start 32 {nested with schema :=
      root :: nestedGroup :: leaf :: schema} == .ok ())
    assertThat "page interval crosses into footer" (validate span.start 32 (withColumn
      {first with metadata := {first.metadata with totalCompressedSize := 1110}}) == .error .pageInterval)
    assertThat "incomplete offset index pair" (validate span.start 32 (withColumn
      {first with offsetIndexOffset := some 10}) == .error .indexInterval)
    assertThat "negative Bloom offset" (validate span.start 32 (withColumn
      {first with metadata := {first.metadata with bloomFilterOffset := some (-1)}}) == .error .bloomInterval)

public def main : IO Unit := do
  syntheticChecks
  fixtureChecks
  IO.println "Parquet footer: pinned alltypes_plain fixture and negative cases passed"
