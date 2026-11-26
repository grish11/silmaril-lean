module

public import Silmaril.Formats.Parquet.Footer.Defs

/-! Bounded Compact serialization for the one-row-group flat INT32 footer. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.FlatInt32Writer.Compact

structure ColumnIndex where
  name : String
  optional : Bool
  span : Footer.Span
  deriving DecidableEq, Repr

def ColumnIndex.size (column : ColumnIndex) : Nat := column.span.stop - column.span.start

def ColumnIndex.schema (column : ColumnIndex) : Footer.SchemaElement :=
  ⟨some .int32, none, some (if column.optional then .optional else .required), column.name, none⟩

def ColumnIndex.metadata (column : ColumnIndex) (rows : Nat) : Footer.ColumnChunk :=
  ⟨0, ⟨.int32, [0, 3], [column.name], 0, rows, column.size, column.size,
    column.span.start, none, none, none, none⟩, none, none, none, none⟩

def schemaRoot (width : Nat) : Footer.SchemaElement := ⟨none, none, none, "schema", some width⟩

def metadata (rows : Nat) (columns : List ColumnIndex) : Footer.Metadata :=
  ⟨1, schemaRoot columns.length :: columns.map ColumnIndex.schema, rows,
    [⟨columns.map (fun column => column.metadata rows), (columns.map ColumnIndex.size).sum,
      rows, none, none⟩], none⟩

inductive Error where
  | byteLimit
  | integerRange
  deriving DecidableEq, Repr

structure Buffer where
  remaining : Nat
  bytes : Bytes

abbrev Write := StateT Buffer (Except Error)

def put (bytes : Bytes) : Write Unit := do
  let buffer ← get
  if buffer.remaining < bytes.length then throw .byteLimit
  set (⟨buffer.remaining - bytes.length, buffer.bytes.append bytes⟩ : Buffer)

def octet (value : Nat) : Write Unit := put (Bytes.ofList [UInt8.ofNat value])

def field (delta tag : Nat) : Write Unit := octet (16 * delta + tag)

def integer (width : ThriftCompact.Width) (value : Int) : Write Unit := do
  let some bytes := ThriftCompact.encodeSigned? width value | throw .integerRange
  put bytes

def length (size : Nat) : Write Unit := do
  if 2 ^ 31 ≤ size then throw .integerRange
  put (Bytes.ofList (ThriftCompact.varintBytes size))

def text (value : String) : Write Unit := do
  length value.utf8ByteSize
  if (← get).remaining < value.utf8ByteSize then throw .byteLimit
  put ⟨value.toUTF8⟩

def listHeader (tag size : Nat) : Write Unit :=
  if size < 15 then octet (16 * size + tag) else do
    octet (0xf0 + tag)
    length size

def root (width : Nat) : Write Unit := do
  field 4 8
  text "schema"
  field 1 5
  integer .i32 width
  octet 0

inductive LeafAnnotation where
  | unannotated
  | date

def leafAnnotated (annotation : LeafAnnotation) (column : ColumnIndex) : Write Unit := do
  field 1 5
  integer .i32 1
  field 2 5
  integer .i32 (if column.optional then 1 else 0)
  field 1 8
  text column.name
  match annotation with
  | .unannotated => pure ()
  | .date =>
    -- From SchemaElement.name (4) to ConvertedType.DATE (6).
    field 2 5
    integer .i32 6
    -- LogicalType (10) contains only DATE (6) with an empty DateType struct.
    field 4 12
    field 6 12
    octet 0
    octet 0
  octet 0

def leaf (column : ColumnIndex) : Write Unit := leafAnnotated .unannotated column

def chunk (rows : Nat) (column : ColumnIndex) : Write Unit := do
  field 2 6
  integer .i64 0
  field 1 12
  field 1 5
  integer .i32 1
  field 1 9
  listHeader 5 2
  integer .i32 0
  integer .i32 3
  field 1 9
  listHeader 8 1
  text column.name
  field 1 5
  integer .i32 0
  field 1 6
  integer .i64 rows
  field 1 6
  integer .i64 column.size
  field 1 6
  integer .i64 column.size
  field 2 6
  integer .i64 column.span.start
  octet 0
  octet 0

def group (rows : Nat) (columns : List ColumnIndex) : Write Unit := do
  field 1 9
  listHeader 12 columns.length
  for column in columns do chunk rows column
  field 1 6
  integer .i64 (columns.map ColumnIndex.size).sum
  field 1 6
  integer .i64 rows
  octet 0

def footerAnnotated (annotation : LeafAnnotation) (rows : Nat) (columns : List ColumnIndex) :
    Write Unit := do
  field 1 5
  integer .i32 1
  field 1 9
  listHeader 12 (columns.length + 1)
  root columns.length
  for column in columns do leafAnnotated annotation column
  field 1 6
  integer .i64 rows
  field 1 9
  listHeader 12 1
  group rows columns
  octet 0

def footer (rows : Nat) (columns : List ColumnIndex) : Write Unit :=
  footerAnnotated .unannotated rows columns

/-- Each write consumes part of the caller's exact Compact byte budget. -/
def encodeAnnotated (annotation : LeafAnnotation) (limit rows : Nat) (columns : List ColumnIndex) :
    Except Error Bytes :=
  ((footerAnnotated annotation rows columns).run ⟨limit, .empty⟩).map (·.2.bytes)

def encode (limit rows : Nat) (columns : List ColumnIndex) : Except Error Bytes :=
  encodeAnnotated .unannotated limit rows columns

end Silmaril.Formats.Parquet.FlatInt32Writer.Compact
