module

public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Defs
public import Silmaril.Formats.Parquet.DeltaPage.Defs

/-! One selected flat group with a required PLAIN INT32 leaf and an optional
DELTA_LENGTH_BYTE_ARRAY leaf, on the same checked codec-0 snapshot. -/

public section

namespace Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength

structure Limits where
  group : Int32ByteArrayGroup.Limits := {}
  maxBlockValues : Nat := 4096
  maxMiniblocksPerBlock : Nat := 128
  maxBlocks : Nat := 8192

/-- The page and delta length readers inherit the column's byte and slot caps. -/
@[expose] def Limits.delta (limits : Limits) : DeltaPage.Limits :=
  let column := limits.group.column
  let packed : DeltaBinaryPacked.Limits :=
    ⟨column.maxPageBytes, column.maxRows, limits.maxBlockValues, limits.maxMiniblocksPerBlock, limits.maxBlocks⟩
  let bytes : DeltaLengthByteArray.Limits := ⟨packed, column.maxPageBytes, limits.group.maxValueBytes⟩
  ⟨⟨column.maxPageBytes, column.maxPageBytes, ⟨column.maxRows, column.maxPageBytes⟩, 0⟩,
    packed, bytes, ⟨packed, bytes, limits.group.maxValueBytes, column.maxPageBytes⟩⟩

inductive PageError where
  | nonDataPage
  | encoding (actual : Int)
  | delta (reason : DeltaPage.Error)
  deriving DecidableEq, Repr

inductive Error where
  | openFailure (reason : Int32ByteArrayGroup.Error)
  | int32 (reason : FlatColumn.Error FlatScan.AdapterError)
  | byteArray (reason : FlatColumn.Error PageError)
  | alignment (group int32Count byteArrayCount : Nat)
  deriving DecidableEq, Repr

@[expose] def policy : FlatColumn.Policy := ⟨6, .v1AndV2⟩

/-- Pass the original frame data through the shared delta page adapter.
The callback itself accepts only the exact selected value encoding. -/
def decodePage (limits : Limits) : FlatColumn.DecodePage Bytes PageError :=
  fun _ metadata header body => do
    let some params := FlatColumn.pageParameters .optional metadata.codec header | throw .nonDataPage
    if params.encoding ≠ 6 then .error (.encoding params.encoding)
    else (DeltaPage.decode .byteArray params limits.delta body).mapError .delta

abbrev Checked (int32Name byteArrayName : String) :=
  Int32ByteArrayGroup.Checked ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩

/-- Reuse the same-snapshot selection and its exact leaf and chunk ordinals. -/
def openFile (limits : Limits) (input : Bytes) (int32Name byteArrayName : String) :
    Except Error (Checked int32Name byteArrayName) :=
  (Int32ByteArrayGroup.openFile limits.group input ⟨int32Name, .required⟩ ⟨byteArrayName, .optional⟩).mapError
    .openFailure

variable {int32Name byteArrayName : String}

@[expose] def readBinary (checked : Checked int32Name byteArrayName) (limits : Limits) (index : Nat) :
    Except (FlatColumn.Error PageError) (List (Option Bytes)) :=
  FlatColumn.readColumn checked.byteArrayBinding limits.group.column policy (decodePage limits) index

/-- Read the PLAIN INT32 chunk first, then the delta-length BYTE_ARRAY chunk.
Both complete slot lists must agree in length before pairing. -/
@[expose] def readGroup (checked : Checked int32Name byteArrayName) (limits : Limits) (index : Nat) :
    Except Error (List Int32ByteArrayGroup.Row) :=
  match checked.readInt32 limits.group index with
  | .error reason => .error (.int32 reason)
  | .ok integers =>
    match readBinary checked limits index with
    | .error reason => .error (.byteArray reason)
    | .ok bytes =>
      if integers.length = bytes.length then .ok (integers.zip bytes)
      else .error (.alignment index integers.length bytes.length)

def readFileRowGroup (limits : Limits) (input : Bytes) (int32Name byteArrayName : String) (index : Nat) :
    Except Error (List Int32ByteArrayGroup.Row) := do
  let checked ← openFile limits input int32Name byteArrayName
  readGroup checked limits index

/-- The exact original frame yields a checked mask, a complete signed length
stream, and exactly the concatenated opaque bytes that those lengths specify. -/
@[expose] def PageWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (frame : Page.Frame) (slots : List (Option Bytes)) : Prop :=
  let body := FlatColumn.frameBody source frame
  ∃ (params : ScalarPage.Parameters) (layout : FlatPage.Layout) (page : ScalarPage.Prepared)
    (values : List Bytes) (lengths : DeltaBinaryPacked.Stream) (payload : List UInt8),
    FlatColumn.pageParameters .optional metadata.codec frame.value = some params ∧ params.encoding = 6 ∧
    ScalarPage.validateFor 6 params limits.delta.page body = .ok layout ∧
    ScalarPage.PreparedWire params limits.delta.page layout body page ∧
    slots.map Option.isSome = page.mask ∧ slots.filterMap id = values ∧ slots.length = params.numValues ∧
    page.scalars.length ≤ limits.delta.lengthByteArray.lengths.bytes ∧
    page.scalars.toList = lengths.wire ++ payload ∧
    page.scalars.length = lengths.wire.length + (values.map Bytes.length).sum ∧
    lengths.Valid .int32 limits.delta.lengthByteArray.lengths (page.mask.count true) ∧
    DeltaLengthByteArray.Assembled limits.delta.lengthByteArray (lengths.reconstruct .int32) payload values ∧
    values.length = page.mask.count true

@[expose] def BinaryWire (checked : Checked int32Name byteArrayName) (limits : Limits) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option Bytes)) : Prop :=
  ∃ column chunk frames pages,
    checked.snapshot.groupAt index = some group ∧
    group.columns[checked.byteArrayBinding.columnOrdinal]? = some column ∧
    column.metadata.pathInSchema = [checked.byteArrayBinding.leaf.name] ∧
    column.metadata.physicalType = .byteArray ∧ column.metadata.numValues = group.numRows ∧
    column.metadata.codec = 0 ∧
    Page.columnSpan checked.snapshot.footer.start column.metadata = some chunk ∧
    Page.readChunk limits.group.column.framing checked.snapshot.bytes chunk = .ok frames ∧
    (frames.map (FlatColumn.pageSlots ∘ Page.Frame.value)).sum = group.numRows.toNat ∧
    List.Forall₂ (PageWire limits column.metadata checked.snapshot.bytes) frames pages ∧
    slots = pages.flatten ∧ slots.length = group.numRows.toNat

/-- Independent page partitions disappear only after both complete ordered
slot lists have been checked for the same footer group. -/
@[expose] def GroupWire (checked : Checked int32Name byteArrayName) (limits : Limits)
    (index : Nat) (rows : List Int32ByteArrayGroup.Row) : Prop :=
  ∃ (group : Footer.RowGroup) (integers : List (Option Int32)) (bytes : List (Option Bytes)),
    FlatColumn.ColumnWire checked.int32Binding limits.group.column
      (Int32ByteArrayGroup.decodeInt32 limits.group .required) index group integers ∧
    BinaryWire checked limits index group bytes ∧
    checked.readInt32 limits.group index = .ok integers ∧ readBinary checked limits index = .ok bytes ∧
    integers.length = bytes.length ∧ rows.length = group.numRows.toNat ∧
    rows = integers.zip bytes ∧ rows.unzip = (integers, bytes)

end Silmaril.Formats.Parquet.Int32ByteArrayGroup.DeltaLength
