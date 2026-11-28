module

public import Silmaril.Formats.Arrow.BinaryView.Stream.Defs
public import Silmaril.Formats.Parquet.Footer.Metadata.Defs
public import Silmaril.Formats.Parquet.Page.Header.Defs
public import Silmaril.Formats.Parquet.ScalarPage.Defs
public import Silmaril.Semantics.Relational.Scan.Defs

/-! Common ordered octet observations from one BinaryView IPC field or
one declared flat Parquet BYTE_ARRAY column's supplied page windows. -/

@[expose] public section

namespace Silmaril.Formats.Relational.BinaryObservation

open Silmaril.Relational
open Arrow.BinaryView Parquet

structure Field where
  name : String
  nullable : Bool
  deriving DecidableEq, Repr

abbrev Slot := Option (List UInt8)
abbrev Cell (_ : Bool) := List UInt8
abbrev Observation := Scan.Observation String Cell

def Field.schema (field : Field) : Scan.Schema String Bool :=
  ⟨1, fun _ => (field.name, field.nullable)⟩

def observation (field : Field) (slots : List Slot) : Observation :=
  ⟨field.schema, slots.map fun slot _ => slot⟩

def ipcSlots (batches : List (List (Option KBytes))) : List Slot :=
  batches.flatten.map (Option.map KBytes.toList)

inductive IpcError where
  | reader (cause : Stream.Error)
  | fieldMismatch (actual : Field)
  | utf8View
  deriving DecidableEq, Repr

/-- Consume the existing checked IPC stream through exact EOS, preserving
its original failure. Then bind the sole BinaryView field and normalize its cells. -/
def observeIpc (expected : Field) (ipc : Arrow.Limits) (limits : Column.Limits)
    (input : KBytes) : Except IpcError Observation :=
  match Stream.read ipc limits input with
  | .error cause => .error (.reader cause)
  | .ok ⟨⟨name, nullable, .binary⟩, batches⟩ =>
    let actual : Field := ⟨name, nullable⟩
    if actual = expected then .ok (observation actual (ipcSlots batches))
    else .error (.fieldMismatch actual)
  | .ok ⟨⟨_, _, .utf8⟩, _⟩ => .error .utf8View

/-- Caller declarations for the selected column. Exact name and nullability
are checked against the requested descriptor. -/
structure ParquetColumn where
  field : Field
  physicalType : Footer.PhysicalType
  codec : Int
  levels : FlatPage.LevelSchema
  deriving DecidableEq, Repr

/-- Projected page header and exact body supplied by the caller. This
boundary carries no information about file membership or offsets. -/
structure PageWindow where
  header : Page.Header
  body : Bytes

structure PageLimits where
  scalar : ScalarPage.Limits
  values : Plain.ByteArray.Limits

inductive PageError where
  | pageKind (actual : Page.Kind)
  | crcUnsupported
  | scalar (cause : ScalarPage.Error)
  deriving DecidableEq, Repr

inductive ParquetError where
  | fieldMismatch (actual : Field)
  | physicalType (actual : Footer.PhysicalType)
  | codec (actual : Int)
  | levels (actual : FlatPage.LevelSchema)
  | page (index : Nat) (cause : PageError)
  deriving DecidableEq, Repr

def Field.levels (field : Field) : FlatPage.LevelSchema :=
  ⟨0, if field.nullable then 1 else 0⟩

def checkColumn (expected : Field) (column : ParquetColumn) : Except ParquetError Unit :=
  if column.field ≠ expected then .error (.fieldMismatch column.field)
  else if column.physicalType ≠ .byteArray then .error (.physicalType column.physicalType)
  else if column.codec ≠ 0 then .error (.codec column.codec)
  else if column.levels ≠ expected.levels then .error (.levels column.levels)
  else .ok ()

def pageParameters (field : Field) (header : Page.Header) (data : Page.DataV2) :
    ScalarPage.Parameters :=
  ⟨⟨header.compressedSize, header.uncompressedSize⟩, field.levels, data.numValues,
    0, data.encoding, .v2 data.numNulls data.numRows data.repetitionBytes data.definitionBytes
      (some data.isCompressed)⟩

/-- Decode a supplied PLAIN V2 body through the scalar page boundary. -/
def readPage (field : Field) (limits : PageLimits) (window : PageWindow) :
    Except PageError (List Slot) := do
  let .dataV2 data := window.header.kind | throw (.pageKind window.header.kind)
  if window.header.crc.isSome then throw .crcUnsupported
  else
    let slots ← (ScalarPage.decode (.byteArray limits.values)
      (pageParameters field window.header data) limits.scalar window.body).mapError .scalar
    return slots.map (Option.map Bytes.toList)

/-- Read supplied windows in order. The first failed page returns its
ordinal and cause before any later page is examined. -/
def readPages (field : Field) (limits : PageLimits) :
    Nat → List PageWindow → Except ParquetError (List (List Slot))
  | _, [] => .ok []
  | index, window :: rest => do
    let slots ← (readPage field limits window).mapError (.page index)
    let later ← readPages field limits (index + 1) rest
    return slots :: later

/-- Check the supplied column declaration and all supplied page windows.
The observation covers those windows in caller order. -/
def observeParquet (expected : Field) (limits : PageLimits) (column : ParquetColumn)
    (windows : List PageWindow) : Except ParquetError Observation := do
  checkColumn expected column
  let pages ← readPages expected limits 0 windows
  return observation expected pages.flatten

end Silmaril.Formats.Relational.BinaryObservation
