module

public import Silmaril.Formats.Parquet.Footer.Defs
public import Silmaril.Formats.ColumnarTimestamp.Wire.Defs

/-! # Parquet TIMESTAMP annotations on selected INT64 schema leaves -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp

open ThriftCompact
open Traversal (Reader Field)

abbrev Descriptor := ColumnarTimestamp.Parquet.Metadata

/-- Legacy converted-only INT64 timestamps require explicit opt-in. -/
inductive AnnotationProfile where
  | modernOnly
  | allowConvertedOnly

inductive Error where
  | footer (error : Footer.Error)
  | traversal (error : Traversal.Error)
  | missingField (id : Int)
  | duplicateField (id : Int)
  | fieldType (id : Int)
  | fieldExtent (id : Int)
  | schemaIndex (index : Nat)
  | notInt64Leaf
  | logicalUnion
  | timestampFields
  | unitUnion
  | convertedType (code : Int)
  deriving DecidableEq, Repr

structure Binding where
  leaf : Footer.SchemaElement
  descriptor : Descriptor

/-- A legacy annotation alongside a modern one must agree on the unit. The
    modern `isAdjustedToUTC` flag controls interpretation in either case. -/
def compatibleConvertedType (unit : ColumnarTimestamp.Parquet.TimeUnit) (code : Int) : Bool :=
  match unit with
  | .millis => code == 9
  | .micros => code == 10
  | .nanos => false

namespace Internal

abbrev Read (α : Type) := Nat → Except Error (α × Nat)

def structFields (reader : Reader) : Read (List Field) := fun offset =>
  (Traversal.readStruct reader offset).mapError .traversal

def optionalField (fields : List Field) (id : Int) : Except Error (Option Field) :=
  match fields.filter (·.id == id) with
  | [] => .ok none
  | [field] => .ok (some field)
  | _ => .error (.duplicateField id)

def requiredField (fields : List Field) (id : Int) : Except Error Field := do
  let some value ← optionalField fields id | throw (.missingField id)
  return value

def payload {α : Type} (field : Field) (type : ValueType) (read : Read α) : Except Error α := do
  if field.type ≠ .payload type then throw (.fieldType field.id)
  let (value, next) ← read field.start
  if next ≠ field.stop then throw (.fieldExtent field.id)
  return value

def boolField (field : Field) : Except Error Bool :=
  match field.type with
  | .bool value => .ok value
  | _ => .error (.fieldType field.id)

def integer (reader : Reader) (field : Field) : Except Error Int :=
  payload field .i32 fun offset =>
    (readSigned .i32 reader.mode reader.source offset).mapError (.traversal ∘ .compact)

/-- The schema is kept in its serialized depth-first order, including the root. -/
def schemaFields (reader : Reader) : Except Error (List (List Field)) := do
  let (metadata, next) ← structFields reader 0
  if next ≠ reader.source.length then throw (.footer .trailingMetadata)
  let schema ← requiredField metadata 2
  payload schema .list (Traversal.readList reader .traversal .struct (structFields reader))

def timeUnit (reader : Reader) (field : Field) : Except Error ColumnarTimestamp.Parquet.TimeUnit := do
  let [member] ← payload field .struct (structFields reader) | throw .unitUnion
  let [] ← payload member .struct (structFields reader) | throw .unitUnion
  match member.id with
  | 1 => return .millis
  | 2 => return .micros
  | 3 => return .nanos
  | _ => throw .unitUnion

def logicalTimestamp (reader : Reader) (field : Field) : Except Error Descriptor := do
  let [member] ← payload field .struct (structFields reader) | throw .logicalUnion
  if member.id ≠ 8 then throw .logicalUnion
  let fields ← payload member .struct (structFields reader)
  let adjusted ← (← requiredField fields 1) |> boolField
  let unit ← (← requiredField fields 2) |> timeUnit reader
  if fields.length ≠ 2 then throw .timestampFields
  return ⟨unit, adjusted⟩

def annotation (reader : Reader) (fields : List Field) : Except Error Descriptor := do
  let descriptor ← logicalTimestamp reader (← requiredField fields 10)
  match ← optionalField fields 6 with
  | none => return descriptor
  | some field =>
    let code ← integer reader field
    if compatibleConvertedType descriptor.unit code then return descriptor
    else throw (.convertedType code)

/-- The historical ConvertedType contract uses the UTC epoch. -/
def convertedTimestamp (code : Int) : Except Error Descriptor :=
  match code with
  | 9 => .ok ⟨.millis, true⟩
  | 10 => .ok ⟨.micros, true⟩
  | _ => .error (.convertedType code)

def annotationWith (profile : AnnotationProfile) (reader : Reader) (fields : List Field) :
    Except Error Descriptor :=
  match profile with
  | .modernOnly => annotation reader fields
  | .allowConvertedOnly => do
    match ← optionalField fields 10 with
    | some _ => annotation reader fields
    | none =>
      let field ← requiredField fields 6
      convertedTimestamp (← integer reader field)

end Internal

/-- Decode the selected annotation from an exact FileMetaData slice. `index`
    names a node in the serialized schema, with the root at index zero.
    The typed leaf and raw annotation are selected from the same footer bytes. -/
def readMetadataWith (profile : AnnotationProfile) (limits : Footer.Limits) (index : Nat)
    (bytes : Bytes) : Except Error Binding :=
  if limits.maxFooterBytes < bytes.length then .error (.footer (.framing .footerLimit)) else do
    let footer ← (Footer.readMetadata limits bytes).mapError .footer
    let some leaf := footer.schema[index]? | throw (.schemaIndex index)
    if index ≠ 0 ∧ leaf.physicalType = some .int64 ∧ leaf.numChildren.getD 0 = 0 ∧
        leaf.repetition.isSome = true then
      let reader : Reader := ⟨bytes, limits.compact, limits.varintMode⟩
      let schema ← Internal.schemaFields reader
      let some fields := schema[index]? | throw (.schemaIndex index)
      let descriptor ← Internal.annotationWith profile reader fields
      return ⟨leaf, descriptor⟩
    else .error .notInt64Leaf

/-- Decode only the modern annotation from an exact FileMetaData slice. -/
def readMetadata (limits : Footer.Limits) (index : Nat) (bytes : Bytes) : Except Error Binding :=
  readMetadataWith .modernOnly limits index bytes

/-- Locate the plaintext footer of the supplied file and bind the indexed leaf.
    Page intervals and association of values to a leaf are separate checks. -/
def readFooter (limits : Footer.Limits) (index : Nat) (file : Bytes) : Except Error Binding := do
  let span ← (Footer.locate limits.maxFooterBytes file).mapError (.footer ∘ .framing)
  readMetadata limits index (Footer.fileBytes file span.start span.stop)

/-- Interpret an already delimited INT64 PLAIN values slice for this leaf. The
    page layer supplies the present value count and associates the slice to the leaf. -/
abbrev Binding.decodePlain (binding : Binding) (count : Nat) (bytes : Bytes) :=
  binding.descriptor.decodePlain count bytes

end Silmaril.Formats.Parquet.Timestamp
