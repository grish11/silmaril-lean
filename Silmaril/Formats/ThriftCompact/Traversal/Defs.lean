module

public import Silmaril.Formats.ThriftCompact.Defs

/-! Bounded structural traversal for Compact values and unknown fields. -/

public section

namespace Silmaril.Formats.ThriftCompact.Traversal

structure Limits where
  maxBinaryBytes : Nat := 1024 * 1024
  maxCollectionSize : Nat := 65536
  maxStructFields : Nat := 256
  /-- Number of simultaneously open structs, lists, sets and maps. -/
  maxDepth : Nat := 32

inductive Error where
  | compact (error : ThriftCompact.Error)
  | depthLimit
  | fieldLimit
  | elementType (expected actual : ValueType)
  deriving DecidableEq, Repr

structure Reader where
  source : Bytes
  limits : Limits
  mode : VarintMode

abbrev Read (α : Type) := Nat → Except Error (α × Nat)

private def compact {α : Type} (read : Nat → Except ThriftCompact.Error (α × Nat)) : Read α :=
  fun offset => (read offset).mapError .compact

private def foldFields {α : Type} (reader : Reader) (read : Int → FieldType → α → Read α) :
    Nat → Int → α → Read α
  | budget, previous, acc, offset => do
    let (header, next) ← compact (readFieldHeader reader.mode previous reader.source) offset
    match header with
    | .stop => pure (acc, next)
    | .field id type =>
      match budget with
      | 0 => throw .fieldLimit
      | budget + 1 =>
        let (acc, next) ← read id type acc next
        foldFields reader read budget id acc next

private def skipMany (skip : Read Unit) : Nat → Read Unit
  | 0, offset => .ok ((), offset)
  | count + 1, offset => do
    let (_, next) ← skip offset
    skipMany skip count next

private def skipBinary (reader : Reader) : Read Unit := fun offset => do
  let (count, start) ← compact
    (readLength reader.mode reader.limits.maxBinaryBytes reader.source) offset
  let next := start + count
  if next ≤ reader.source.length then pure ((), next) else throw (.compact .truncated)

private def skipValue (reader : Reader) (depth : Nat) (type : ValueType) : Read Unit :=
  match type with
  | .bool => discardValue (readBool reader.source)
  | .i8 => discardValue (readI8 reader.source)
  | .i16 => discardValue (readSigned .i16 reader.mode reader.source)
  | .i32 => discardValue (readSigned .i32 reader.mode reader.source)
  | .i64 => discardValue (readSigned .i64 reader.mode reader.source)
  | .double => discardValue (readFixed 8 reader.source)
  | .uuid => discardValue (readFixed 16 reader.source)
  | .binary => skipBinary reader
  | .struct | .list | .set | .map =>
    match depth with
    | 0 => fun _ => .error .depthLimit
    | depth + 1 =>
      let skip := skipValue reader depth
      fun offset =>
        match type with
        | .struct => foldFields reader (fun _ type _ => skipField skip type)
            reader.limits.maxStructFields 0 () offset
        | .map => do
          let (header, next) ← compact
            (readMapHeader reader.mode reader.limits.maxCollectionSize reader.source) offset
          match header with
          | .empty => pure ((), next)
          | .entries size key value =>
            skipMany (fun start => do
              let (_, next) ← skip key start
              skip value next) size next
        | _ => do
          let (header, next) ← compact
            (readCollectionHeader reader.mode reader.limits.maxCollectionSize reader.source) offset
          skipMany (skip header.elementType) header.size next
where
  discardValue {α : Type} (read : Nat → Except ThriftCompact.Error (α × Nat)) : Read Unit :=
    fun offset => do
      let (_, next) ← compact read offset
      pure ((), next)
  skipField (skip : ValueType → Read Unit) : FieldType → Read Unit
    | .bool _ => fun offset => .ok ((), offset)
    | .payload type => skip type

/-- The payload span of an immediate struct field. An inline boolean has an empty span. -/
structure Field where
  id : Int
  type : FieldType
  start : Nat
  stop : Nat

/-- Index the immediate fields in wire order, checking and skipping their values. The
returned offset is the first octet after STOP. Each nested struct starts with field ID zero. -/
def readStruct (reader : Reader) : Read (List Field) := fun offset => do
  let depth + 1 := reader.limits.maxDepth | throw .depthLimit
  let (fields, next) ← foldFields reader (fun id type fields start => do
    let (_, stop) ← skipValue.skipField (skipValue reader depth) type start
    pure (⟨id, type, start, stop⟩ :: fields, stop)) reader.limits.maxStructFields 0 [] offset
  pure (fields.reverse, next)

/-- Read a list of the expected wire type, including the type check for an empty list. -/
def readList {α ε : Type} (reader : Reader) (error : Error → ε) (type : ValueType)
    (read : Nat → Except ε (α × Nat)) : Nat → Except ε (List α × Nat) := fun offset => do
  let (header, next) ← (compact
    (readCollectionHeader reader.mode reader.limits.maxCollectionSize reader.source) offset).mapError error
  if header.elementType ≠ type then throw (error (.elementType type header.elementType))
  go header.size [] next
where
  go : Nat → List α → Nat → Except ε (List α × Nat)
    | 0, acc, offset => .ok (acc.reverse, offset)
    | size + 1, acc, offset => do
      let (value, next) ← read offset
      go size (value :: acc) next

end Silmaril.Formats.ThriftCompact.Traversal
