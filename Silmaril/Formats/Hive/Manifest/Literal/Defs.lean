module

public import Silmaril.Formats.Hive.Manifest.Defs

/-! Bounded literal Hive file admission. Percent spellings are text in this
reader profile, as in PyArrow's Hive `segment_encoding="none"` mode. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest.Literal

open TypedPartitions (PartitionSchema Convert)

def value (options : PartitionPath.Options) (raw : String) : Option String :=
  if raw == options.nullMarker then none else some raw

def parseSegment (options : PartitionPath.Options) (segment : String) :
    Except PartitionPath.Error PartitionPath.Entry := do
  if segment.isEmpty then throw .emptySegment
  let (key, suffix) := segment.toList.span (· != '=')
  let '=' :: raw := suffix | throw (.missingEquals segment)
  if key.isEmpty then throw .emptyKey
  return (String.ofList key, value options (String.ofList raw))

/-- Apply the strict relative-directory and key policy to literal strings. -/
def parse (options : PartitionPath.Options) (directory : String) :
    Except PartitionPath.Error PartitionPath.Partition := do
  if options.nullMarker.isEmpty then throw .emptyNullMarker
  let entries ← if directory.isEmpty then pure [] else
    (directory.splitOn "/").mapM (parseSegment options)
  PartitionPath.validate options entries
  return entries

inductive Error (Failure : Type*) where
  | pathByteLimit (maximum actual : Nat)
  | prepare (reason : PrepareError Failure)
  deriving BEq, Repr

/-- Bound the original UTF-8 file path, then lexically split and bind it.
The canonical directory uses the library's internal URI rendering. The
resolver still receives the complete original spelling. -/
def prepareFile {Kind : Type*} {Value : Kind → Type*} {Failure : Type*}
    (schema : PartitionSchema Kind) (maxPathBytes : Nat) (options : PartitionPath.Options)
    (convert : Convert Value Failure) (declared : String) :
    Except (Error Failure) (File schema Value) :=
  if declared.utf8ByteSize > maxPathBytes then .error (.pathByteLimit maxPathBytes declared.utf8ByteSize)
  else (prepareFileWith schema parse options convert declared).mapError Error.prepare

end Silmaril.Formats.Hive.Manifest.Literal
