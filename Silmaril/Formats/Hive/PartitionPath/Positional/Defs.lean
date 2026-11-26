module

public import Silmaril.Formats.Hive.PartitionPath.Defs

/-! Bounded, exact-arity positional partitions with an explicit segment encoding. -/

@[expose] public section

namespace Silmaril.Formats.Hive.PartitionPath.Positional

inductive Encoding where
  | uri
  | literal
  deriving Repr

/-- The empty directory has zero positions. Interior empty segments are retained
here and rejected by segment validation. -/
def segments (directory : String) : List String :=
  if directory.isEmpty then [] else directory.splitOn "/"

def decodeSegment (encoding : Encoding) (segment : String) : Except Error String :=
  if segment.isEmpty then .error .emptySegment
  else
    match encoding with
    | .uri => Percent.decode segment
    | .literal => .ok segment

/-- Pair the given keys with the directory values in order. Position counts
are checked before decoding. Every admitted value is present, even sentinel
text. The inherited options supply required keys. -/
def parse (maxDirectoryBytes : Nat) (keys : List String) (encoding : Encoding)
    (options : Options) (directory : String) : Except Error Partition :=
  if directory.utf8ByteSize > maxDirectoryBytes then
    .error (.directoryByteLimit maxDirectoryBytes directory.utf8ByteSize)
  else
    let raw := segments directory
    if raw.length != keys.length then .error (.segmentArity keys.length raw.length)
    else
      (raw.mapM (decodeSegment encoding)).bind fun values =>
        let entries := keys.zip (values.map some)
        (validate options entries).map fun _ => entries

end Silmaril.Formats.Hive.PartitionPath.Positional
