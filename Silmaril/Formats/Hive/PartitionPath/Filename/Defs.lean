module

public import Silmaril.Formats.Hive.PartitionPath.Positional.Defs

/-! An exact prefix of filename partition tokens followed by an opaque suffix. -/

@[expose] public section

namespace Silmaril.Formats.Hive.PartitionPath.Filename

/-- The last literal underscore separates the prefix from the opaque suffix.
With no underscore there are zero prefix tokens. -/
def prefixTokens (leaf : String) : Except Error (List String) :=
  match (leaf.split '_').toList.reverse.map String.Slice.copy with
  | [] => .error .missingFilenameSuffix
  | suffix :: revPrefix =>
    if suffix.isEmpty then .error .missingFilenameSuffix else .ok revPrefix.reverse

/-- Bound literal leaf bytes and bind their prefix. The parent has already
been checked lexically by manifest admission and supplies no partition cells. -/
def parse (maxFilenameBytes : Nat) (keys : List String) (encoding : Positional.Encoding)
    (options : Options) (_directory leaf : String) : Except Error Partition :=
  if leaf.utf8ByteSize > maxFilenameBytes then
    .error (.filenameByteLimit maxFilenameBytes leaf.utf8ByteSize)
  else (prefixTokens leaf).bind (Positional.parseSegments keys encoding options)

end Silmaril.Formats.Hive.PartitionPath.Filename
