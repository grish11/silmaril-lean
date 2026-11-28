module

public import Silmaril.Formats.Hive.PartitionPath.Filename.Defs

/-! Checked canonical filename prefix rendering for an explicit encoding. -/

@[expose] public section

namespace Silmaril.Formats.Hive.PartitionPath.Filename

/-- An opaque suffix is a nonempty ASCII name of letters, digits, dots or
hyphens. Exclude the two special relative path segments. -/
def safeSuffix (suffix : String) : Bool :=
  !suffix.isEmpty && suffix != "." && suffix != ".." &&
    suffix.toList.all (fun c => c.isAlphanum || c == '-' || c == '.')

def renderToken (options : Options) (encoding : Positional.Encoding) (entry : Entry) : Except Error String :=
  match entry with
  | (key, none) => .error (.filenameNull key)
  | (key, some value) =>
    if value.isEmpty then .error .emptySegment
    else if value == options.nullMarker then .error (.nullMarkerCollision key)
    else
      match encoding with
      | .uri => .ok (Percent.encodeWith true value)
      | .literal =>
        let chars := value.toList
        if '_' ∈ chars ∨ '/' ∈ chars ∨ '\\' ∈ chars ∨ ':' ∈ chars ∨ Char.ofNat 0 ∈ chars then
          .error (.unsafeLiteralFilenameValue key)
        else .ok value

/-- Produce a canonical filename at the given output byte cap. The same
options are used for manifest metadata binding. Null entries and text
equal to the configured canonical marker are refused. -/
def render (maxFilenameBytes : Nat) (keys : List String) (encoding : Positional.Encoding)
    (options : Options) (entries : Partition) (suffix : String) : Except Error String :=
  if !safeSuffix suffix then .error .unsafeFilenameSuffix
  else if options.nullMarker.isEmpty then .error .emptyNullMarker
  else if entries.map Prod.fst != keys then .error .filenameKeyOrder
  else
    (validate options entries).bind fun _ =>
      (entries.mapM (renderToken options encoding)).bind fun tokens =>
        let leaf := "_".intercalate (tokens ++ [suffix])
        if leaf.utf8ByteSize > maxFilenameBytes then
          .error (.filenameByteLimit maxFilenameBytes leaf.utf8ByteSize)
        else .ok leaf

end Silmaril.Formats.Hive.PartitionPath.Filename
