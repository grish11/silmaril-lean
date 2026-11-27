module

public import Silmaril.Formats.Hive.PartitionPath.Positional.Defs

/-! Canonical rendering for the opt-in exact-arity directory profile. -/

@[expose] public section

namespace Silmaril.Formats.Hive.PartitionPath.Positional

/-- Output byte caps. Directory bytes include the literal separators. -/
structure RenderLimits where
  maxDirectoryBytes : Nat
  maxSegmentBytes : Nat
  deriving Repr

inductive RenderError where
  | partition (reason : Error)
  | keyOrder
  | nullValue (key : String)
  | unsafeSegment (key : String)
  | segmentByteLimit (key : String) (maximum actual : Nat)
  deriving BEq, Repr

/-- Recognize unsafe encoded components for a relative path. -/
def unsafeSegment (segment : String) : Prop :=
  segment = "." ∨ segment = ".." ∨ '/' ∈ segment.toList ∨ '\\' ∈ segment.toList ∨
    ':' ∈ segment.toList ∨ Char.ofNat 0 ∈ segment.toList

instance (segment : String) : Decidable (unsafeSegment segment) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

def encodeSegment (encoding : Encoding) (value : String) : String :=
  match encoding with
  | .uri => Percent.encode value
  | .literal => value

/-- Encode one present value and check the resulting component and byte cap. -/
def renderSegment (maxSegmentBytes : Nat) (encoding : Encoding) (options : Options)
    (entry : Entry) : Except RenderError String := do
  let (key, value) := entry
  let some text := value | throw (.nullValue key)
  if text == options.nullMarker then throw (.partition (.nullMarkerCollision key))
  let segment := encodeSegment encoding text
  if segment.isEmpty then throw (.partition .emptySegment)
  if unsafeSegment segment then throw (.unsafeSegment key)
  if segment.utf8ByteSize > maxSegmentBytes then
    throw (.segmentByteLimit key maxSegmentBytes segment.utf8ByteSize)
  return segment

/-- Render exact ordered keys as a relative directory. Null entries and text
equal to the configured canonical Hive null marker are refused. -/
def render (limits : RenderLimits) (keys : List String) (encoding : Encoding)
    (options : Options) (entries : Partition) : Except RenderError String := do
  if options.nullMarker.isEmpty then throw (.partition .emptyNullMarker)
  if entries.map Prod.fst != keys then throw .keyOrder
  (validate options entries).mapError RenderError.partition
  let raw ← entries.mapM (renderSegment limits.maxSegmentBytes encoding options)
  let directory := "/".intercalate raw
  if directory.utf8ByteSize > limits.maxDirectoryBytes then
    throw (.partition (.directoryByteLimit limits.maxDirectoryBytes directory.utf8ByteSize))
  return directory

end Silmaril.Formats.Hive.PartitionPath.Positional
