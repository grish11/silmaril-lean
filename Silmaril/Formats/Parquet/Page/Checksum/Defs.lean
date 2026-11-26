module

public import Silmaril.Formats.Parquet.Page.Defs
public import Silmaril.Formats.Compression.Checksum.Defs

/-! Standalone verification of Parquet CRC-32 on the serialized page body. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Page.Checksum

inductive Status where
  | absent
  | valid (crc : UInt32)
  deriving DecidableEq, Repr

inductive Error where
  | byteLimit
  | invalidExtent
  | mismatch (declared computed : UInt32)
  deriving DecidableEq, Repr

/-- The advertised payload starts immediately after a nonempty header, has
its exact on-disk length, and fits the snapshot. -/
def PayloadWithin (source : Bytes) (frame : Frame) : Prop :=
  frame.header.start < frame.header.stop ∧
    frame.header.stop = frame.payload.start ∧
    frame.payload.stop = frame.payload.start + frame.value.compressedSize ∧
    frame.payload.stop ≤ source.length

instance (source : Bytes) (frame : Frame) : Decidable (PayloadWithin source frame) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The serialized body designated by the frame. Use with a checked extent. -/
def payloadBytes (source : Bytes) (frame : Frame) : Bytes :=
  Footer.fileBytes source frame.payload.start frame.payload.stop

/-- Check a frame from this snapshot before extracting or hashing any bytes.
The parsed header stores the signed Thrift i32's bit pattern as a UInt32.
An absent checksum is reported separately without computing a digest. -/
def verify (maxPayloadBytes : Nat) (source : Bytes) (frame : Frame) : Except Error Status :=
  if maxPayloadBytes < frame.value.compressedSize then .error .byteLimit
  else if ¬ PayloadWithin source frame then .error .invalidExtent
  else
    match frame.value.crc with
    | none => .ok .absent
    | some declared =>
      let computed := Compression.Checksum.crc32.digest (payloadBytes source frame).toList
      if computed = declared then .ok (.valid declared)
      else .error (.mismatch declared computed)

end Silmaril.Formats.Parquet.Page.Checksum
