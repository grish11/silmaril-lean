module

meta import Silmaril.Formats.Arrow.DateStream.FromCsv.Defs

open Silmaril.Formats
open Arrow
open DateStream.FromCsv

private meta def bytes (value : String) : Csv.Bytes := value.toUTF8.data.toList

private meta def bounds : CsvLimits := ⟨1024, 32⟩

private meta def rejects (input : Csv.Bytes) (nullable : Bool) (cause : DateStream.FromCsv.Error)
    (csv : CsvLimits := bounds) (ipc : ObservationLimits := {}) : Bool :=
  match convert ipc csv "日付" nullable input with
  | .error actual => actual == cause
  | .ok _ => false

private meta def emitFixture (input : Csv.Bytes) (name : String) (nullable : Bool)
    (expected : List (Option Int)) (path : String) : IO Unit := do
  let .ok wire := convert {} bounds name nullable input
    | throw (IO.userError "Date32 CSV conversion failed")
  let .ok stream := DateStream.read {} wire
    | throw (IO.userError "Date32 IPC readback failed")
  let batches := stream.batches.map (List.map fun slot =>
    (slot.bind DateInterop.Date32.ofCivil?).map Int32.toInt)
  if stream.field != ⟨name, nullable, .day⟩ || batches != [expected] then
    throw (IO.userError "Date32 IPC readback mismatch")
  IO.FS.writeBinFile path wire.toByteArray

#guard rejects [] true (.csv (.csv .missingHeader)) ⟨0, 0⟩
#guard rejects (bytes "x") true (.csvByteLimit 1 0) ⟨0, 0⟩
#guard rejects (bytes "other\r\nN\r\n") true (.csv (.csv .headerMismatch)) ⟨1024, 0⟩
#guard rejects (bytes "日付\r\nN\r\n") true (.csvRowLimit 1 0) ⟨1024, 0⟩
  { ipc := { batches := 0 } }
#guard rejects (bytes "日付\r\n") true (.writer (.writer (.limit .batches))) ⟨8, 0⟩
  { ipc := { batches := 0 } }
#guard rejects (bytes "日付\r\nN\r\n") false (.csv (.requiredNull 0 0)) ⟨1024, 0⟩
#guard rejects (bytes "日付\r\nN,\r\n") true (.csv (.csv (.width 1 2)))
#guard rejects (bytes "日付\r\nT\r\n") true (.csv (.csv (.parseCell 0)))
#guard rejects (bytes "日付\r\n" ++ [0x54, 0xC0, 0xAF, 0x0D, 0x0A]) true
  (.csv (.csv .malformedWire))
