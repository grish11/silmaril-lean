module

meta import Silmaril.Formats.Parquet.Date.PageLess.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet

private meta def strictRejects (wire : Bytes) : Bool :=
  match Date.openChecked {} wire with
  | .error (.snapshot (.invalidMetadata .pageInterval)) => true
  | _ => false

private meta def rejects (wire : Bytes) (cause : Footer.PageLessInt32.Error) : Bool :=
  match Date.openCheckedPageLess {} wire with
  | .error (.inl actual) => actual == cause
  | _ => false

private meta def observe (path : System.FilePath) (wire : Bytes) (name : String) (nullable : Bool)
    (expected : List (List (Option Int))) : IO Unit := do
  let .ok ⟨schema, trace⟩ := Date.PageLess.readAll {} wire
    | throw (IO.userError "DATE page-less event admission failed")
  let .eos := trace.termination | throw (IO.userError "DATE events did not reach EOF")
  if same : schema.width = 1 then
    let col : Fin schema.width := ⟨0, by omega⟩
    if schema.kind col != (name, .date32 nullable) ||
        (trace.batches.map fun batch => (batch.values col).map (Option.map Int32.toInt)) != expected then
      throw (IO.userError "DATE event observation differs")
  else throw (IO.userError "Expected one DATE field")
  let .ok ipc := Date.PageLess.toIpc {} {} wire
    | throw (IO.userError "DATE page-less IPC emission failed")
  IO.FS.writeBinFile path ipc.toByteArray

#guard rejects (Bytes.ofList []) (.footer (.framing .shortFile))
