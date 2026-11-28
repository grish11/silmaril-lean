module

meta import Silmaril.Formats.Parquet.Date.Leaf.Events.Defs

open Silmaril Silmaril.Formats Silmaril.Formats.Parquet

private meta def readBack (input : Bytes) (ordinal : Nat) (name : String) (nullable : Bool)
    (expected : List (List (Option Int))) (spans : List (Nat × Nat))
    (path : System.FilePath) : IO Unit := do
  let .ok bound := Date.Leaf.openLeaf {} input ordinal
    | throw (IO.userError "DATE leaf open failed")
  unless bound.ordinal == ordinal && bound.binding.leaf.name == name &&
      bound.nullable == nullable && bound.binding.annotation == .logicalAndConverted do
    throw (IO.userError "DATE leaf binding differed")
  let indices := List.range bound.snapshot.groupCount
  let .ok observed := indices.mapM (fun index => do
      let chunk ← Date.Leaf.selectChunk bound index
      let slots ← Date.Leaf.readGroup {} bound index
      return ((chunk.span.start, chunk.span.stop), slots.map (Option.map Int32.toInt)))
    | throw (IO.userError "DATE selected chunk read failed")
  unless observed.map Prod.fst == spans && observed.map Prod.snd == expected do
    throw (IO.userError "DATE selected intervals or rows differed")
  let .ok ipc := Date.Leaf.Events.toIpc {} {} ordinal input
    | throw (IO.userError "DATE IPC emission failed")
  IO.FS.writeBinFile path ipc.toByteArray

private meta def rejects (input : Bytes) (ordinal : Nat) (expected : Date.Leaf.Events.IpcError)
    (out : Arrow.ObservationLimits := {}) : Bool :=
  match Date.Leaf.Events.toIpc {} out ordinal input with
  | .error actual => actual == expected
  | .ok _ => false

private meta def keepsPrefix (input : Bytes) (ordinal : Nat) (expected : List (Option Int))
    (cause : Date.Leaf.Error) : Bool := Id.run do
  let .ok ⟨schema, trace⟩ := Date.Leaf.Events.readAll {} ordinal input | return false
  let .readError (.groupFailure 1 actual) := trace.termination | return false
  let [batch] := trace.batches | return false
  if width : schema.width = 1 then
    return actual == cause && (batch.values ⟨0, by omega⟩).map (Option.map Int32.toInt) == expected
  return false

private meta def strictRefuses (input : Bytes) : Bool :=
  match Date.openChecked {} input with
  | .error .schemaShape => true
  | _ => false

#guard rejects (Bytes.ofList []) 1 (.source (.openFailure (.snapshot (.footer (.framing .shortFile)))))
