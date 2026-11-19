module
public meta import Silmaril.Elf.Corpus.SqliteGlobalVersion.Initialization.Defs
public meta section
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Elf.Corpus.SqliteGlobalVersion
public def main : IO Unit := do
  for sample in List.range 8 do
    let payload : Initialization.Payload := fun j => BitVec.ofNat 8 (sample*31+j.val*13)
    let before ← match Initialization.prepare payload with
      | .ok state => pure state
      | .error e => throw <| IO.userError e
    let result := run Source.Elaboration.core.toFile ∅ 1000 before
    match result.ending with
    | some (.defined (.loaded (.specified (.pointer (.allocated id address))))) =>
      unless id == 1 && address == globalAddress do throw <| IO.userError "actual pointer/provenance mismatch"
    | _ => throw <| IO.userError "actual getter did not return pointer"
    let a := before.memory
    let b := result.finalState.memory
    unless a.enumTypes == b.enumTypes && a.nextId == b.nextId && a.lastAddress == b.lastAddress &&
        a.bytes == b.bytes && a.dead == b.dead && a.lastUsed == b.lastUsed &&
        a.pointerBytes == b.pointerBytes && a.functions == b.functions && a.stdout == b.stdout &&
        a.nextExcluded == b.nextExcluded && a.allocations.keys == b.allocations.keys &&
        (List.range a.nextId.toNat).all (fun id => reprStr (a.allocations.lookup (Int.ofNat id)) == reprStr (b.allocations.lookup (Int.ofNat id))) do
      throw <| IO.userError "complete nondiagnostic source memory changed"
    for j in List.finRange 64 do
      unless Mem.Concrete.readByte (Initialization.unrelatedAddress+j.val) result.finalState.memory.bytes == some ((payload j).toNat : Int) do
        throw <| IO.userError "unrelated initialized payload changed"
    for (byte,j) in globalBytes.zipIdx do
      unless Mem.Concrete.readByte (globalAddress+j) result.finalState.memory.bytes == some (byte.toNat : Int) do
        throw <| IO.userError "actual global bytes mismatch"
  IO.println "PASS8 actual initialized global/getter source executions: real pointer provenance, all7 global bytes, arbitrary sampled64-byte unrelated payload and complete memory after ONLY currentLocation normalization; observations only"
