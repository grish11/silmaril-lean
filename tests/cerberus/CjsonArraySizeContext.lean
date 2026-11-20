module
public import Silmaril.Elf.Corpus.CjsonArraySize.Context.Defs
public import Silmaril.Cerberus.Core.Outcome.Defs
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Elf.Corpus.CjsonArraySize
public def main : IO Unit := do
  unless reprStr Source.Elaboration.core.funs == reprStr Source.programDocument.bindings.funs &&
      reprStr Source.Elaboration.core.funInfo == reprStr Source.programDocument.bindings.funInfo do
    throw <| IO.userError "saved traversal Core/procedure metadata differ from actual elaboration"
  let F := Source.Elaboration.function
  let inputs := Context.Input.null :: (List.finRange 65).map Context.Input.list
  for input in inputs do
    let before ← match Context.prepare input with
      | .ok state => pure state
      | .error why => throw <| IO.userError why
    let result := run F.file ∅ 2000000 before
    match result.ending with
    | some (.defined (.loaded (.specified (.integer got)))) =>
        unless got == input.length do throw <| IO.userError s!"actual traversal result {got} for {reprStr input}"
    | ending => throw <| IO.userError s!"actual traversal {reprStr input}: {(observation ending).json.compress}"
    let after := result.finalState.memory
    unless after.enumTypes == before.memory.enumTypes && after.functions == before.memory.functions &&
        after.stdout == before.memory.stdout do throw <| IO.userError "caller registrations or output changed"
    for index in List.range (input.length+1) do
      let id : Int := index+1
      unless reprStr (before.memory.allocations.lookup id) == reprStr (after.allocations.lookup id) &&
          before.memory.dead.contains id == after.dead.contains id do
        throw <| IO.userError "caller allocation or lifetime changed"
      for offset in List.range 64 do
        let address : Int := Context.heapAddress index + offset
        unless before.memory.bytes.lookup address == after.bytes.lookup address &&
            before.memory.pointerBytes.lookup address == after.pointerBytes.lookup address do
          throw <| IO.userError "caller byte or pointer provenance changed"
    unless after.nextId == before.memory.nextId + 2 &&
        after.dead.contains before.memory.nextId && after.dead.contains (before.memory.nextId+1) do
      throw <| IO.userError "actual two automatic locals were not allocated and killed"
    if input == .list ⟨1, by decide⟩ then
      let invalid := {before with memory := {before.memory with allocations := before.memory.allocations.erase 2}}
      match (run F.file ∅ 2000000 invalid).ending with
      | some (.defined _) => throw <| IO.userError "missing child allocation accepted"
      | none => throw <| IO.userError "invalid case exhausted fuel"
      | some (.unsupported why) =>
          unless why == "outside allocation lifetime UB mapping" do
            throw <| IO.userError s!"unexpected unsupported invalid case: {why}"
      | some _ => pure ()
  IO.println "PASS actual cJSON_GetArraySize on null and all65 acyclic lengths0..64: real readonly heap/provenance preserved, two automatic locals allocated/killed, missing-allocation rejection retains explicit unsupported UB mapping outside the domain; finite execution is not a contextual or termination proof"
