module
public meta import Silmaril.Elf.Corpus.MimallocOsFlags.Context.Defs
public meta import Silmaril.Cerberus.Core.Outcome.Defs
public meta section
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Elf.Corpus.MimallocOsFlags
private def check (g : Getter) (overcommit reserve : Bool) : IO Unit := do
  let s ← match Context.prepare g ⟨overcommit, reserve⟩ with
    | .ok s => pure s
    | .error e => throw <| IO.userError e
  let F := Source.Elaboration.function g
  let result := run F.file ∅ 100000 s
  let expected : Int := cond (if g == .overcommit then overcommit else reserve) 1 0
  match result.ending with
  | some (.defined (.loaded (.specified (.integer got)))) =>
    unless got == expected do throw <| IO.userError s!"wrong actual Boolean result {got}"
  | ending => throw <| IO.userError s!"actual Core failed: {(observation ending).json.compress}"
  unless result.finalState.memory.bytes == s.memory.bytes &&
      result.finalState.memory.nextId == s.memory.nextId &&
      result.finalState.memory.dead == s.memory.dead &&
      result.finalState.memory.stdout == s.memory.stdout do
    throw <| IO.userError "read-only getter changed caller-visible memory"
  let missing := {s with memory := {}}
  match (run F.file ∅ 100000 missing).ending with
  | some (.defined _) => throw <| IO.userError "missing global allocation accepted"
  | none => throw <| IO.userError "negative case exhausted fuel"
  | some _ => pure ()
  IO.println s!"PASS {g.name} overcommit={overcommit} reserve={reserve}; preserved memory; missing allocation rejected"
private def initialization : IO Unit := do
  let [(global, .definition _ initializer)] := Source.Elaboration.core.globs
    | throw <| IO.userError "expected actual global initializer"
  let _ := global
  let result := run Source.Elaboration.core.toFile ∅ 300000
    ⟨.effectExpr initializer ∅, [], {}⟩
  let pointer ← match result.ending with
    | some (.defined (.object (.pointer pointer))) => pure pointer
    | ending => throw <| IO.userError s!"actual initializer failed: {(observation ending).json.compress}"
  let [(tag, _)] := Source.Elaboration.core.tagDefs
    | throw <| IO.userError "expected actual struct tag"
  let aggregate : Ctype := .mk [] (.struct tag)
  let layout ← match Mem.Concrete.typeLayout 64 Source.Elaboration.core.toFile.tagDefs aggregate with
    | .ok layout => pure layout
    | .error _ => throw <| IO.userError "actual layout failed"
  let .allocated id address := pointer | throw <| IO.userError "initializer returned non-object pointer"
  for (name, expected) in [("page_size", 4096), ("large_page_size", 0),
      ("alloc_granularity", 4096), ("physical_memory", 34359738368),
      ("virtual_address_bits", 48), ("has_overcommit", 1),
      ("has_partial_free", 0), ("has_virtual_reserve", 1)] do
    let some (_, type, offset) := layout.members.find? (fun (member, _, _) => member.key == name)
      | throw <| IO.userError "missing actual member"
    match Mem.Concrete.loadTyped Source.Elaboration.core.toFile.tagDefs result.finalState.memory type
        (.allocated id (address + offset)) with
    | .ok (.integer _ got, _) =>
      unless got == expected do throw <| IO.userError s!"initializer {name}: {got}"
    | _ => throw <| IO.userError s!"initializer member read failed: {name}"
  IO.println s!"PASS actual eight-field global initialization, transitions={result.actions.length}"

public def main : IO Unit := do
  initialization
  for overcommit in [false, true] do
    for reserve in [false, true] do
      for g in [Getter.overcommit, Getter.virtualReserve] do check g overcommit reserve
