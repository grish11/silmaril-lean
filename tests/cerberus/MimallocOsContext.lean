module
public meta import Silmaril.Elf.Corpus.MimallocOsGlobals.Context.Defs
public meta import Silmaril.Cerberus.Core.Outcome.Defs
public meta section
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Elf.Corpus.MimallocOsGlobals

private def check (g : Getter) (page large : Nat) : IO Unit := do
  let i : Context.Input := ⟨BitVec.ofNat 64 page, BitVec.ofNat 64 large⟩
  let s ← match Context.prepare g i with
    | .ok s => pure s
    | .error e => throw <| IO.userError e
  let F := Source.Elaboration.function g
  let result := run F.file ∅ 100000 s
  let expected := if g == .page || large == 0 then page else large
  match result.ending with
  | some (.defined (.loaded (.specified (.integer got)))) =>
      unless got == expected do throw <| IO.userError s!"wrong actual Core result {got}, expected {expected}"
  | ending => throw <| IO.userError s!"actual Core failed: {(observation ending).json.compress}"
  unless Context.readField "page_size" result.finalState == some (page : Int) &&
      Context.readField "large_page_size" result.finalState == some (large : Int) do
    throw <| IO.userError "caller-visible fields changed"
  for offset in List.range 48 do
    unless Mem.Concrete.readByte (globalAddress + offset) result.finalState.memory.bytes ==
        Mem.Concrete.readByte (globalAddress + offset) s.memory.bytes do
      throw <| IO.userError "global bytes changed"
  unless result.finalState.memory.nextId == s.memory.nextId &&
      result.finalState.memory.dead == s.memory.dead && result.finalState.memory.stdout == s.memory.stdout do
    throw <| IO.userError "allocation/lifetime/stdout changed"
  IO.println s!"PASS {g.name} page={page} large={large} transitions={result.actions.length}"

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
  for page in [0, 4096, 65536, 9223372036854775808, 18446744073709551615] do
    for large in [0, 2097152, 18446744073709551615] do
      for g in [Getter.page, Getter.largePage] do check g page large
  let s ← match Context.prepare .largePage ⟨4096, 0⟩ with
    | .ok s => pure s
    | .error e => throw <| IO.userError e
  let F := Source.Elaboration.function .largePage
  let reduced := {F.file with funs := Map.ofList (Source.Elaboration.core.funs.filter
    (fun (symbol, _) => symbol.description != .id "_mi_os_page_size"))}
  match (run reduced ∅ 100000 s).ending with
  | some (.defined _) => throw <| IO.userError "missing actual source callee was accepted"
  | none => throw <| IO.userError "missing-callee test exhausted fuel"
  | some _ => IO.println "PASS removing actual page-size callee rejects zero branch"
  let missing := {s with memory := {}}
  match (run F.file ∅ 100000 missing).ending with
  | some (.defined _) => throw <| IO.userError "missing global allocation was accepted"
  | none => throw <| IO.userError "missing-allocation test exhausted fuel"
  | some _ => IO.println "PASS missing global allocation rejected"
