module
public meta import Silmaril.Elf.Corpus.SqliteBuildQueries.Context.Defs
public meta import Silmaril.Cerberus.Core.Outcome.Defs
public meta section
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Elf.Corpus.SqliteBuildQueries
public def main : IO Unit := do
  for g in [Getter.versionNumber, Getter.threadsafe] do
    let s := Context.prepare g
    let F := Source.Elaboration.function g
    unless F.params.isEmpty && F.file.globs.isEmpty do
      throw <| IO.userError "unexpected actual parameters or globals"
    let result := run F.file ∅ 100000 s
    let expected : Int := if g == .versionNumber then 3054001 else 1
    match result.ending with
    | some (.defined (.loaded (.specified (.integer got)))) =>
      unless got == expected do throw <| IO.userError s!"wrong actual build query result {got}"
    | ending => throw <| IO.userError s!"actual Core failed: {(observation ending).json.compress}"
    unless result.finalState.memory.bytes == s.memory.bytes &&
        result.finalState.memory.nextId == s.memory.nextId &&
        result.finalState.memory.dead == s.memory.dead &&
        result.finalState.memory.stdout == s.memory.stdout do
      throw <| IO.userError "pure query changed observable source memory/lifetimes/stdout"
    IO.println s!"PASS {g.name} actual Core result={expected}; preserved memory; no globals or parameters"
