module
public meta import Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Context.Defs
public meta import Silmaril.Cerberus.Core.Outcome.Defs
public meta section
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Elf.Corpus.DarkhttpdLogEncoding
public def main : IO Unit := do
  unless reprStr Source.Elaboration.core.funs == reprStr Source.programDocument.bindings.funs &&
      reprStr Source.Elaboration.core.funInfo == reprStr Source.programDocument.bindings.funInfo do
    throw <| IO.userError "saved Core/procedure metadata differ from actual elaboration"
  let F := Source.Elaboration.function
  unless F.params.length == 1 && F.file.globs.isEmpty do
    throw <| IO.userError "unexpected actual parameter/global closure"
  for n in List.range 256 do
    let input := BitVec.ofNat 8 n
    let s ← match Context.prepare input with
      | .ok s => pure s
      | .error why => throw <| IO.userError why
    let result := run F.file ∅ 100000 s
    let expected : Int := if n ≤ 31 || n ≥ 127 || n == 34 then 1 else 0
    match result.ending with
    | some (.defined (.loaded (.specified (.integer got)))) =>
      unless got == expected do throw <| IO.userError s!"actual Core {n}: {got} != {expected}"
    | ending => throw <| IO.userError s!"actual Core {n} failed: {(observation ending).json.compress}"
    unless result.finalState.memory.bytes == s.memory.bytes &&
        result.finalState.memory.nextId == s.memory.nextId &&
        result.finalState.memory.lastAddress == s.memory.lastAddress &&
        result.finalState.memory.dead == s.memory.dead &&
        result.finalState.memory.stdout == s.memory.stdout do
      throw <| IO.userError "read-only parameter predicate changed caller memory"
    let after := result.finalState.memory
    unless after.allocations.keys == s.memory.allocations.keys &&
        reprStr (after.allocations.lookup 0) == reprStr (s.memory.allocations.lookup 0) &&
        after.enumTypes == s.memory.enumTypes &&
        after.pointerBytes == s.memory.pointerBytes &&
        after.functions == s.memory.functions &&
        after.lastUsed == s.memory.lastUsed &&
        after.nextExcluded == s.memory.nextExcluded do
      throw <| IO.userError "parameter allocation or auxiliary memory state changed"
    if n == 34 then
      let missing := {s with memory := {}}
      match (run F.file ∅ 100000 missing).ending with
      | some (.defined _) => throw <| IO.userError "missing parameter allocation was accepted"
      | none => throw <| IO.userError "negative case exhausted fuel"
      | some _ => pure ()
  IO.println "PASS actual darkhttpd needs_logencoding Core on256 byte arguments, preserved parameter memory, missing-allocation rejection and unconstrained upper ABI bits; finite execution is not a contextual proof"

example : Silmaril.X86.SystemV.Encodes .uint8 (0x22 : BitVec 8) (0xabcdef0123456722 : BitVec 64) := by
  change (0xabcdef0123456722 : BitVec 64).setWidth 8 = (0x22 : BitVec 8)
  decide
example : ¬ Silmaril.X86.SystemV.Encodes .uint8 (0x23 : BitVec 8) (0xabcdef0123456722 : BitVec 64) := by
  change ¬ (0xabcdef0123456722 : BitVec 64).setWidth 8 = (0x23 : BitVec 8)
  decide

/-- The diagnostic-only normalization cannot hide allocation-state mutations.
This is an observation-definition regression, not a source/ELF refinement proof. -/
example (s t : State) (v : _) (changed : t.memory.nextId ≠ s.memory.nextId) :
    ¬ (Context.context.sourceObservation (0 : BitVec 8) s t v).2 := by
  intro observed
  change {t.memory with currentLocation := s.memory.currentLocation} = s.memory at observed
  have same := congrArg (fun memory : Mem.Concrete.State => memory.nextId) observed
  exact changed same
