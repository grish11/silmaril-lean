module
public meta import Silmaril.Elf.Corpus.CjsonTypePredicates.Context.Defs
public meta import Silmaril.Cerberus.Core.Outcome.Defs
public meta section
open Silmaril.Elf.Corpus.CjsonTypePredicates
open Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics

/-- Finite executions of the same entries used in the contextual problems.
They test initialized field/null behavior and preserved caller state, not refinement. -/
def main : IO Unit := do
  let mut count := 0
  for (p, kind) in [(Predicate.isNull, (4 : Int)), (.isBool, 3), (.isNumber, 8),
      (.isString, 16), (.isArray, 32), (.isObject, 64),
      (.isInvalid, 0), (.isFalse, 1), (.isTrue, 2), (.isRaw, 128)] do
    for bits in ([kind, kind + 256, 0, -1, -2147483648] : List Int).eraseDups do
      for null in [false, true] do
        let i : Context.Input := ⟨null, BitVec.ofInt 32 bits⟩
        let entry ← match Context.prepare p i with
          | .ok s => pure s
          | .error error => throw (IO.userError s!"{p.name}: {error}")
        let F := Source.Elaboration.function p
        let result := run F.file F.labels 20000 entry
        let expected := if null then 0 else if
          (if p == .isBool then bits % 4 != 0 else bits % 256 == kind) then 1 else 0
        match result.ending with
        | some (.defined (.loaded (.specified (.integer n)))) =>
          unless n == expected do throw (IO.userError s!"{p.name}: expected {expected}, got {n}")
        | _ => throw (IO.userError s!"{p.name}: no defined return")
        let m := result.finalState.memory
        unless m.bytes == entry.memory.bytes && m.dead == entry.memory.dead &&
            m.stdout == entry.memory.stdout do
          throw (IO.userError s!"{p.name}: caller state changed")
        count := count + 1
  IO.println s!"PASS {count} actual cJSON contextual entries: returns, field bytes, lifetimes and stdout"
