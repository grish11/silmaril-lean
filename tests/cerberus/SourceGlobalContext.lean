import Silmaril.Elf.Corpus.OpenSslSecureInitialized.Thms
import Silmaril.Cerberus.Core.Outcome.Defs

/-! Finite execution observations of the actual pinned global-reader Core.
These exercise the concrete memory binding; they are not semantic proofs. -/
open Silmaril.Cerberus Silmaril.Cerberus.Core.Dynamics
open Silmaril.Elf.Corpus.OpenSslSecureInitialized

private def check (n : BitVec 32) : IO Unit := do
  let s := entry n
  let result := run sourceFn.file ∅ 20000 s
  match result.ending with
  | some (.defined (.loaded (.specified (.integer got)))) =>
      unless got == n.toInt do throw <| IO.userError s!"wrong global result {got}"
  | ending => throw <| IO.userError s!"unexpected ending: {(observation ending).json.compress}"
  for offset in [0, 1, 2, 3] do
    unless Mem.Concrete.readByte (4096 + offset) result.finalState.memory.bytes ==
        Mem.Concrete.readByte (4096 + offset) s.memory.bytes do
      throw <| IO.userError "global contents changed"
  unless result.finalState.memory.stdout == s.memory.stdout &&
      result.finalState.memory.nextId == s.memory.nextId &&
      result.finalState.memory.dead == s.memory.dead do
    throw <| IO.userError "source lifetime/stdout changed"
  IO.println s!"PASS global={n.toInt} transitions={result.actions.length}"

def main : IO Unit := do
  for n in ([0, 1, 2147483647, 2147483648, 4294967295] : List Nat) do
    check (BitVec.ofNat 32 n)
  let missing : State := {entry 0 with memory := {}}
  let result := run sourceFn.file ∅ 20000 missing
  match result.ending with
  | some (.defined _) => throw <| IO.userError "missing allocation was accepted"
  | none => throw <| IO.userError "missing-allocation test exhausted fuel"
  | some _ => IO.println s!"PASS missing allocation rejected: {(observation result.ending).json.compress}"
