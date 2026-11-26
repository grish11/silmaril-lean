module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Defs

/-! Re-admit the retained native entry of a finite switch for one more cut. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.Forwarding.Disjoint (Certificate)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}

structure Request (args : List ValueSort) (preds : Predecessors sites) where
  /-- The one-based Store version in the table seen by this check. -/
  version : Nat
  facts : Certificate args
  candidate : Candidate args preds

structure Result (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) where
  first : Emission cells args preds
  second : Option (Emission cells args preds)

def Result.retained (result : Result cells args preds) : Memory.Graph args :=
  (result.second.getD result.first).edit.retained

def Result.deleted (result : Result cells args preds) : Nat :=
  if result.second.isSome then 2 else 1

def Result.programs (result : Result cells args preds) : Programs cells args preds :=
  match result.second with
  | none => result.first.programs
  | some next => { result.first.programs with optimized := next.programs.optimized }

/-- Check two nominations latest first. The second check uses the exact
retained entry from the first, with its current memory versions, and
checks its own facts on the original input, arms and continuation.
A second refusal retains the first emission. -/
def lower (preds : Predecessors sites) (fits : Fits preds) (entry : Memory.Graph args)
    (arm : Occurrence preds → Memory.Graph args) (suffix : Memory.Graph (.word :: args))
    (input : Tuple (Val cells) args) (first second : Request args preds) : Option (Result cells args preds) := do
  let stage ← lowerWithEntry preds fits entry first.version arm first.candidate suffix input first.facts
  let next := lowerWithEntry preds fits stage.edit.retained second.version arm second.candidate suffix input second.facts
  some ⟨stage, next⟩

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence
