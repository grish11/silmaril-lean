module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Defs

/-! Replay a finite list of checked entry cuts, stopping at the first refusal. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay

open RVSDG (Tuple)
open Quads.CFG (Predecessors)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}

structure Result (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) where
  programs : Programs cells args preds
  retained : Memory.Graph args
  admitted : List (Emission cells args preds)
  /-- The refused request and all requests after it. Empty when the plan is exhausted. -/
  remaining : List (Request args preds)

def Result.deleted (result : Result cells args preds) : Nat :=
  result.admitted.length

def Result.stop (input : Tuple (Val cells) args) (entry : Memory.Graph args) (current : Program cells args preds)
    (remaining : List (Request args preds)) : Result cells args preds :=
  ⟨⟨input, current, current⟩, entry, [], remaining⟩

def Result.prepend (result : Result cells args preds) (input : Tuple (Val cells) args)
    (source : Program cells args preds) (stage : Emission cells args preds) : Result cells args preds :=
  { result with
    programs := ⟨input, source, result.programs.optimized⟩
    admitted := stage :: result.admitted }

/-- Apply the plan on the actual retained table and carry the current emitted
artifact through a stop. The public entry point initializes this pair together. -/
def lowerFrom (fits : Fits preds) (arm : Occurrence preds → Memory.Graph args) (suffix : Memory.Graph (.word :: args))
    (input : Tuple (Val cells) args) :
    List (Request args preds) → Memory.Graph args → Program cells args preds → Result cells args preds
  | [], entry, current => .stop input entry current []
  | request :: rest, entry, current =>
    match lowerWithEntry preds fits entry request.version arm request.candidate suffix input request.facts with
    | none => .stop input entry current (request :: rest)
    | some stage =>
      (lowerFrom fits arm suffix input rest stage.edit.retained stage.programs.optimized).prepend input current stage

/-- Recheck each nomination on the latest retained entry under the same
input, arm bank and continuation. The request list bounds the replay. -/
def lower (preds : Predecessors sites) (fits : Fits preds) (entry : Memory.Graph args)
    (arm : Occurrence preds → Memory.Graph args) (suffix : Memory.Graph (.word :: args))
    (input : Tuple (Val cells) args) (requests : List (Request args preds)) : Result cells args preds :=
  lowerFrom fits arm suffix input requests entry (lowerBank preds fits cells (some entry) arm suffix)

/-- Each accepted emission starts at the preceding optimized CFG and uses
the original input. A refusal leaves the exact current graph and CFG. -/
inductive Trace (fits : Fits preds) (arm : Occurrence preds → Memory.Graph args)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args) :
    Memory.Graph args → Program cells args preds → List (Request args preds) → Result cells args preds → Prop where
  | done (entry : Memory.Graph args) (current : Program cells args preds) :
    Trace fits arm suffix input entry current [] (.stop input entry current [])
  | refused {entry : Memory.Graph args} (current : Program cells args preds)
      {request : Request args preds} (rest : List (Request args preds))
      (checked : lowerWithEntry preds fits entry request.version arm request.candidate suffix input request.facts = none) :
    Trace fits arm suffix input entry current (request :: rest) (.stop input entry current (request :: rest))
  | step {entry : Memory.Graph args} {current : Program cells args preds}
      {request : Request args preds} {rest : List (Request args preds)}
      {stage : Emission cells args preds} {result : Result cells args preds}
      (checked : lowerWithEntry preds fits entry request.version arm request.candidate suffix input request.facts = some stage)
      (sourceEq : stage.programs.original = current) (inputEq : stage.programs.input = input)
      (next : Trace fits arm suffix input stage.edit.retained stage.programs.optimized rest result) :
    Trace fits arm suffix input entry current (request :: rest) (result.prepend input current stage)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay
