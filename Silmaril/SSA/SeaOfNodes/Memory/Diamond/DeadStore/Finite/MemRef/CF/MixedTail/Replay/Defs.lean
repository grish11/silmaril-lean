module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Defs

/-! Replay the checked mixed-entry finder on each actual retained table. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay

open RVSDG (Tuple)
open Quads.CFG (Predecessors)
open Memory.Forwarding.Disjoint (cell)
open Memory.DeadStore.Search.Selection.Readers.Repeat (storeCount)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}

inductive Request where
  | discover
  /-- Require the current finder to select this one-based version. -/
  | expect (version : Nat)

def Request.accepts : Request → Nat → Bool
  | .discover, _ => true
  | .expect version, actual => version == actual

/-- One record per original occurrence, in the original Region order. -/
def occurrenceRecords (stage : MixedTail.Result cells args preds) :
    Vector (ArmOverwrite args) (preds.rest.length + 1) :=
  Vector.ofFn stage.candidate

def check (fits : Fits preds) (arm : Occurrence preds → Memory.Graph args)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args)
    (entry : Memory.Graph args) (request : Request) : Option (MixedTail.Result cells args preds) := do
  let stage ← MixedTail.lower fits arm suffix input entry
  if request.accepts stage.version then some stage else none

structure Result (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) where
  programs : Programs cells args preds
  retained : Memory.Graph args
  admitted : List (MixedTail.Result cells args preds)
  /-- The refused request and the unattempted tail. -/
  remaining : List Request

def Result.deleted (result : Result cells args preds) : Nat :=
  result.admitted.length

def Result.stop (input : Tuple (Val cells) args) (entry : Memory.Graph args)
    (current : Program cells args preds) (remaining : List Request) : Result cells args preds :=
  ⟨⟨input, current, current⟩, entry, [], remaining⟩

def Result.prepend (result : Result cells args preds) (input : Tuple (Val cells) args)
    (source : Program cells args preds) (stage : MixedTail.Result cells args preds) : Result cells args preds :=
  { result with
    programs := ⟨input, source, result.programs.optimized⟩
    admitted := stage :: result.admitted }

/-- Reapply the removed writes in reverse order, using each actual
prefix-produced word at the saved input and original initial buffer. -/
def Result.restoreEntry (result : Result cells args preds) (initial : Buffer cells) : Buffer cells :=
  let input := result.programs.input
  result.admitted.foldr (fun stage buffer =>
    let edit := stage.emission.edit
    ⟨Heap.write buffer.cell (cell input edit.address) (observe edit.beforeStore input initial).1⟩)
    (observe result.retained input initial).2

/-- The current artifact is carried through a stop without re-emitting it. -/
def lowerFrom (fits : Fits preds) (arm : Occurrence preds → Memory.Graph args) (suffix : Memory.Graph (.word :: args))
    (input : Tuple (Val cells) args) :
    List Request → Memory.Graph args → Program cells args preds → Result cells args preds
  | [], entry, current => .stop input entry current []
  | request :: rest, entry, current =>
    match check fits arm suffix input entry request with
    | none => .stop input entry current (request :: rest)
    | some stage =>
      let next := lowerFrom fits arm suffix input rest stage.emission.edit.retained stage.emission.programs.optimized
      next.prepend input current stage

/-- Replay a bounded list of checks on the successive retained entries. -/
def lower (preds : Predecessors sites) (fits : Fits preds) (entry : Memory.Graph args)
    (arm : Occurrence preds → Memory.Graph args) (suffix : Memory.Graph (.word :: args))
    (input : Tuple (Val cells) args) (requests : List Request) : Result cells args preds :=
  lowerFrom fits arm suffix input requests entry (lowerBank preds fits cells (some entry) arm suffix)

/-- Use the original Store count as the discovery bound. -/
def discover (preds : Predecessors sites) (fits : Fits preds) (entry : Memory.Graph args)
    (arm : Occurrence preds → Memory.Graph args) (suffix : Memory.Graph (.word :: args))
    (input : Tuple (Val cells) args) : Result cells args preds :=
  lower preds fits entry arm suffix input (List.replicate (storeCount entry) .discover)

/-- A successful step uses the exact preceding CFG and the original input,
with the next check on its retained entry. A refused check ends the trace. -/
inductive Trace (fits : Fits preds) (arm : Occurrence preds → Memory.Graph args)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args) :
    Memory.Graph args → Program cells args preds → List Request → Result cells args preds → Prop where
  | done (entry : Memory.Graph args) (current : Program cells args preds) :
    Trace fits arm suffix input entry current [] (.stop input entry current [])
  | refused {entry : Memory.Graph args} (current : Program cells args preds)
      {request : Request} (rest : List Request) (checked : check fits arm suffix input entry request = none) :
    Trace fits arm suffix input entry current (request :: rest) (.stop input entry current (request :: rest))
  | step {entry : Memory.Graph args} {current : Program cells args preds}
      {request : Request} {rest : List Request} {stage : MixedTail.Result cells args preds}
      {result : Result cells args preds}
      (checked : check fits arm suffix input entry request = some stage)
      (sourceEq : stage.emission.programs.original = current) (inputEq : stage.emission.programs.input = input)
      (routes : ∀ i : Occurrence preds,
        LoadTail.PrefixWord.checkArm stage.emission.edit.address (arm i) (occurrenceRecords stage)[i.val] input = true)
      (next : Trace fits arm suffix input stage.emission.edit.retained stage.emission.programs.optimized rest result) :
    Trace fits arm suffix input entry current (request :: rest) (result.prepend input current stage)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay
