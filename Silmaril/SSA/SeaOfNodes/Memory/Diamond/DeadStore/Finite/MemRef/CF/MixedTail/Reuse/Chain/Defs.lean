module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay.Defs

/-! Reuse the admitted mixed-entry chain under its ordered address contracts. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain

open RVSDG (Tuple)
open Quads.CFG (Predecessors)

variable {args : List ValueSort} {cells sites : Nat} {preds : Predecessors sites}

def contracts (original : Replay.Result cells args preds) : List (Contract args preds) :=
  original.admitted.map contractOf

def Valid (original : Replay.Result cells args preds) (input : Tuple (Val cells) args) : Prop :=
  ∀ facts ∈ contracts original, facts.Valid input

/-- Check the full contract list without rebinding the artifacts. -/
def check (original : Replay.Result cells args preds) (input : Tuple (Val cells) args) : Bool :=
  (contracts original).all (fun facts => facts.check input)

structure Result (cells : Nat) (args : List ValueSort) (preds : Predecessors sites) where
  replay : Replay.Result cells args preds
  /-- The original first refused stage and all later stages. -/
  pending : List (MixedTail.Result cells args preds)

def Result.stop (input : Tuple (Val cells) args) (entry : Memory.Graph args)
    (current : Program cells args preds) (pending : List (MixedTail.Result cells args preds)) : Result cells args preds :=
  ⟨Replay.Result.stop input entry current [], pending⟩

def Result.prepend (result : Result cells args preds) (input : Tuple (Val cells) args)
    (source : Program cells args preds) (stage : MixedTail.Result cells args preds) : Result cells args preds :=
  { result with replay := result.replay.prepend input source stage }

/-- Carry the actual retained entry and optimized artifact through a stop. -/
def lowerFrom (input : Tuple (Val cells) args) :
    List (MixedTail.Result cells args preds) → Memory.Graph args → Program cells args preds → Result cells args preds
  | [], entry, current => .stop input entry current []
  | stage :: rest, entry, current =>
    match reuse stage input with
    | none => .stop input entry current (stage :: rest)
    | some rebound =>
      let next := lowerFrom input rest rebound.emission.edit.retained rebound.emission.programs.optimized
      next.prepend input current rebound

/-- Recheck just the admitted prefix of an existing checked replay. The
first invalid contract returns the exact preceding emitted CFG. -/
def lower (original : Replay.Result cells args preds) (entry : Memory.Graph args)
    (input : Tuple (Val cells) args) : Result cells args preds :=
  lowerFrom input original.admitted entry original.programs.original

/-- An accepted version is rechecked on its exact preceding entry, under
the new shared valuation and the original occurrence bank. -/
inductive Trace (fits : Fits preds) (arm : Occurrence preds → Memory.Graph args)
    (suffix : Memory.Graph (.word :: args)) (input : Tuple (Val cells) args) :
    Memory.Graph args → Program cells args preds → List (MixedTail.Result cells args preds) → Result cells args preds → Prop where
  | done (entry : Memory.Graph args) (current : Program cells args preds) :
    Trace fits arm suffix input entry current [] (.stop input entry current [])
  | refused {entry : Memory.Graph args} (current : Program cells args preds)
      {stage : MixedTail.Result cells args preds} (rest : List (MixedTail.Result cells args preds))
      (checked : reuse stage input = none) :
    Trace fits arm suffix input entry current (stage :: rest) (.stop input entry current (stage :: rest))
  | step {entry : Memory.Graph args} {current : Program cells args preds}
      {stage rebound : MixedTail.Result cells args preds} {rest : List (MixedTail.Result cells args preds)}
      {result : Result cells args preds}
      (checked : reuse stage input = some rebound)
      (selected : tryVersion fits arm suffix input entry stage.version = some rebound)
      (sourceEq : rebound.emission.programs.original = current)
      (inputEq : rebound.emission.programs.input = input)
      (next : Trace fits arm suffix input rebound.emission.edit.retained rebound.emission.programs.optimized rest result) :
    Trace fits arm suffix input entry current (stage :: rest) (result.prepend input current rebound)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain
