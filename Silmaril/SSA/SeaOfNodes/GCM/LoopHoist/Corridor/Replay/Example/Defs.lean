module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Example.Defs

/-! # Replay the checked producer and consumer by their original identities -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Example

open Loop.MLIR.CF (evalOp)
open Corridor.Example (input)
open AfterReorder.Second.Example (first loop)

def producer : Nomination := ⟨1, 0⟩

def consumer : Nomination := ⟨2, 1⟩

/-- Observe the current origin order and returns at fuel three, four and five. -/
def observe (nominations : List Nomination) : Except Refusal (List Nat × List (Option Nat)) :=
  (replay (loop false) first.header nominations).map fun snapshot =>
    (snapshot.origins, [3, 4, 5].map fun fuel =>
      (snapshot.cfg.run evalOp fuel (input 2 10 1)).map (fun result => (result.get .here).toNat))

/-- Report a current header position or a saved packet position and
its preheader definition cut. -/
def locate (nominations : List Nomination) (origin : Nat) :
    Except Refusal (Option (Nat ⊕ (Nat × Nat))) :=
  (replay (loop false) first.header nominations).map fun snapshot =>
    (snapshot.locate? origin).map fun
      | .inl index => .inl index
      | .inr ⟨_, ref⟩ => .inr (ref.index, Saved.definitionCut snapshot.savedWidths (Saved.prefixRef [] ref))

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Example
