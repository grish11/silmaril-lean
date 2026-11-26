module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Example.Defs

/-! # Discover three physical placements, then stop with latch-local reads -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Example

open Silmaril.MLIR.CF (Frame Terminator)
open Loop.MLIR.CF (evalOp)
open Corridor.Example (input)
open Layout.Example (seed?)
open Step.Example (words)

structure Observation where
  requests : List Nomination
  stop : Stop
  remainingOrigins : List Nat
  slots : List (Option Nat)
  packets : List (List Nat)
  runs : List (Option Nat)
  appendRuns : List (Option Nat)
  deriving BEq, Repr

/-- Observe the actual chosen sequence, physical slots and exact transfers. -/
def observe (budget : Nat) : Option Observation := do
  let ⟨_, _, seed⟩ ← seed?
  let .ok plan := discover seed.reference budget | none
  let final := plan.output.2
  let cfg := final.cfg
  let inputs := input 2 10 1
  let .inl entry := cfg.entry.eval evalOp (fun term env => Terminator.eval env term) inputs | none
  let step := fun (frame : Frame _) =>
    (cfg.block frame.label).eval evalOp (fun term env => Terminator.eval env term) (frame.args.append inputs)
  let .inl once := step entry | none
  let .inl twice := step once | none
  let .inl exit := step twice | none
  let runs := fun code => [3, 4, 5].map fun fuel =>
    (code.run evalOp fuel inputs).map (fun env => (env.get .here).toNat)
  pure ⟨plan.requests, plan.stop, final.reference.origins, [7, 6, 5, 2, 1].map final.physicalSlot?,
    [entry, once, twice, exit].map (fun frame => words frame.args), runs cfg, runs final.reference.cfg⟩

/-- Origin 6 initially reads a header-local value. Discovery has to save
    origin 5 before the dependent binding can be selected. -/
def dependentInitiallyRefused : Bool :=
  seed?.any fun ⟨_, _, seed⟩ => (Layout.emit? seed ⟨6, 2⟩).isNone

/-- An absent saved prefix and an unchecked live inventory fail before search. -/
def refused : Option (List Unsupported) := do
  let ⟨_, _, seed⟩ ← seed?
  let withoutPrefix := { seed.reference with
    cfg := { seed.reference.cfg with entry := .terminator (.ret (.cons .here .nil)) } }
  let .error prefixError := discover withoutPrefix 5 | none
  let .error inventoryError := discover { seed.reference with origins := [] } 5 | none
  pure [prefixError, inventoryError]

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Example
