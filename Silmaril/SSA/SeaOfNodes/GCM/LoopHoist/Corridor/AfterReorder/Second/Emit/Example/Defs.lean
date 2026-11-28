module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Example.Defs

/-! # Observe a dependent consumer actually moved into the preheader -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Example

open Silmaril.MLIR.CF (Frame Terminator)
open Loop.MLIR.CF (evalOp)
open Corridor.Example (input)
open Second.Example (loop first)

/-- Read the typed successor packet in argument order. -/
def packet {saved consumer : Silmaril.MLIR.Arith.Width} :
    Frame (Label saved Corridor.Example.word Corridor.Example.word [consumer]) → List Nat
  | ⟨.header, .cons second (.cons first (.cons old .nil))⟩ => [second.toNat, first.toNat, old.toNat]
  | ⟨.exit, .cons result .nil⟩ => [result.toNat]

/-- Observe the intermediate consumer index, actual entry and header
binding counts, and the emitted transfers through two feedbacks and exit. -/
def observe (varying : Bool) : Option (Nat × (Nat × Nat) × List (List Nat)) := do
  let moved ← replay? (loop varying) first 2
  let cfg := moved.cfg
  let inputs := input 2 10 1
  let .inl entry := cfg.entry.eval evalOp (fun term env => Terminator.eval env term) inputs | none
  let step := fun (frame : Frame _) =>
    (cfg.block frame.label).eval evalOp (fun term env => Terminator.eval env term) (frame.args.append inputs)
  let .inl once := step entry | none
  let .inl twice := step once | none
  let .inl exit := step twice | none
  pure (moved.prepared.index, ((shape cfg none).bindings, (shape cfg (some ⟨_, .header⟩)).bindings),
    [entry, once, twice, exit].map packet)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Example
