module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Example.Defs

/-! # Move a live binding in the lowered saved header -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Example

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg Terminator)
open Corridor.Example (Inputs word input)
open Loop.MLIR.CF (TargetOp evalOp)
open CrossBlock.Example (seed? packets runs)
open Step.Example (words)

def headerPackets {saved second : Width}
    (cfg : Cfg TargetOp (Label saved word word [second]) Inputs [word]) : Option (List (Nat × List Nat)) := do
  let inputs := input 2 10 1
  let .inl ⟨.header, args⟩ := cfg.entry.eval evalOp (fun term env => Terminator.eval env term) inputs | none
  pure $ ((cfg.block .header).eval evalOp Header.Typed.edgePackets (args.append inputs)).map fun (slot, frame) =>
    ((match slot with | .jump => 0 | .onTrue => 1 | .onFalse => 2), words frame.args)

structure Observation where
  bindingAndCuts : Nat × Nat × Nat
  beforeOrigins : List Nat
  afterOrigins : List Nat
  ordinaryReads : List Nat
  falseExitRead : Bool
  beforeEdges : List (Nat × List Nat)
  afterEdges : List (Nat × List Nat)
  beforePackets : List (List Nat)
  afterPackets : List (List Nat)
  beforeRuns : List (Option Nat)
  afterRuns : List (Option Nat)
  deriving BEq, Repr

/-- Origin 5 crosses origin 4. Its two ordinary reads and false-edge
    argument zero survive, including the argument on the untaken branch. -/
def observe : Option Observation := do
  let ⟨_, _, state⟩ ← seed?
  let move ← emit? state ⟨5, 2⟩
  let sites ← CrossBlock.findSites? move.next move.insertion 0 (Saved.origins _) (move.next.cfg.block .header)
  let beforeEdges ← headerPackets state.cfg
  let afterEdges ← headerPackets move.next.cfg
  let beforePackets ← packets state.cfg
  let afterPackets ← packets move.next.cfg
  let ordinaryReads := sites.uses.filterMap fun use =>
    match use with | .ordinary point => some point.cut | .phi .. => none
  let falseRead := sites.uses.any fun use =>
    match use with | .phi (some ⟨_, .header⟩) .onFalse 0 => true | _ => false
  pure ⟨(move.binding.index, move.cut.cut, move.insertion), state.reference.origins,
    move.next.reference.origins, ordinaryReads, falseRead, beforeEdges, afterEdges,
    beforePackets, afterPackets, runs state.cfg, runs move.next.cfg⟩

/-- Cut 5 crosses origin 5's first ordinary read at cut 4. Origin 6
    cannot move to cut 3 because that is before its operand, origin 5. -/
def refused : Option (Bool × Bool) := do
  let ⟨_, _, state⟩ ← seed?
  pure ((emit? state ⟨5, 5⟩).isNone, (emit? state ⟨6, 3⟩).isNone)

structure Ranking where
  depths : Nat × Nat
  headerCut : Nat
  headerInsertion : Nat
  outsideBeforeProducer : Bool
  lateSelection : Nat × Nat
  depthSelection : Nat × Nat
  lateRuns : List (Option Nat)
  depthRuns : List (Option Nat)
  deriving BEq, Repr

/-- Start from the emitted header permutation. The later header position
    wins when the preheader cannot read an operand. A legal shallower cut
    wins over that same emitted header alternative. -/
def ranking : Option Ranking := do
  let ⟨_, _, state⟩ ← seed?
  let earlier ← emit? state ⟨5, 2⟩
  let late ← rank? earlier.next ⟨5, 0⟩ 4
  let depth ← rank? earlier.next ⟨5, 1⟩ 4
  let moved ← depth.header
  let control := depth.crossBlock.control
  let point := fun (p : Point _) => (CrossBlock.blockNumber p.block, p.cut)
  pure ⟨(control.depth none, control.depth moved.cut.block), moved.cut.cut, moved.insertion,
    late.crossBlock.preheader.isNone, point late.selection.1, point depth.selection.1,
    runs late.selection.2.2.cfg, runs depth.selection.2.2.cfg⟩

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice.Example
