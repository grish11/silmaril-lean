module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Insert.Defs

/-! # Checked earlier insertion into the saved preheader prefix -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Block Cfg)
open AfterReorder.Second (checkPrefixCut)
open AfterReorder.Second.Emit (liftCode)
open Loop.MLIR.CF (TargetOp)

variable {Input extra : List Width} {saved carried result : Width}

/-- The append emitter supplies the rewritten header and exact feedback/exit
    occurrences. The typed insertion changes its physical entry order only. -/
structure Emission (Input : List Width) (saved carried result : Width) (extra : List Width) where
  append : Step.Emission Input saved carried result extra
  splice : Saved.Prefix.Insertion Input ((extra ++ [saved]) ++ Input) append.candidate.width
  tail : Block TargetOp (Label saved carried result extra) ((extra ++ [saved]) ++ Input) [result]

def Emission.entryTail (moved : Emission Input saved carried result extra) :
    Block TargetOp (Label saved carried result (moved.append.candidate.width :: extra)) moved.splice.physical [result] :=
  liftCode moved.splice.previous moved.splice.inserted moved.tail

def Emission.cfg (moved : Emission Input saved carried result extra) :
    Cfg TargetOp (Label saved carried result (moved.append.candidate.width :: extra)) Input [result] :=
  { moved.append.next.cfg with
    entry := moved.splice.leading.wrap moved.entryTail }

/-- Check the nomination on the current CFG at the requested earlier cut.
    The append result is the reference for routing and keeps the regular
    replay API available. The earlier CFG carries the physical slot map. -/
def emit? (state : State Input saved carried result extra) (request : Nomination) :
    Option (Emission Input saved carried result extra) := do
  let widths := extra ++ [saved]
  if request.cut < widths.length then
    let .ok append := Step.emit state { request with cut := widths.length } | none
    if checkPrefixCut state.cfg append.candidate request.cut then
      let (leading, tail) ← Saved.splitPrefix? state.cfg.entry widths
      let splice ← leading.insert? append.candidate.op (widths.length - request.cut) append.candidate.inputs
      pure ⟨append, splice, tail⟩
    else none
  else none

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier
