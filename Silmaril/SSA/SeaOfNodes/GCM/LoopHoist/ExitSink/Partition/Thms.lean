module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition

open Silmaril.MLIR.Arith (Env Width)
open Loop.MLIR.CF (evalOp)
open Corridor.Header.Typed (edgePackets)
open Corridor.Header.Earlier (operations)

variable {Input extra : List Width} {saved carried result : Width}
variable {source : Source Input saved carried result extra} {mask : List Bool}

/-- Each emitted block keeps its selected subsequence of the original
operation order. The mask is in original header coordinates. -/
theorem operation_order (emission : Emission source mask) :
    operations (emission.cfg.block .header) = selected false mask (operations (source.block .header)) ∧
    operations (emission.cfg.block .exit) = selected true mask (operations (source.block .header)) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.operation_order emission

/-- The emitted sites of the moved bindings pass the existing exact
dominance and local operand/use check. -/
theorem legal (emission : Emission source mask)
    {site : Suffix.Site (ExitLabel (SavedBank saved carried extra) emission.sunk.header.packetTypes)}
    (listed : site ∈ Suffix.sites exitId 0 (emission.cfg.block .exit)) :
    Legal emission.cfg site.operands site.uses site.point :=
  Suffix.sinkAt?_legal emission.checked listed

/-- The new argument reads on the actual false edge after the retained operations. -/
theorem operand_occurrence (emission : Emission source mask) {argument : Nat}
    (inPacket : argument < emission.sunk.header.packetTypes.length) :
    (Use.phi (some ⟨_, .header⟩) .onFalse argument).point? emission.cfg =
      some ⟨some ⟨_, .header⟩, mask.count false⟩ :=
  Suffix.operand_occurrence emission.sunk inPacket

/-- The exact feedback packet and reconstructed exit value agree even
when one of the two occurrences is untaken. -/
theorem header_packets (emission : Emission source mask) (env : Env (SavedBank saved carried extra ++ Input)) :
    (((emission.cfg.block .header).eval evalOp edgePackets env).map fun (slot, frame) =>
      (slot, emission.sunk.restorePacket frame)) = (source.block .header).eval evalOp edgePackets env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.header_packets emission env

/-- Returns and exhaustion agree at every common block-fuel budget. -/
theorem run_eq (emission : Emission source mask) (input : Env Input) (fuel : Nat) :
    emission.cfg.run evalOp fuel input = source.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.run_eq emission input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The emitted CFG has the original partial denotation. -/
theorem denotePart (emission : Emission source mask) (input : Env Input) :
    (Cfg.embed emission.cfg).denotePart evalOp input = (Cfg.embed source).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.denotePart emission input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition
