module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block)
open Loop.MLIR.CF (TargetOp evalOp)
open Corridor.Header.Typed (edgePackets)
open Corridor.Header.Earlier (operations)

variable {Input extra Γ : List Width} {saved carried result : Width}
variable {code : Block TargetOp (Label saved carried result extra) Γ [result]}
variable {scan : Scan} {mask : List Bool} {reads : List Nat}
variable {source : Source Input saved carried result extra}

/-- All retained reads are closed under header producers, including the
actual guard and ordered feedback operands. -/
theorem scan_closed (found : scan? code = some scan) : RetainedReads code scan.mask scan.inputs :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.scan_closed found

/-- There is one decision for each typed binding in the input header. -/
theorem scan_length (found : scan? code = some scan) : scan.mask.length = (operations code).length :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.scan_length found

/-- Every move in a control-closed mask is also proposed by the scan.
The scan also needs only the entry reads required by every closed choice.
This concerns closure, before the partition and exit checks. -/
theorem scan_least (valid : RetainedReads code mask reads) (found : scan? code = some scan) :
    (∀ read ∈ scan.inputs, read ∈ reads) ∧
    ∀ index : Nat, mask[index]? = some true → scan.mask[index]? = some true :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery.scan_least valid found

/-- When the scan proposes no move, every control-closed mask retains
all bindings. -/
theorem no_move_closed (valid : RetainedReads code mask reads) (found : scan? code = some scan)
    (none : true ∉ scan.mask) : true ∉ mask := by
  intro present
  obtain ⟨index, moved⟩ := List.getElem?_of_mem present
  exact none (List.mem_of_getElem? ((scan_least valid found).2 index moved))

/-- The checked result retains the original typed order on both sides
of the discovered mask. -/
theorem Plan.operation_order (plan : Plan source) :
    operations (plan.cfg.block .header) = selected false plan.scan.mask (operations (source.block .header)) ∧
    operations (plan.cfg.block .exit) = selected true plan.scan.mask (operations (source.block .header)) :=
  Partition.operation_order plan.emission

/-- The actual emitted sites pass dominance, operand availability and use checks. -/
theorem Plan.legal (plan : Plan source)
    {site : Suffix.Site (ExitLabel (SavedBank saved carried extra) plan.emission.sunk.header.packetTypes)}
    (listed : site ∈ Suffix.sites exitId 0 (plan.cfg.block .exit)) :
    Legal plan.cfg site.operands site.uses site.point :=
  Partition.legal plan.emission listed

/-- The ordered exit arguments belong to the actual false-edge occurrence. -/
theorem Plan.operand_occurrence (plan : Plan source) {argument : Nat}
    (inPacket : argument < plan.emission.sunk.header.packetTypes.length) :
    (Use.phi (some ⟨_, .header⟩) .onFalse argument).point? plan.cfg =
      some ⟨some ⟨_, .header⟩, plan.scan.mask.count false⟩ :=
  Partition.operand_occurrence plan.emission inPacket

/-- Feedback is exact and the new false packet reconstructs the original
exit value, even when that edge is untaken. -/
theorem Plan.header_packets (plan : Plan source) (env : Env (SavedBank saved carried extra ++ Input)) :
    (((plan.cfg.block .header).eval evalOp edgePackets env).map fun (slot, frame) =>
      (slot, plan.emission.sunk.restorePacket frame)) = (source.block .header).eval evalOp edgePackets env :=
  Partition.header_packets plan.emission env

/-- Returns and exhaustion agree at every common block-fuel budget. -/
theorem Plan.run_eq (plan : Plan source) (input : Env Input) (fuel : Nat) :
    plan.cfg.run evalOp fuel input = source.run evalOp fuel input :=
  Partition.run_eq plan.emission input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The checked discovered CFG has the original partial denotation. -/
theorem Plan.denotePart (plan : Plan source) (input : Env Input) :
    (Cfg.embed plan.cfg).denotePart evalOp input = (Cfg.embed source).denotePart evalOp input :=
  Partition.denotePart plan.emission input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Discovery
