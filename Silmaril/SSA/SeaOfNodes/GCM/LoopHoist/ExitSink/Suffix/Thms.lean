module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Thms
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix

open Silmaril.MLIR.Arith (Env Width)
open Loop.MLIR.CF (evalOp)
open Corridor.Header.Typed (edgePackets)
open Corridor.Header.Earlier (operations)

variable {Input extra : List Width} {saved carried result : Width} {cut : Nat}
variable {source : Source Input saved carried result extra} {emission : Emission source cut}

/-- Discovery returns the actual checked emission at the least accepted
split, hence the longest admitted suffix. -/
theorem discover?_spec (found : discover? source = some ⟨cut, emission⟩) :
    sinkAt? source cut = some emission ∧
      ∀ {other : Nat} (alternative : Emission source other), sinkAt? source other = some alternative → cut ≤ other :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.discover_spec found

/-- Failure excludes every split accepted by the same emitter and site checker. -/
theorem discover?_none : discover? source = none ↔ ∀ cut, sinkAt? source cut = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.discover_none

/-- Every moved operation is checked on the emitted CFG at its actual
exit binding cut with its resolved operands and uses. -/
theorem sinkAt?_legal (accepted : sinkAt? source cut = some emission)
    {site : Site (ExitLabel (SavedBank saved carried extra) emission.header.packetTypes)}
    (listed : site ∈ sites exitId 0 (emission.cfg.block .exit)) :
    Legal emission.cfg site.operands site.uses site.point :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.sink_legal accepted listed

/-- The two physical blocks contain the original prefix and suffix in their
original typed operation order. -/
theorem operation_order (emission : Emission source cut) :
    operations (emission.cfg.block .header) = (operations (source.block .header)).take cut ∧
    operations (emission.cfg.block .exit) = (operations (source.block .header)).drop cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.operation_order emission.header Input

/-- Every retained-scope argument is read on the real false-edge occurrence
at the shortened header's terminator. -/
theorem operand_occurrence (emission : Emission source cut) {argument : Nat}
    (inPacket : argument < emission.header.packetTypes.length) :
    (Use.phi (some ⟨_, .header⟩) .onFalse argument).point? emission.cfg =
      some ⟨some ⟨_, .header⟩, cut⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.operand_occurrence emission inPacket

/-- Feedback passes the exact old bank. The false edge's new packet
reconstructs the old result by evaluating the emitted suffix's bindings. -/
theorem header_packets (emission : Emission source cut) (env : Env (SavedBank saved carried extra ++ Input)) :
    (((emission.cfg.block .header).eval evalOp edgePackets env).map fun (slot, frame) =>
      (slot, emission.restorePacket frame)) = (source.block .header).eval evalOp edgePackets env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.header_packets emission.header env

/-- The rewrite preserves return and exhaustion at every common block-fuel budget. -/
theorem run_eq (emission : Emission source cut) (input : Env Input) (fuel : Nat) :
    emission.cfg.run evalOp fuel input = source.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.run_eq emission input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The emitted CFG preserves the original partial denotation. -/
theorem denotePart (emission : Emission source cut) (input : Env Input) :
    (Cfg.embed emission.cfg).denotePart evalOp input = (Cfg.embed source).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix.denotePart emission input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Suffix
