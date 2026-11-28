module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.CF (evalOp)
open Corridor.Header.Typed (edgePackets)

variable {Input Γ full extra : List Width} {saved carried result : Width}
variable {source : TargetCfg Input saved carried result extra full}

/-- The ordered projection selects exactly the in-packet indices in
the source exit's return dependency closure. -/
theorem packet_indices (emission : Emission source) (index : Nat) :
    index ∈ emission.projection.indices ↔ index < full.length ∧ index ∈ emission.scan.inputs :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.packet_indices emission index

/-- Every forwarded slot is demanded by the return dependency closure of
the actual emitted exit. -/
theorem packet_used (emission : Emission source) :
    ∃ scan, scanExit? (emission.cfg.block .exit) = some scan ∧
      ∀ index < emission.projection.types.length, index ∈ scan.inputs :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.packet_used emission

/-- Projecting before evaluating an edge's operands is equivalent to
taking the same ordered projection of the old argument values. -/
theorem project_values (p : Projection full) (packet : Operands Γ full) (env : Env Γ) :
    (p.operands packet).eval env = p.values (packet.eval env) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.project_values p packet env

/-- At each exact header occurrence, feedback keeps its old packet and
an exit receives the ordered projection of its old packet. -/
theorem header_packets (emission : Emission source) (env : Env (SavedBank saved carried extra ++ Input)) :
    (emission.cfg.block .header).eval evalOp edgePackets env =
      ((source.block .header).eval evalOp edgePackets env).map fun (slot, frame) =>
        (slot, emission.projection.frame frame) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.header_packets emission env

/-- Retagging the exit preserves all header slots and the terminator cut. -/
theorem header_shape (emission : Emission source) (slot : EdgeSlot) :
    (shape emission.cfg (some ⟨_, .header⟩)).target slot =
      ((shape source (some ⟨_, .header⟩)).target slot).map emission.projection.target ∧
    (shape emission.cfg (some ⟨_, .header⟩)).bindings = (shape source (some ⟨_, .header⟩)).bindings :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.header_shape emission slot

/-- The false-edge destination is preserved even when the projection is empty. -/
theorem false_target (emission : Emission source)
    (edge : (shape source (some ⟨_, .header⟩)).target .onFalse = some ⟨full, .exit⟩) :
    (shape emission.cfg (some ⟨_, .header⟩)).target .onFalse = exitId := by
  simpa only [edge, Option.map_some, Projection.target, exitId] using (header_shape emission .onFalse).1

/-- Each projected argument is read at the same actual false occurrence
and header cut as before compaction. -/
theorem false_occurrence (emission : Emission source)
    (edge : (shape source (some ⟨_, .header⟩)).target .onFalse = some ⟨full, .exit⟩)
    {argument : Nat} (inPacket : argument < emission.projection.types.length) :
    (Use.phi (some ⟨_, .header⟩) .onFalse argument).point? emission.cfg =
      some ⟨some ⟨_, .header⟩, (shape source (some ⟨_, .header⟩)).bindings⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.false_occurrence emission edge inPacket

/-- Full and compact packets have equal returns and exhaustion at common block fuel. -/
theorem run_eq (emission : Emission source) (input : Env Input) (fuel : Nat) :
    emission.cfg.run evalOp fuel input = source.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.run_eq emission input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The compacted artifact has the original full-packet CFG's partial denotation. -/
theorem denotePart (emission : Emission source) (input : Env Input) :
    (Cfg.embed emission.cfg).denotePart evalOp input = (Cfg.embed source).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.denotePart emission input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
