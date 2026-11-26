module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Terminator)
open Loop.MLIR.CF (TargetOp evalOp)
open Corridor.Header.Typed (edgePackets)

variable {Input extra args : List Width} {saved carried result : Width} {index : Nat}
variable {source : Source Input saved carried result extra} {emission : Emission source index}

/-- The operands of the moved binding read exactly the packet supplied on the
incoming exit edge, in operand order. -/
theorem packetRefs_eval (input : Env Input) (packet : Env args) :
    (packetRefs Input args).eval (packet.append input) = packet :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.packetRefs_eval input packet

/-- The actual old use scan finds exactly the exit Φ occurrence, whose read
point is the original header terminator. -/
theorem source_occurrence (emission : Emission source index) :
    sourceUses index 0 (source.block .header) = some [.phi (some ⟨_, .header⟩) .onFalse 0] ∧
    (Use.phi (some ⟨_, .header⟩) .onFalse 0).point? source = some ⟨some ⟨_, .header⟩, index + 1⟩ :=
  ⟨Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.header_uses emission.header 0,
    Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.source_use_point emission⟩

/-- A live use elsewhere in the header or on the feedback edge prevents a sink. -/
theorem refuses_other_use {uses : List (Use (Label saved carried result extra))}
    (scanned : sourceUses index 0 (source.block .header) = some uses)
    (other : uses ≠ [.phi (some ⟨_, .header⟩) .onFalse 0]) :
    sink? source index = none := by
  cases sink? source index with
  | none => rfl
  | some emission => exact (other (Option.some.inj (scanned.symm.trans (source_occurrence emission).1))).elim

/-- The header loses exactly one binding and keeps the true feedback
and false exit occurrences with their respective typed targets. -/
theorem header_slots (emission : Emission source index) :
    (shape source (some ⟨_, .header⟩)).target .onFalse = some ⟨_, .exit⟩ ∧
    (shape emission.cfg (some ⟨_, .header⟩)).target .onTrue = some ⟨_, .header⟩ ∧
    (shape emission.cfg (some ⟨_, .header⟩)).target .onFalse = exitId ∧
    (shape source (some ⟨_, .header⟩)).bindings = index + 1 ∧
    (shape emission.cfg (some ⟨_, .header⟩)).bindings = index :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.header_slots emission.header

/-- Each new exit argument is read on the same false-edge occurrence at
the shortened header's terminator. -/
theorem operand_occurrence (emission : Emission source index) {argument : Nat}
    (inPacket : argument < emission.header.opcode.1.length) :
    (Use.phi (some ⟨_, .header⟩) .onFalse argument).point? emission.cfg =
      some ⟨some ⟨_, .header⟩, index⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.operand_occurrence emission inPacket

/-- The existing exact CFG checker admits exit cut zero and the actual
return read at cut one using exact dominance and local availability. -/
theorem sink?_legal (accepted : sink? source index = some emission) :
    Legal emission.cfg emission.operandSites [.ordinary ⟨exitId, 1⟩] ⟨exitId, 0⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.sink_legal accepted

/-- Retagging an admitted entry leaves its evaluated jump packet unchanged
for every exit signature. -/
theorem Entry.code_packet {Γ : List Width}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]} (entry : Entry code)
    (exitArgs : List Width) (env : Env Γ) :
    ∃ packet : Env (SavedBank saved carried extra),
      code.eval evalOp (fun term vals => Terminator.eval vals term) env = .inl ⟨.header, packet⟩ ∧
      (entry.code exitArgs).eval evalOp (fun term vals => Terminator.eval vals term) env = .inl ⟨.header, packet⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.entry_packet entry exitArgs env

/-- The entry forwards the exact saved and carried packet. -/
theorem entry_packet (emission : Emission source index) (input : Env Input) :
    ∃ packet : Env (SavedBank saved carried extra),
      source.entry.eval evalOp (fun term vals => Terminator.eval vals term) input = .inl ⟨.header, packet⟩ ∧
      emission.cfg.entry.eval evalOp (fun term vals => Terminator.eval vals term) input = .inl ⟨.header, packet⟩ :=
  emission.entry.code_packet _ input

/-- Compare both actual outgoing occurrences independently of the branch
condition. Feedback carries the identical bank and the exit carries the
typed operands that reproduce the old exit value. -/
theorem header_packets (emission : Emission source index) (env : Env (SavedBank saved carried extra ++ Input)) :
    (((emission.cfg.block .header).eval evalOp edgePackets env).map fun (slot, frame) =>
      (slot, restorePacket emission.header.opcode.2 frame)) =
      (source.block .header).eval evalOp edgePackets env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.header_packets emission.header env

/-- Reusing the original exit block preserves return and exhaustion at
every common block-fuel budget. -/
theorem run_eq (emission : Emission source index) (input : Env Input) (fuel : Nat) :
    emission.cfg.run evalOp fuel input = source.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.run_eq emission input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The actual emitted CFG has the same partial denotation as the source. -/
theorem denotePart (emission : Emission source index) (input : Env Input) :
    (Cfg.embed emission.cfg).denotePart evalOp input = (Cfg.embed source).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.denotePart emission input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink
