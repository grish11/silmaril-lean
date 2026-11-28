module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Thms
import Silmaril.SSA.PhiView.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi

open Silmaril.MLIR.Arith (Atom Env Width)
open Silmaril.Isotope (Value)

variable {Input full extra : List Width} {saved carried result : Width}
variable {source : TargetCfg Input saved carried result extra full}

/-- Extraction after compaction preserves the terminal scope and occurrence,
and selects the typed operands in the order of the packet projection. -/
theorem rowAt_project (emission : Emission source) (occ : Occurrence) :
    rowAt? emission.cfg occ =
      (rowAt? source occ).map fun row => ⟨row.1, emission.projection.operands row.2⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.row_project emission occ

/-- Evaluating the real CF occurrence after compaction is the same as
projecting the old evaluated exit packet. An absent occurrence stays absent. -/
theorem packetAt_project (emission : Emission source) (occ : Occurrence)
    (env : Env (occ.1.scope Input (SavedBank saved carried extra))) :
    packetAt? emission.cfg occ env = (packetAt? source occ env).map emission.projection.values :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.packet_project emission occ env

/-- The positional Φ latch reads the actual evaluated CF successor packet. -/
theorem Incoming.latch_packet (row : Incoming source)
    (env : Env (row.val.1.scope Input (SavedBank saved carried extra))) :
    (packetAt? source row.val env).map pack = some (row.latch env) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.latch_packet row env

/-- Occurrence lookup and positional Φ latching also agree on absence. -/
theorem latchAt_packet (occ : Occurrence) (env : Env (occ.1.scope Input (SavedBank saved carried extra))) :
    latchAt? source occ env = (packetAt? source occ env).map pack :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.latch_at_packet occ env

/-- The explicit Φ branch for this occurrence transfers exactly the
packed CF argument row, with the usual unchanged branch state. -/
theorem Incoming.transfer_iff {σ : Type} (row : Incoming source)
    (env : Env (row.val.1.scope Input (SavedBank saved carried extra)))
    (instr : Silmaril.MLIR.Arith.Prim → Value Atom → σ → Value Atom → σ → Prop)
    (start finish : σ) (label : Nat) (payload : Value Atom) :
    Isotope.LambdaSSA.Semantics.Region.Eval instr (terminalEnv (predecessor source row.val.1) env).toLambdaSSA
      (.br row.edge.target row.edge.argument) start label payload finish ↔
      label = 0 ∧ (packetAt? source row.val env).map pack = some payload ∧ finish = start := by
  rw [row.latch_packet, PhiView.latch_eq_transfer instr (view source) row.edge]
  change label = 0 ∧ payload = row.latch env ∧ finish = start ↔
    label = 0 ∧ some (row.latch env) = some payload ∧ finish = start
  simp only [Option.some.injEq, eq_comm (a := payload)]

/-- Re-running the implemented compactor preserves exact extracted rows,
evaluated CF packets, and packed Φ values at every occurrence.
The packet signatures are propositionally equal by the identity projection. -/
theorem compact_rows_again (first : Emission source) :
    ∃ second : Emission first.cfg, compact? first.cfg = some second ∧
      ∀ occ : Occurrence, HEq (rowAt? second.cfg occ) (rowAt? first.cfg occ) ∧
        ∀ env : Env (occ.1.scope Input (SavedBank saved carried extra)),
          HEq (packetAt? second.cfg occ env) (packetAt? first.cfg occ env) ∧
          latchAt? second.cfg occ env = latchAt? first.cfg occ env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.compact_rows_again first

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi
