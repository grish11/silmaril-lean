module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Identity
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact

open Silmaril.MLIR.Arith (Env Width)
open Loop.MLIR.CF (evalOp)
open Corridor.Header.Typed (edgePackets)

variable {Input full extra : List Width} {saved carried result : Width}
variable {source : TargetCfg Input saved carried result extra full}

/-- Keeping every position preserves the packet's type list. -/
theorem Projection.keepAll_types (widths : List Width) : (Projection.keepAll widths).types = widths :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.keepAll_types widths

/-- Identity indices enumerate the current packet in order. -/
theorem Projection.keepAll_indices (widths : List Width) :
    (Projection.keepAll widths).indices = List.range widths.length :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.keepAll_indices widths

/-- Projecting a packet through the identity retains each value. -/
theorem Projection.keepAll_values (packet : Env full) : HEq ((Projection.keepAll full).values packet) packet :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.keepAll_values packet

/-- Scanning the actual compacted exit retains all its lets and demands
every position of its compact packet. Ambient reads belong to the
remaining input suffix of that scope. -/
theorem Emission.rescan (emission : Emission source) :
    ∃ scan, scanExit? (emission.cfg.block .exit) = some scan ∧
      scan.mask = List.replicate (shape.ofBlock (emission.cfg.block .exit)).bindings false ∧
      ∀ index < emission.projection.types.length, index ∈ scan.inputs :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.rescan emission

/-- Re-running the actual compactor on its own output succeeds with the
identity projection, the same typed exit code, and the exact packets at
both header occurrences. Heterogeneous equality compares the artifacts
across their propositionally equal packet signatures. -/
theorem Emission.compact_again (first : Emission source) :
    ∃ second : Emission first.cfg, compact? first.cfg = some second ∧
      second.projection = Projection.keepAll first.projection.types ∧ HEq second.exitCode first.exitCode ∧
      ∀ env : Env (SavedBank saved carried extra ++ Input),
        HEq ((second.cfg.block .header).eval evalOp edgePackets env)
          ((first.cfg.block .header).eval evalOp edgePackets env) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.stable first

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
