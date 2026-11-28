module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Block)
open Loop.MLIR.CF (TargetOp)
open Partition.Discovery (Scan)

variable {Input bank full results extra : List Width} {saved carried result : Width}
variable {source : TargetCfg Input saved carried result extra full}

/-- The actual exit rewrite can translate the surviving slice exactly
when the projection retains all demanded old packet slots. Reads of
ambient function inputs stay available independently of the packet. -/
theorem Projection.rewriteScanned?_iff (p : Projection full)
    {code : Block TargetOp (ExitLabel bank full) (full ++ Input) results} {scan : Scan}
    (scanned : scanExit? code = some scan) :
    (p.rewriteScanned? code).isSome = true ↔
      ∀ index ∈ scan.inputs, index < full.length → index ∈ p.indices :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.projection_rewrite_iff p scanned

/-- The supplied-projection API replays the compactor's exact exit code
when supplied its discovered projection. -/
theorem Emission.rewriteScanned?_exact (emission : Emission source) :
    emission.projection.rewriteScanned? (source.block .exit) = some emission.exitCode := by
  simp only [Projection.rewriteScanned?, emission.scanned]
  exact emission.rewritten

/-- The automatic projection is least by slot inclusion among ordered
projections that rewrite the same discovered typed exit slice. -/
theorem Emission.minimal_projection (emission : Emission source) (p : Projection full) :
    (p.rewriteScanned? (source.block .exit)).isSome = true ↔
      ∀ index ∈ emission.projection.indices, index ∈ p.indices :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.minimal emission p

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact
