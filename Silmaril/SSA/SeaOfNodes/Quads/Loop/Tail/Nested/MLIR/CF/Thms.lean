module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Thms

/-! # Exact source and projected CF budgets through the nested merge -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues valueBits)
open Silmaril.MLIR.Arith (Width Env)
open Diamond.Prune (HeaderProjection)
open Diamond.MLIR.CF (entryNames entryNames_agree)
open Diamond.MLIR.CF.Pruned (siteFrame lowerSourceWith_from_run)
open Blocks (Bank)
open Blocks.Prune (Mask)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {mask : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body mask)

/-- The typed return label costs one visit. This equation also preserves
exhaustion at every corresponding source and target budget. -/
theorem lower_run (fuel : Nat) (input : Bank (regs := regs) model) :
    (lower p projected).run evalOp (fuel + 1) (encodeValues input) =
      (src.runFrom model fuel entry input).map (fun value => Env.cons (valueBits value) .nil) :=
  Diamond.MLIR.CF.Pruned.lowerSourceWith_run projected _ _ fuel input (entryNames_agree input)

/-- The actual emitted CFG may resume at the common merge at exactly
the selected path's cost, with its post-edge reaching-version bank. -/
theorem from_header_eq_merge (fuel : Nat) (input old : Bank (regs := regs) model) :
    let occurrence := p.selected model old
    (lower p projected).runFrom evalOp (fuel + p.mergeVisits occurrence + 1) (encodeValues input)
        (siteFrame p.header mask p.header old) =
      (lower p projected).runFrom evalOp (fuel + 1) (encodeValues input)
        (siteFrame p.header mask p.join (p.mergeBank model old occurrence)) := by
  change (Diamond.MLIR.CF.Pruned.lowerSourceWith src entry p.header projected (entryNames regs)).runFrom _ _ _ _ = _
  unfold lower
  rw [lowerSourceWith_from_run, lowerSourceWith_from_run, p.run_to_merge]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF
