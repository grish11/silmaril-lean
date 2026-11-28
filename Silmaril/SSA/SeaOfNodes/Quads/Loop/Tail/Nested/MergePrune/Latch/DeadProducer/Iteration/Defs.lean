module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Defs

/-! # Prepare one checked shortened latch for the two actual emitters -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Pure.Deletion.Iteration (Result normalize)
open Diamond.Prune (HeaderProjection)
open Nested.Numbered (KeptResult)
open Blocks.Prune (Mask)

universe u v

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable {p : Program src entry} (projected : HeaderProjection (src p.header).body carry)
variable (checked : Split.Checked p carry merge atLatch)

abbrev Prepared := Result (Split.DeadProducer.originalTable checked.latchTransfer)

/-- Start at the exact source-derived merge-to-latch transfer. All cuts
are checked before either target sees the final table. -/
def prepare : Prepared checked := normalize (Split.DeadProducer.originalTable checked.latchTransfer)

variable (p)
variable (prepared : Prepared checked)

def lowerNumbered (result : KeptResult p (mask := carry)) :=
  Numbered.DeadProducer.lowerWith p projected checked prepared.final result

section CF

open Silmaril.MLIR.Arith (Width)
variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source SeaOfNodes.Loop.MLIR.CF.Op regs out size} {entry : Fin size}
variable {carry merge atLatch : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body carry)
variable (checked : Split.Checked p carry merge atLatch) (prepared : Prepared checked)

def lowerCF := MLIR.CF.DeadProducer.lowerWith p projected checked prepared.final

end CF

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration
