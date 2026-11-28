module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Numbered.Defs

/-! # Emit the smaller γ with the merge–latch observation certificate -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered

open SeaOfNodes.Diamond (ValueSort)
open Diamond.Prune (HeaderProjection)
open Nested.Numbered (KeptResult)
open Blocks.Prune (Mask)

universe u v

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge : Mask regs}
variable (p : Program src entry) (projected : HeaderProjection (src p.header).body carry)

def thetaBody (_checked : Checked p carry merge) :=
  MergePrune.Numbered.thetaBodyFor p projected merge

/-- Reuse the numbered γ/θ emitter with the verified narrower bank.
Dropped wires use in-scope fillers and cannot affect the latch packet. -/
def lower (checked : Checked p carry merge) (result : KeptResult p (mask := carry)) :=
  Nested.Numbered.lowerWith p result (thetaBody p projected checked)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered
