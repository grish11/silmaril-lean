module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.Native

/-! Bounded native source execution through the two feedback occurrences. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges

open Diamond (Model Signature ValueSort)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

theorem Program.source_entry (p : Program Op regs out) (m : Model.{u, v, w} Op) (fuel : Nat)
    (input : Bank (regs := regs) m) :
    p.source.runFrom m (fuel + 1) 0 input = p.source.runFrom m fuel 1 (p.preheader.eval m input) := rfl

/-- One header visit returns immediately or spends two further visits on
dispatch and the selected feedback block. Insufficient fuel gives none. -/
theorem Program.source_header (p : Program Op regs out) (m : Model.{u, v, w} Op) (fuel : Nat)
    (old : Bank (regs := regs) m) :
    p.source.runFrom m (fuel + 1) 1 old =
      match p.step m old with
      | .inl result => some result
      | .inr (_, next) => p.source.runFrom m (fuel - 2) 1 next :=
  Proofs.source_header p m fuel old

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges
