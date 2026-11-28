module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Correctness

/-! # Exact branch, return and feedback from each projected incoming occurrence -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch

open SeaOfNodes.Diamond (Model ValueSort)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge : Mask regs}
variable {p : Program src entry} (checked : Checked p carry merge) (m : Model.{u, v, w} Op)

theorem Checked.eval_agrees (old : Bank (regs := regs) m) :
    checked.eval m (merge.project old) = observe p carry ((Nested.Numbered.tail p).eval m old) :=
  Proofs.eval_agrees p m checked old

/-- Renaming the required operands gives the original latch packet for
the predecessor's independently compiled bank. -/
theorem Checked.incoming_agrees (old : Bank (regs := regs) m) (occurrence : Occurrence) :
    checked.eval m (incoming p merge m old occurrence) =
      observe p carry ((Nested.Numbered.tail p).eval m (p.mergeBank m old occurrence)) :=
  Checked.eval_agrees checked m (p.mergeBank m old occurrence)

/-- The complete bank may differ. The condition, return and kept
feedback have the same values whenever the projected inputs agree. -/
theorem Checked.observes_eq (cert : Checked p carry merge) (left right : Bank (regs := regs) m)
    (same : merge.project left = merge.project right) :
    observe p carry ((Nested.Numbered.tail p).eval m left) =
      observe p carry ((Nested.Numbered.tail p).eval m right) :=
  (Checked.eval_agrees cert m left).symm.trans
    ((congrArg (cert.eval m) same).trans (Checked.eval_agrees cert m right))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch
