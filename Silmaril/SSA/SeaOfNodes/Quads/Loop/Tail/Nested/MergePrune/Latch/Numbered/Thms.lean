module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.Correctness

/-! # Selected merge packets and finite returns of the narrower numbered loop -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered

open SeaOfNodes.Diamond (Model ValueSort sortValue)
open Diamond.Prune (HeaderProjection)
open MergePrune.Numbered (latchPacket)
open Nested.Numbered (KeptResult sourceVisits)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge : Mask regs}
variable (p : Program src entry) (m : Model.{u, v, w} Op)
variable (projected : HeaderProjection (src p.header).body carry) (checked : Checked p carry merge)

/-- The actual θ body supplies the original stop tag and projected carry. -/
theorem activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBody p projected checked).run (Join.model m) fuel (carry.project old) =
      some (latchPacket p carry m (Nested.Numbered.nextBank p m old)) :=
  Proofs.activation_run p m projected checked fuel old

variable (result : KeptResult p (mask := carry))

theorem lower_run (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p projected checked result).run (Join.model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) :=
  Nested.Numbered.lowerWith_run p m _ (activation_run p m projected checked) result fuel input

theorem run_agrees (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p projected checked result).run (Join.model m) fuel input =
      (Nested.Numbered.lower p projected result).run (Join.model m) fuel input :=
  (lower_run p m projected checked result fuel input).trans
    (Nested.Numbered.lower_run p m projected result fuel input).symm

theorem returns_iff (input : Bank (regs := regs) m) (value : sortValue m.value out) :
    (lower p projected checked result).Returns (Join.model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value :=
  (exists_congr fun fuel => by rw [run_agrees p m projected checked result fuel input]).trans
    (Nested.Numbered.returns_iff p m projected result input value)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered
