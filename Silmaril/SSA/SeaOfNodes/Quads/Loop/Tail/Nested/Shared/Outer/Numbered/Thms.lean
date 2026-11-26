module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Correctness
import Silmaril.SSA.RVSDG.NestedTheta.Thms

/-! # Selected merge banks, simultaneous latching and finite θ returns -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered

open SeaOfNodes.Diamond (Model ValueSort sortValue)
open RVSDG.NestedTheta (Graph Term)
open Join (model)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (m : Model.{u, v, w} Op)

/-- The outer γ forwards the selected route's full bank before executing
the common outer suffix. -/
theorem outer_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (outerRegion p).toGraph.run (model m) fuel old =
      some (p.outerBank m old (p.toControl.selected m old)) :=
  Proofs.outer_run p m fuel old

/-- The final merge reads the one shared suffix on the selected outer bank. -/
theorem merge_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (mergeRegion p).toGraph.run (model m) fuel old =
      some (p.mergeBank m old (p.toControl.selected m old)) :=
  Proofs.merge_run p m fuel old

/-- The actual numbered body sends the same full bank to feedback or exit,
with the latch's original predicate providing the tag. -/
theorem activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBody p).toGraph.run (model m) fuel old =
      let next := nextBank p m old
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next) := by
  rw [← Graph.run_toTerm, Term.toTerm_toGraph]
  exact Proofs.activation_run p m fuel old

/-- Match a θ activation bound with the source visits of the selected
routes. The outer suffix is charged on either route and the inner suffix
only on the outer true route. -/
theorem lower_run (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p).run (model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) :=
  Proofs.lower_run p m fuel input

theorem returns_iff (input : Bank (regs := regs) m) (value : sortValue m.value out) :
    (lower p).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value :=
  Proofs.returns_iff p m input value

/-- Neither runner has a finite return exactly when the other exhausts
at every finite bound. -/
theorem noFiniteReturn_iff (input : Bank (regs := regs) m) :
    (∀ fuel, (lower p).run (model m) fuel input = none) ↔
      ∀ fuel, src.runFrom m fuel entry input = none :=
  Proofs.noFiniteReturn_iff p m input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered
