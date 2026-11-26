module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Execution.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Proofs

open SeaOfNodes.Diamond (Model ValueSort sortValue)
open RVSDG.NestedTheta (Term)
open Join (Block model)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (thenBase_eval routeLatchWith_eval)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (m : Model.{u, v, w} Op)

theorem merge_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (mergeRegion p).toGraph.run (model m) fuel old =
      some (p.mergeBank m old (p.toControl.selected m old)) := by
  rw [← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  exact Prefix.afterHeader_run (Prefix.ofProgram p) m .ret fuel old some (fun _ _ => rfl)

theorem activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBody p).run (model m) fuel old =
      let next := nextBank p m old
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next) := by
  let packet (bank : Bank (regs := regs) m) :=
    some (RVSDG.Theta.bodyResult (model m) (bank.get p.again).down bank)
  apply Prefix.afterHeader_run (Prefix.ofProgram p) m _ fuel old (fun bank => packet ((tail p).eval m bank))
  intro merged locals
  erw [thenBase_eval (observe := packet), Block.lowerFrom_eval]
  · rfl
  · intro wires later
    exact routeLatchWith_eval m p.again wires fuel old later

private abbrev merge (old : Bank (regs := regs) m) :=
  p.mergeBank m old (p.toControl.selected m old)

private abbrev count (old : Bank (regs := regs) m) :=
  p.mergeVisits (p.toControl.selected m old)

private theorem visits_agree (fuel : Nat) (old : Bank (regs := regs) m) :
    visitsFrom p m fuel old = Execution.visitsFrom p.toControl m (merge p m) (count p m) fuel old := by
  induction fuel generalizing old with
  | zero => rfl
  | succ fuel ih =>
    rw [visitsFrom, Execution.visitsFrom]
    dsimp only
    rw [ih]
    rfl

theorem lower_run (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p).run (model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) := by
  rw [sourceVisits, visits_agree]
  exact Execution.lower_run p.toControl m (merge p m) (count p m) (thetaBody p)
    (p.run_to_merge m) (activation_run p m) fuel input

theorem returns_iff (input : Bank (regs := regs) m) (value : sortValue m.value out) :
    (lower p).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value :=
  Execution.returns_iff p.toControl m (merge p m) (count p m) (thetaBody p)
    (p.run_to_merge m) (activation_run p m) input value

theorem noFiniteReturn_iff (input : Bank (regs := regs) m) :
    (∀ fuel, (lower p).run (model m) fuel input = none) ↔
      ∀ fuel, src.runFrom m fuel entry input = none :=
  Execution.noFiniteReturn_iff p.toControl m (merge p m) (count p m) (thetaBody p)
    (p.run_to_merge m) (activation_run p m) input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Proofs
