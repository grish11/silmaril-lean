module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Prefix.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Execution.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Proofs

open SeaOfNodes.Diamond (Model Ty Val ValueSort dataPorts sortValue)
open RVSDG (Locals Tuple Wires)
open RVSDG.NestedTheta (Term)
open Join (Block model)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (thenBase_eval routeLatchWith_eval)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (m : Model.{u, v, w} Op)

private theorem afterOuterSuffix_run {results : List (Ty Data)} {suffix : List (List (Ty Data))}
    (finish : Wires (dataPorts regs) (mergeScope p) (dataPorts regs) →
      Term (Join.Opcode Op) (dataPorts regs) (mergeScope p) suffix results)
    (fuel : Nat) (old : Bank (regs := regs) m)
    (observe : Bank (regs := regs) m → Option (Tuple (Val m.value) results))
    (agrees : ∀ wires locals, (finish wires).eval (model m) fuel old locals = observe (wires.read old locals)) :
    (afterOuterSuffix p finish).run (model m) fuel old =
      observe (p.mergeBank m old (p.toControl.selected m old)) := by
  unfold afterOuterSuffix
  apply Prefix.afterHeader_run p.toRoutes m _ fuel old (fun bank => observe (p.outerSuffixBank m bank))
  intro merged locals
  erw [thenBase_eval (observe := observe) (agrees := agrees), Block.lowerFrom_eval, p.outer_suffix_bank]
  rfl

theorem outer_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (outerRegion p).toGraph.run (model m) fuel old =
      some (p.outerBank m old (p.toControl.selected m old)) := by
  rw [← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  exact Prefix.afterHeader_run p.toRoutes m .ret fuel old some (fun _ _ => rfl)

theorem merge_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (mergeRegion p).toGraph.run (model m) fuel old =
      some (p.mergeBank m old (p.toControl.selected m old)) := by
  rw [← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  exact afterOuterSuffix_run p m .ret fuel old some (fun _ _ => rfl)

theorem activation_run (fuel : Nat) (old : Bank (regs := regs) m) :
    (thetaBody p).run (model m) fuel old =
      let next := nextBank p m old
      some (RVSDG.Theta.bodyResult (model m) (next.get p.again).down next) := by
  let packet (bank : Bank (regs := regs) m) :=
    some (RVSDG.Theta.bodyResult (model m) (bank.get p.again).down bank)
  apply afterOuterSuffix_run p m _ fuel old (fun bank => packet ((tail p).eval m bank))
  intro merged locals
  erw [thenBase_eval (observe := packet), Block.lowerFrom_eval]
  · rfl
  · intro wires later
    exact routeLatchWith_eval m p.again wires fuel old later

theorem lower_run (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower p).run (model m) fuel input =
      (src.runFrom m (sourceVisits p m fuel input) entry input).map (fun value => .cons value .nil) :=
  Shared.Numbered.Execution.lower_run p.toControl m (selectedBank p m) (selectedVisits p m) (thetaBody p)
    (p.run_to_merge m) (activation_run p m) fuel input

theorem returns_iff (input : Bank (regs := regs) m) (value : sortValue m.value out) :
    (lower p).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value :=
  Shared.Numbered.Execution.returns_iff p.toControl m (selectedBank p m) (selectedVisits p m) (thetaBody p)
    (p.run_to_merge m) (activation_run p m) input value

theorem noFiniteReturn_iff (input : Bank (regs := regs) m) :
    (∀ fuel, (lower p).run (model m) fuel input = none) ↔
      ∀ fuel, src.runFrom m fuel entry input = none :=
  Shared.Numbered.Execution.noFiniteReturn_iff p.toControl m (selectedBank p m) (selectedVisits p m) (thetaBody p)
    (p.run_to_merge m) (activation_run p m) input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Proofs
