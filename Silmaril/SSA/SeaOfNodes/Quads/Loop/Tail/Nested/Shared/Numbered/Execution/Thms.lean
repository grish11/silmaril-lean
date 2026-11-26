module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Execution.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Execution.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Execution

open SeaOfNodes.Diamond (Model ValueSort sortValue dataPorts)
open RVSDG.NestedTheta (Term iterate)
open Join (Opcode model)
open Blocks (Bank)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (bodyPorts thenBase iterateThenReturnWith)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (control : Control src entry) (m : Model.{u, v, w} Op)
variable (merge : Bank (regs := regs) m → Bank (regs := regs) m)
variable (routeVisits : Bank (regs := regs) m → Nat)

variable {bodySigs : List (List (SeaOfNodes.Diamond.Ty Data))}
variable (body : Term (Opcode Op) (dataPorts regs) [] bodySigs (bodyPorts regs))

/-- The generated θ starts from the bank computed by the original preheader. -/
theorem lower_iterate (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower control body).run (model m) fuel input =
      (iterate (body.run (model m) fuel) (fun tag => tag.down.val == 1) fuel
        ((src entry).body.eval m input)).map (fun bank => .cons (bank.get control.result) .nil) :=
  Proofs.lower_iterate control m body fuel input

variable (reachesJoin : ∀ old fuel,
  src.runFrom m (fuel + routeVisits old) control.header old = src.runFrom m fuel control.join (merge old))
variable (activation : ∀ fuel old,
  body.run (model m) fuel old =
    let next := nextBank control m merge old
    some (RVSDG.Theta.bodyResult (model m) (next.get control.again).down next))

include reachesJoin activation in
theorem lower_run (fuel : Nat) (input : Bank (regs := regs) m) :
    (lower control body).run (model m) fuel input =
      (src.runFrom m (sourceVisits control m merge routeVisits fuel input) entry input).map (fun value => .cons value .nil) :=
  Proofs.lower_run control m merge routeVisits body reachesJoin activation fuel input

include reachesJoin activation in
theorem returns_iff (input : Bank (regs := regs) m) (value : sortValue m.value out) :
    (lower control body).Returns (model m) input (.cons value .nil) ↔
      ∃ fuel, src.runFrom m fuel entry input = some value :=
  Proofs.returns_iff control m merge routeVisits body reachesJoin activation input value

include reachesJoin activation in
theorem noFiniteReturn_iff (input : Bank (regs := regs) m) :
    (∀ fuel, (lower control body).run (model m) fuel input = none) ↔
      ∀ fuel, src.runFrom m fuel entry input = none :=
  Proofs.noFiniteReturn_iff control m merge routeVisits body reachesJoin activation input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Execution
