module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Defs

/-! # Shared θ construction and source visit count -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Execution

open SeaOfNodes.Diamond (Model ValueSort dataPorts)
open RVSDG.NestedTheta (Term)
open Join (Opcode)
open Blocks (Bank)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond (bodyPorts thenBase iterateThenReturnWith)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (control : Control src entry) (m : Model.{u, v, w} Op)
variable (merge : Bank (regs := regs) m → Bank (regs := regs) m)
variable (routeVisits : Bank (regs := regs) m → Nat)

def nextBank (old : Bank (regs := regs) m) : Bank (regs := regs) m :=
  ((src control.join).body ++ (src control.latch).body).eval m (merge old)

def visitsFrom : Nat → Bank (regs := regs) m → Nat
  | 0, _ => 0
  | fuel + 1, old =>
    let next := nextBank control m merge old
    (if (next.get control.again).down then visitsFrom fuel next else 0) + (routeVisits old + 2)

def sourceVisits (fuel : Nat) (input : Bank (regs := regs) m) : Nat :=
  visitsFrom control m merge routeVisits fuel ((src entry).body.eval m input) + 1

variable {bodySigs : List (List (SeaOfNodes.Diamond.Ty Data))}
variable (body : Term (Opcode Op) (dataPorts regs) [] bodySigs (bodyPorts regs))

def lowerTerm :
    Term (Opcode Op) (dataPorts regs) [] ((src entry).body.producers ++ [dataPorts regs]) [.value out] :=
  thenBase ((src entry).body.lowerFrom (initial regs) .jump) (iterateThenReturnWith body control.result)

def lower : RVSDG.NestedTheta.Graph (Opcode Op) (dataPorts regs) []
    ((src entry).body.producers ++ [dataPorts regs]) [.value out] :=
  (lowerTerm control body).toGraph

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Execution
