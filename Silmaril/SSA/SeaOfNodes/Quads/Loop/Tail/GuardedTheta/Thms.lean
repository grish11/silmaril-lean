module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.GuardedTheta.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.GuardedTheta.Correctness

/-! The entry guard observes the initial bank before any θ body evaluation. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.GuardedTheta

open SeaOfNodes.Diamond (Model Signature Ty ValueSort dataPorts)
open RVSDG (Port)
open RVSDG.NestedTheta (Term iterate)
open Join (Block Opcode model)
open Tail.Diamond (bodyPorts)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} {sigs : List (List (Ty Data))}

theorem test_packet (test : Port (dataPorts regs) (.value .predicate)) (bank : Bank (regs := regs) m) :
    (model m).run (.route (.test test (.take 1) (.take 0))) bank =
      RVSDG.Theta.bodyResult (model m) (bank.get test).down bank :=
  Proofs.test_packet test bank

theorem lower_run (entry : Block Op regs)
    (test : Port (dataPorts regs) (.value .predicate)) (result : Port (dataPorts regs) (.value out))
    (body : Term (Opcode Op) (dataPorts regs) [] sigs (bodyPorts regs))
    (fuel : Nat) (input : Bank (regs := regs) m) :
    (lowerTerm entry test result body).toGraph.run (model m) fuel input =
      let bank := entry.eval m input
      if (bank.get test).down then
        (iterate (body.run (model m) fuel) (fun tag => tag.down.val == 1) fuel bank).map
          (fun done => .cons (done.get result) .nil)
      else some (.cons (bank.get result) .nil) :=
  Proofs.lower_run test result body entry fuel input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.GuardedTheta
