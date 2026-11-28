module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.GuardedTheta.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Join.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.GuardedTheta.Proofs

open SeaOfNodes.Diamond (Model Signature Ty Val ValueSort dataPorts)
open RVSDG (Port Tuple Wires Locals)
open RVSDG.NestedTheta (Term Kind Graph iterate)
open Join (Block Opcode model)
open Join.Finite (lastBank lastBank_read)
open Tail.Diamond (bodyPorts thenBase_eval)
open Blocks (Bank)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} {sigs past : List (List (Ty Data))}
variable (test : Port (dataPorts regs) (.value .predicate))
variable (result : Port (dataPorts regs) (.value out))
variable (body : Term (Opcode Op) (dataPorts regs) [] sigs (bodyPorts regs))

theorem test_packet (bank : Bank (regs := regs) m) :
    (model m).run (.route (.test test (.take 1) (.take 0))) bank =
      RVSDG.Theta.bodyResult (model m) (bank.get test).down bank := by
  by_cases selected : (bank.get test).down = true <;>
    simp [model, Join.Choice.eval, RVSDG.Theta.bodyResult, selected]

private theorem continue_run (fuel : Nat) (bank : Bank (regs := regs) m) :
    (arm result body 1).run (model m) fuel bank =
      (iterate (body.run (model m) fuel) (fun tag => tag.down.val == 1)
        fuel bank).map (fun next => .cons (next.get result) .nil) := by
  let finish (next : Bank (regs := regs) m) :=
    Tuple.cons (SeaOfNodes.Diamond.read m ((lastBank [] (dataPorts regs)).get result)
      bank (Locals.snoc PUnit.unit next)) .nil
  change (iterate (body.run (model m) fuel) (fun tag => tag.down.val == 1)
    fuel ((initial regs).read bank PUnit.unit)).bind (fun next => some (finish next)) = _
  rw [read_initial m]
  cases iterate (body.run (model m) fuel) (fun tag => tag.down.val == 1) fuel bank with
  | none => rfl
  | some next =>
    change some (finish next) = some (.cons (next.get result) .nil)
    dsimp only [finish]
    rw [← read_get]
    exact congrArg (fun values : Bank (regs := regs) m =>
      some (Tuple.cons (values.get result) .nil : Tuple (Val m.value) [.value out]))
      (lastBank_read (past := []) m bank PUnit.unit next)

private def observed (fuel : Nat) (bank : Bank (regs := regs) m) :=
  if (bank.get test).down then (arm result body 1).run (model m) fuel bank
  else some (Tuple.cons (bank.get result) .nil)

private theorem guard_eval (wires : Wires (dataPorts regs) past (dataPorts regs)) (fuel : Nat)
    (input : Bank (regs := regs) m) (locals : Locals (Val m.value) past) :
    (guard test result body wires).eval (model m) fuel input locals =
      observed test result body fuel (wires.read input locals) := by
  let bank := wires.read input locals
  let routed : Tuple (Val m.value) (bodyPorts regs) :=
    (model m).run (.route (.test test (.take 1) (.take 0))) bank
  let gamma : Kind (Opcode Op) (bodyPorts regs) [.value out] := .base (.gamma 0)
  change (gamma.eval (model m) fuel (fun i x => (arm result body i).run (model m) fuel x)
    ((lastBank past (bodyPorts regs)).read input (locals.snoc routed))).bind
    (fun value => some ((lastBank (past ++ [bodyPorts regs]) [.value out]).read
      input ((locals.snoc routed).snoc value))) = _
  rw [lastBank_read m]
  rw [show routed = _ from test_packet test bank]
  have pick : gamma.eval (model m) fuel
      (fun i x => (arm result body i).run (model m) fuel x)
      (RVSDG.Theta.bodyResult (model m) (bank.get test).down bank) =
      observed test result body fuel bank := by
    unfold observed
    cases (bank.get test).down <;> rfl
  rw [pick]
  change _ = observed test result body fuel bank
  cases observed test result body fuel bank with
  | none => rfl
  | some value =>
    change some ((lastBank (past ++ [bodyPorts regs]) [.value out]).read input
      ((locals.snoc (RVSDG.Theta.bodyResult (model m) (bank.get test).down bank)).snoc value)) = _
    rw [lastBank_read m]

theorem lower_run (entry : Block Op regs) (fuel : Nat) (input : Bank (regs := regs) m) :
    (lowerTerm entry test result body).toGraph.run (model m) fuel input =
      let bank := entry.eval m input
      if (bank.get test).down then
        (iterate (body.run (model m) fuel) (fun tag => tag.down.val == 1) fuel bank).map
          (fun done => .cons (done.get result) .nil)
      else some (.cons (bank.get result) .nil) := by
  rw [← Graph.run_toTerm, Term.toTerm_toGraph]
  unfold lowerTerm Term.run
  erw [thenBase_eval (observe := observed test result body fuel)
    (agrees := fun wires locals => guard_eval test result body wires fuel input locals)]
  have reads := Block.lowerFrom_eval (past := []) entry .jump m input PUnit.unit (initial regs)
  rw [read_initial m] at reads
  refine (congrArg (observed test result body fuel) reads).trans ?_
  unfold observed
  rw [continue_run]
  rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.GuardedTheta.Proofs
