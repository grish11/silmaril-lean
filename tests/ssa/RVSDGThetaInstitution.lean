module

import Silmaril.SSA.RVSDG.Theta.Institution.Thms
import Silmaril.SSA.RVSDG.Theta.Thms

namespace Silmaril.SSA.RVSDG.Theta.Institution.Tests

open CategoryTheory Silmaril.Logic.Institution
open RVSDG.Institution (reduct)

private abbrev Ty := PortType Unit Unit
private abbrev carried : Ports Ty := [.state ()]
private abbrev results : Ports Ty := BodyResults carried

private inductive SourceOp : Dialect Unit Unit where
  | current : SourceOp carried results
  | legacy : SourceOp carried results

private inductive TargetOp : Dialect Unit Unit where
  | step : TargetOp carried results

private abbrev source : RVSDG.Institution.Signature Unit Unit := ⟨SourceOp⟩
private abbrev target : RVSDG.Institution.Signature Unit Unit := ⟨TargetOp⟩

-- Migrate both typed opcodes to the same loop body operation.
private def migrate : source ⟶ target :=
  ⟨fun op => match op with
    | .current => TargetOp.step
    | .legacy => TargetOp.step⟩

example : SourceOp.current ≠ SourceOp.legacy := by
  intro h
  cases h

private def loop {Op : Dialect Unit Unit} (op : Op carried results) : Graph Op carried [results] :=
  let node : Node Op carried [] results :=
    ⟨carried, .simple op, .cons (.arg .head) .nil, fun i => i.elim0⟩
  (⟨.bind node (fun i => i.elim0)
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))⟩ :
      Term Op carried [results]).toGraph

private def equation : Equation source.op :=
  ⟨carried, [results], [results], loop SourceOp.current, loop SourceOp.legacy⟩

private def targetModel : Model target.op where
  value _ := Unit
  state _ := Nat
  run
    | .step, .cons n .nil =>
      let next := (show Nat from n) + 1
      .cons ⟨if next < 3 then 1 else 0⟩ (.cons next .nil)

private def mixedModel : Model source.op where
  value _ := Unit
  state _ := Nat
  run
    | .current, .cons n .nil => .cons ⟨0⟩ (.cons ((show Nat from n) + 1) .nil)
    | .legacy, .cons n .nil => .cons ⟨1⟩ (.cons ((show Nat from n) + 1) .nil)

private abbrev dialectInst : Inst.{1, 0, 0, 1, 1} := inst Unit Unit

example : (dialectInst.I.obj target).Sat (Discrete.mk targetModel)
      ((dialectInst.I.map migrate).sen equation) ↔
    (dialectInst.I.obj source).Sat ((dialectInst.I.map migrate).mod.obj (Discrete.mk targetModel))
      equation :=
  (dialectInst.I.map migrate).sat (Discrete.mk targetModel) equation

set_option backward.isDefEq.respectTransparency false in
private theorem translatedHolds : (equation.map (RVSDG.Institution.Signature.opcodeMap migrate)).Holds targetModel := by
  intro input
  constructor
  · intro output
    exact Iff.rfl
  · exact Iff.rfl

example : equation.Holds (reduct (RVSDG.Institution.Signature.opcodeMap migrate) targetModel) :=
  (equation.satisfaction (RVSDG.Institution.Signature.opcodeMap migrate) targetModel).mp translatedHolds

example : (equation.map (RVSDG.Institution.Signature.opcodeMap migrate)).rhs.Returns targetModel
    (.cons (0 : Nat) .nil) (.cons (3 : Nat) .nil) :=
  .again (next := .cons (1 : Nat) .nil) rfl (.again (next := .cons (2 : Nat) .nil) rfl (.stop rfl))

private def input (n : Nat) : Tuple mixedModel.Val carried := .cons n .nil

example : ¬equation.Holds mixedModel := by
  intro eq
  have stops : equation.lhs.Returns mixedModel (input 0) (input 1) := .stop rfl
  have restarts : equation.rhs.Diverges mixedModel (input 0) :=
    ⟨input, rfl, fun _ => rfl⟩
  exact equation.lhs.not_diverges_of_returns mixedModel stops ((eq (input 0)).2.mpr restarts)

end Silmaril.SSA.RVSDG.Theta.Institution.Tests
