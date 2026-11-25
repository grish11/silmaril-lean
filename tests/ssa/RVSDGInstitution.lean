module

import Silmaril.SSA.RVSDG.Institution.Categorical.Thms

namespace Silmaril.SSA.RVSDG.Institution.Tests
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Silmaril.Logic.Institution

private abbrev Ty := PortType Unit Unit
private abbrev state : Ty := .state ()
private abbrev payload : Ports Ty := [state]
private abbrev args : Ports Ty := [.control 3, state]

private inductive SourceOp : Dialect Unit Unit where
  | advance : SourceOp payload payload
  | legacyAdvance : SourceOp payload payload

private inductive TargetOp : Dialect Unit Unit where
  | increment : TargetOp payload payload

private abbrev source : Signature Unit Unit := ⟨SourceOp⟩
private abbrev target : Signature Unit Unit := ⟨TargetOp⟩

-- A dialect migration that identifies two previously distinct instructions.
private def migrate : source ⟶ target :=
  ⟨fun op => match op with
    | .advance => TargetOp.increment
    | .legacyAdvance => TargetOp.increment⟩

example : SourceOp.advance ≠ SourceOp.legacyAdvance := by
  intro h
  cases h

example : (Signature.opcodeMap migrate) SourceOp.advance = (Signature.opcodeMap migrate) SourceOp.legacyAdvance := rfl

private def primitiveArm {Op : Dialect Unit Unit} (op : Op payload payload) :
    Term Op payload [] [payload] payload :=
  .bind ⟨payload, .simple op, .cons (.arg .head) .nil, fun i => i.elim0⟩
    (fun i => i.elim0) (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def switchNode {Op : Dialect Unit Unit} : Node Op args [] payload :=
  ⟨args, .gamma 1, .cons (.arg .head) (.cons (.arg (.tail .head)) .nil),
    Fin.cases [] (fun _ => [payload])⟩

-- Arm zero passes through the old state. The other two run the supplied
-- instructions in fresh child regions and return the resulting state.
private def switch {Op : Dialect Unit Unit} (first second : Op payload payload) :
    Term Op args [] [payload] payload :=
  .bind switchNode
    (Fin.cases (motive := fun j => Term Op payload [] ((switchNode (Op := Op)).childSigs j) payload)
      (.ret (.cons (.arg .head) .nil))
      (Fin.cases (primitiveArm first) (fun _ => primitiveArm second)))
    (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def equation : Equation source.op :=
  ⟨args, payload, [payload], [payload],
    (switch SourceOp.advance SourceOp.advance).toGraph,
    (switch SourceOp.legacyAdvance SourceOp.advance).toGraph⟩

private def targetModel : Model target.op where
  value _ := Unit
  state _ := Nat
  run
    | .increment, .cons n .nil => .cons (Nat.succ n) .nil

private def distinctModel : Model source.op where
  value _ := Unit
  state _ := Nat
  run
    | .advance, .cons n .nil => .cons (Nat.succ n) .nil
    | .legacyAdvance, .cons n .nil => .cons (Nat.succ (Nat.succ n)) .nil

private def entry (i : Fin 3) : Tuple targetModel.Val args :=
  .cons ⟨i⟩ (.cons (10 : Nat) .nil)

private theorem translatedHolds : (equation.map (Signature.opcodeMap migrate)).Holds targetModel := by
  intro input
  change (mapGraph (Signature.opcodeMap migrate) (switch SourceOp.advance SourceOp.advance).toGraph).run targetModel input =
    (mapGraph (Signature.opcodeMap migrate) (switch SourceOp.legacyAdvance SourceOp.advance).toGraph).run targetModel input
  simp only [mapGraph_toGraph]
  cases input with
  | cons selector tail =>
    rcases selector with ⟨i⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) j
      · rfl
      · exact Fin.cases rfl (fun z => z.elim0) k

example : equation.Holds (reduct (Signature.opcodeMap migrate) targetModel) :=
  (Equation.satisfaction (Signature.opcodeMap migrate) equation targetModel).mp translatedHolds

-- Read the same equation through the institution's actual sentence and model functors.
example : (room target).Sat (Discrete.mk targetModel)
    (((inst Unit Unit).I.map migrate).sen equation) :=
  translatedHolds

private abbrev dialectInst : Inst.{1, 0, 0, 1, 1} := inst Unit Unit

example : (dialectInst.I.obj target).Sat (Discrete.mk targetModel)
      ((dialectInst.I.map migrate).sen equation) ↔
    (dialectInst.I.obj source).Sat ((dialectInst.I.map migrate).mod.obj (Discrete.mk targetModel)) equation :=
  (dialectInst.I.map migrate).sat (Discrete.mk targetModel) equation

private theorem distinctFails : ¬equation.Holds distinctModel := by
  intro h
  have bad := h (entry 1)
  change (Tuple.cons (11 : Nat) .nil : Tuple distinctModel.Val payload) = .cons (12 : Nat) .nil at bad
  cases bad

example : (equation.map (Signature.opcodeMap migrate)).lhs.run targetModel (entry 0) =
    (.cons (10 : Nat) .nil : Tuple targetModel.Val payload) := by
  change (mapGraph (Signature.opcodeMap migrate) (switch SourceOp.advance SourceOp.advance).toGraph).run targetModel _ = _
  simp only [mapGraph_toGraph]
  rfl

example : (equation.map (Signature.opcodeMap migrate)).rhs.run targetModel (entry 2) =
    (.cons (11 : Nat) .nil : Tuple targetModel.Val payload) := by
  change (mapGraph (Signature.opcodeMap migrate) (switch SourceOp.legacyAdvance SourceOp.advance).toGraph).run targetModel _ = _
  simp only [mapGraph_toGraph]
  rfl

-- The same nonidentity signature map satisfies the institution law with
-- arbitrary Cartesian port objects and chosen selector cocones.
example {D : Type} [Category D] [CartesianMonoidalCategory D]
    (m : Categorical.Model target.op D) :
    (categoricalRoom target D).Sat (Discrete.mk m)
        (((categoricalInst Unit Unit D).I.map migrate).sen equation) ↔
      (categoricalRoom source D).Sat
        (((categoricalInst Unit Unit D).I.map migrate).mod.obj (Discrete.mk m)) equation :=
  ((categoricalInst Unit Unit D).I.map migrate).sat (Discrete.mk m) equation

private abbrev typeInst : Inst.{1, 0, 0, 1, 1} := categoricalInst Unit Unit (Type 0)

private abbrev specialize : Inst.CoHom typeInst dialectInst := toRuntime Unit Unit

example : (equation.map (Signature.opcodeMap migrate)).HoldsCategorically
    (Categorical.Model.ofRuntime targetModel) :=
  (specialize.satisfaction target (Discrete.mk targetModel)
    (equation.map (Signature.opcodeMap migrate))).mp translatedHolds

example : ¬equation.HoldsCategorically (Categorical.Model.ofRuntime distinctModel) :=
  fun h => distinctFails ((specialize.satisfaction source (Discrete.mk distinctModel) equation).mpr h)

end Silmaril.SSA.RVSDG.Institution.Tests
