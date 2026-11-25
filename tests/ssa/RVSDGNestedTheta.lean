module

import Silmaril.SSA.RVSDG.NestedTheta.Thms

namespace Silmaril.SSA.RVSDG.NestedTheta.Tests

private abbrev Ty := PortType Unit Unit
private abbrev carried : Ports Ty := [.state ()]
private abbrev resultPorts : Ports Ty := Theta.BodyResults carried
private abbrev args : Ports Ty := .control 2 :: carried

private inductive Op : Ports Ty → Ports Ty → Type where
  | tick (bound : Nat) : Op carried resultPorts
  | check (bound : Nat) : Op carried resultPorts

private def model : Model Op where
  value _ := Unit
  state _ := Nat
  run
    | .tick bound, .cons x .nil =>
      let y := (show Nat from x) + 1
      .cons (⟨if y < bound then (1 : Fin 2) else 0⟩ : ULift (Fin 2)) (.cons y .nil)
    | .check bound, .cons x .nil =>
      .cons (⟨if (show Nat from x) < bound then (1 : Fin 2) else 0⟩ : ULift (Fin 2)) (.cons x .nil)

private def state (n : Nat) : Tuple model.Val carried := .cons n .nil
private def inputs (tag : Fin 2) : Tuple model.Val args := .cons ⟨tag⟩ (state 0)

private def baseBody (bound : Nat) : RVSDG.Term Op carried [] [resultPorts] resultPorts :=
  let node : RVSDG.Node Op carried [] resultPorts :=
    ⟨carried, .simple (.tick bound), .cons (.arg .head) .nil, fun i => i.elim0⟩
  .bind node (fun i => Fin.elim0 (show Fin 0 from i))
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

private def inner (bound : Nat) : Theta.Graph Op carried [resultPorts] :=
  ⟨(baseBody bound).toGraph⟩

-- One θ is inside another θ body. The inner θ increments once, and the enclosing
-- body's check decides whether to repeat the whole body.
private def outerBody : Term Op carried [] [carried, resultPorts] resultPorts :=
  let first : Node Op carried [] carried := thetaVertex [resultPorts]
  let check : Node Op carried [carried] resultPorts :=
    ⟨carried, .base (.simple (.check 4)), .cons (.output (0 : Fin 1) .head) .nil, fun i => i.elim0⟩
  .bind first (fun _ => Term.ofBase (baseBody 1)) <|
    .bind check (fun i => Fin.elim0 (show Fin 0 from i)) <|
      .ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))

private abbrev gamma : Node Op args [] carried :=
  ⟨args, .base (.gamma 0), .cons (.arg .head) (.cons (.arg (.tail .head)) .nil),
    Fin.cases [] (fun _ => [carried])⟩

private abbrev afterGamma : Node Op args [carried] carried :=
  ⟨carried, .theta carried, .cons (.output (0 : Fin 1) .head) .nil, fun _ => [carried, resultPorts]⟩

private def table : Nodes Op args [] [carried, carried] :=
  Fin.cases gamma (Fin.cases afterGamma (fun i => i.elim0))

-- The graph is assembled directly. Its selected γ arm contains a θ, and the
-- following θ reads the γ result through an ordinary same-region wire.
private def root : Graph Op args [] [carried, carried] carried :=
  .region table
    (Fin.cases
      (Fin.cases
        (.region (fun i => i.elim0) (fun i => i.elim0) (.cons (.arg .head) .nil))
        (fun _ => Graph.ofTheta (inner 2)))
      (Fin.cases (fun _ => outerBody.toGraph) (fun i => i.elim0)))
    (.cons (.output (1 : Fin 2) .head) .nil)

example : root.run model 1 (inputs 1) = none := rfl
example : root.run model 2 (inputs 1) = some (state 4) := rfl
example : root.run model 2 (inputs 0) = none := rfl
example : root.run model 4 (inputs 0) = some (state 4) := rfl

example : root.toTerm.Returns model (inputs 1) (state 4) :=
  (root.returns_iff model (inputs 1) (state 4)).1 ⟨2, rfl⟩

example : root.toTerm.toGraph = root := root.toGraph_toTerm

example : (Graph.ofTheta (inner 2)).Returns model (state 0) (state 2) :=
  ((Graph.returns_ofTheta (inner 2) model (state 0) (state 2))).2 (.again (next := state 1) rfl (.stop rfl))

end Silmaril.SSA.RVSDG.NestedTheta.Tests
