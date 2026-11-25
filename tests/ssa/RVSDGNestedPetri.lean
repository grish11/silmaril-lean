module

import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri.Tests

open Relation (ReflTransGen)

private abbrev Ty := PortType Unit Unit
private abbrev st : Ports Ty := [.state ()]
private abbrev val : Ports Ty := [.value ()]
private abbrev tickOut : Ports Ty := Theta.BodyResults st
private abbrev args : Ports Ty := .control 2 :: st
private abbrev outs : Ports Ty := st ++ val

private inductive Op : Ports Ty → Ports Ty → Type where
  | tick (canStop : Bool) : Op st tickOut
  | literal : Op [] val

private def model : Model Op where
  value _ := Nat
  state _ := Nat
  run
    | .tick canStop, .cons x .nil =>
      let y := (show Nat from x) + 1
      .cons (⟨if canStop && decide (2 ≤ y) then (0 : Fin 2) else 1⟩ : ULift (Fin 2))
        (.cons y .nil)
    | .literal, .nil => .cons (9 : Nat) .nil

private def state (n : Nat) : Tuple model.Val st := .cons n .nil
private def note : Tuple model.Val val := .cons (9 : Nat) .nil
private def input : Tuple model.Val args := .cons ⟨(1 : Fin 2)⟩ (state 0)
private def output : Tuple model.Val outs := .cons (2 : Nat) note

private def tickBody (canStop : Bool) : Term Op st [] [tickOut] tickOut :=
  let node : Node Op st [] tickOut :=
    ⟨st, .base (.simple (.tick canStop)), .cons (.arg .head) .nil, fun i => i.elim0⟩
  .bind node (fun i => Fin.elim0 (show Fin 0 from i))
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

private def arm (canStop : Bool) : Term Op st [] [st] st :=
  .bind (thetaVertex [tickOut]) (fun _ => tickBody canStop) (.ret (thetaResults st))

private def term : Term Op args [] [st, val] outs :=
  let selectNode : Node Op args [] st :=
    ⟨args, .base (.gamma 0), .cons (.arg .head) (.cons (.arg (.tail .head)) .nil), fun _ => [st]⟩
  let noteNode : Node Op args [st] val :=
    ⟨[], .base (.simple .literal), .nil, fun i => i.elim0⟩
  .bind selectNode (fun i => arm ((show Fin 2 from i).val == 1)) <|
    .bind noteNode (fun i => Fin.elim0 (show Fin 0 from i)) <|
      .ret (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))

private def graph := term.toGraph
private abbrev Mark := GraphMarking model graph

private def enteredGamma : Mark :=
  (.waiting (1 : Fin 2) (state 0, .pending, PUnit.unit), .pending, PUnit.unit)
private def enteredLoop : Mark :=
  (.waiting (1 : Fin 2) (state 0, .waiting (0 : Fin 1) (state 0, .pending, PUnit.unit), PUnit.unit),
    .pending, PUnit.unit)
private def first : Mark :=
  (.waiting (1 : Fin 2) (state 0, .waiting (0 : Fin 1)
    (state 0, .done (Theta.bodyResult model true (state 1)), PUnit.unit), PUnit.unit), .pending, PUnit.unit)
private def interleaving : Mark :=
  (.waiting (1 : Fin 2) (state 0, .waiting (0 : Fin 1)
    (state 0, .done (Theta.bodyResult model true (state 1)), PUnit.unit), PUnit.unit), .done note, PUnit.unit)
private def restarted : Mark :=
  (.waiting (1 : Fin 2) (state 0, .waiting (0 : Fin 1) (state 1, .pending, PUnit.unit), PUnit.unit),
    .done note, PUnit.unit)
private def second : Mark :=
  (.waiting (1 : Fin 2) (state 0, .waiting (0 : Fin 1)
    (state 1, .done (Theta.bodyResult model false (state 2)), PUnit.unit), PUnit.unit), .done note, PUnit.unit)
private def committedLoop : Mark :=
  (.waiting (1 : Fin 2) (state 0, .done (state 2), PUnit.unit), .done note, PUnit.unit)
private def committedGamma : Mark := (.done (state 2), .done note, PUnit.unit)

-- Arm 0 keeps requesting another iteration. Only the selected arm fires.
-- An unrelated root vertex fires before the selected loop has committed.
private theorem schedule : ReflTransGen (Step model graph input) (initial model graph) committedGamma := by
  have h1 : Step model graph input (initial model graph) enteredGamma := .enter rfl rfl
  have h2 : Step model graph input enteredGamma enteredLoop := .advance (.enter rfl rfl)
  have h3 : Step model graph input enteredLoop first := .advance (.advance (.primitive rfl rfl))
  have h4 : Step model graph input first interleaving := .later (.primitive rfl rfl)
  have h5 : Step model graph input interleaving restarted := .advance (.restart rfl rfl rfl)
  have h6 : Step model graph input restarted second := .advance (.advance (.primitive rfl rfl))
  have h7 : Step model graph input second committedLoop := .advance (.commit rfl rfl)
  have h8 : Step model graph input committedLoop committedGamma := .commit rfl rfl
  exact (((((((ReflTransGen.single h1).tail h2).tail h3).tail h4).tail h5).tail h6).tail h7).tail h8

example : Finishes model graph input output := ⟨committedGamma, schedule, rfl⟩

example : graph.toTerm.Returns model input output :=
  (finishes_toTerm model graph input output).1 ⟨committedGamma, schedule, rfl⟩

example : result model graph input restarted = none := rfl

example : finished model (past := []) (tickBody true) (state 1) PUnit.unit
    (pending model (tickBody true)) = none := rfl

end Silmaril.SSA.RVSDG.NestedTheta.Petri.Tests
