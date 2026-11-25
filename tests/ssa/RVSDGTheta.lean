module

import Silmaril.SSA.RVSDG.Theta.Thms
import Silmaril.SSA.RVSDG.Theta.Petri.Thms

namespace Silmaril.SSA.RVSDG.Theta.Tests

private abbrev Ty := PortType Unit Unit
private abbrev st : Ty := .state ()
private abbrev carried : Ports Ty := [st]
private abbrev sigs : List (Ports Ty) := [carried, BodyResults carried]

private inductive Op : Ports Ty → Ports Ty → Type where
  | increment : Op carried carried
  | check (bound : Option Nat) : Op carried (BodyResults carried)

private def model : Model Op where
  value _ := Unit
  state _ := Nat
  run
    | .increment, .cons x .nil => .cons ((show Nat from x) + 1) .nil
    | .check bound, .cons x .nil =>
      let again := match bound with
        | none => true
        | some limit => decide ((show Nat from x) < limit)
      .cons (⟨if again then (1 : Fin 2) else 0⟩ : ULift (Fin 2)) (.cons x .nil)

private def values (n : Nat) : Tuple model.Val carried := .cons n .nil

private def term (bound : Option Nat) : Term Op carried sigs :=
  let increment : Node Op carried [] carried :=
    ⟨carried, .simple .increment, .cons (.arg .head) .nil, fun j => j.elim0⟩
  let check : Node Op carried [carried] (BodyResults carried) :=
    ⟨carried, .simple (.check bound), .cons (.output (0 : Fin 1) .head) .nil, fun j => j.elim0⟩
  ⟨.bind increment (fun j => Fin.elim0 (show Fin 0 from j)) <|
    .bind check (fun j => Fin.elim0 (show Fin 0 from j)) <|
      .ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (1 : Fin 2) (.tail .head)) .nil))⟩

private def loop (bound : Option Nat) : Graph Op carried sigs := (term bound).toGraph

private theorem threeIterations : (loop (some 3)).Returns model (values 0) (values 3) :=
  .again (next := values 1) rfl (.again (next := values 2) rfl (.stop rfl))

example : Petri.Finishes model (loop (some 3)) (values 0) (values 3) :=
  (Petri.finishes_iff model _ _ _).2 threeIterations

example : (term (some 3)).Returns model (values 0) (values 3) :=
  (Term.returns_toGraph (term (some 3)) model _ _).1 threeIterations

-- Tail control runs the body even when the input already reaches the bound.
example : (loop (some 3)).Returns model (values 3) (values 4) := .stop rfl

example : ¬ (loop (some 3)).Diverges model (values 0) :=
  (loop (some 3)).not_diverges_of_returns model threeIterations

private theorem alwaysRestarts : (loop none).Diverges model (values 0) :=
  ⟨values, rfl, fun _ => rfl⟩

example : Petri.Diverges model (loop none) (values 0) :=
  (Petri.diverges_iff model _ _).2 alwaysRestarts

example (output : Tuple model.Val carried) : ¬ Petri.Finishes model (loop none) (values 0) output := by
  intro returned
  exact (loop none).not_diverges_of_returns model ((Petri.finishes_iff model _ _ _).1 returned)
    alwaysRestarts

private def completedFirst : RVSDG.Petri.GraphMarking model (loop (some 3)).body :=
  (.done (values 1), .done (bodyResult model true (values 1)), PUnit.unit)

example : Petri.Step model (loop (some 3)) (.active (values 0) completedFirst)
    (Petri.initial model (loop (some 3)) (values 1)) := .again rfl

-- The previous body's done tokens and colours are discarded when restarting.
example : RVSDG.Petri.result model (loop (some 3)).body (values 1)
    (RVSDG.Petri.initial model (loop (some 3)).body) = none := rfl

end Silmaril.SSA.RVSDG.Theta.Tests
