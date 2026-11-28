module

public import Silmaril.SSA.RVSDG.Defs

import Silmaril.SSA.RVSDG.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Check.Defs
meta import Silmaril.SSA.RVSDG.NestedTheta.Isomorphism.Check.Defs

namespace Silmaril.SSA.RVSDG.Tests

private abbrev Ty := PortType Unit Unit
private abbrev stateTy : Ty := .state ()
private abbrev valueTy : Ty := .value ()
private abbrev statePorts : Ports Ty := [stateTy]
private abbrev entryPorts : Ports Ty := [.control 3, stateTy]
private abbrev readPorts : Ports Ty := [valueTy, stateTy]
private abbrev resultPorts : Ports Ty := [valueTy, stateTy, valueTy]
private abbrev sigs : List (Ports Ty) := [statePorts, statePorts, readPorts]

private inductive Op : Ports Ty → Ports Ty → Type where
  | record (digit : Nat) : Op statePorts statePorts
  | read : Op statePorts readPorts

private def model : Model Op where
  value _ := Nat
  state _ := List Nat
  run
    | .record digit, .cons trace .nil => .cons ((show List Nat from trace) ++ [digit]) .nil
    | .read, .cons trace .nil => .cons (List.length trace) (.cons trace .nil)

private def pass : Graph Op statePorts [] [] statePorts :=
  .region (fun i => i.elim0) (fun i => i.elim0) (.cons (.arg .head) .nil)

private def recordArm (digit : Nat) : Graph Op statePorts [] [statePorts] statePorts :=
  .region (Fin.cases
    ⟨statePorts, .simple (.record digit), .cons (.arg .head) .nil, fun j => j.elim0⟩
    (fun i => i.elim0))
    (Fin.cases (fun j => j.elim0) (fun i => i.elim0))
    (.cons (.output (0 : Fin 1) .head) .nil)

private def nodes : Nodes Op entryPorts [] sigs :=
  Fin.cases
    ⟨statePorts, .simple (.record 1), .cons (.arg (.tail .head)) .nil, fun j => j.elim0⟩
    (Fin.cases
      ⟨entryPorts, .gamma 1, .cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil),
        Fin.cases [] (fun _ => [statePorts])⟩
      (Fin.cases
        ⟨statePorts, .simple .read, .cons (.output (1 : Fin 2) .head) .nil, fun j => j.elim0⟩
        (fun i => i.elim0)))

-- This graph is built directly as a table. The state from record feeds gamma and
-- the merged state feeds read. The read node's value has two users in the results.
private def graph : Graph Op entryPorts [] sigs resultPorts :=
  .region nodes
    (Fin.cases (fun j => j.elim0)
      (Fin.cases (Fin.cases pass (fun j => recordArm (j.val + 2)))
        (Fin.cases (fun j => j.elim0) (fun i => i.elim0))))
    (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) (.cons (.output (2 : Fin 3) .head) .nil)))

private def entry (choice : Fin 3) : Tuple model.Val entryPorts :=
  .cons ⟨choice⟩ (.cons [] .nil)

private def observation (trace : List Nat) : Tuple model.Val resultPorts :=
  .cons trace.length (.cons trace (.cons trace.length .nil))

example : graph.run model (entry 0) = observation [1] := rfl
example : graph.run model (entry 1) = observation [1, 2] := rfl
example : graph.run model (entry 2) = observation [1, 3] := rfl
example : graph.toTerm.run model (entry 2) = observation [1, 3] := rfl
example : graph.toTerm.toGraph = graph := Graph.toGraph_toTerm graph

private def term : Term Op statePorts [] [statePorts] statePorts :=
  .bind ⟨statePorts, .simple (.record 7), .cons (.arg .head) .nil, fun j => j.elim0⟩
    (fun j => j.elim0) (.ret (.cons (.output (0 : Fin 1) .head) .nil))

private def stateTuple (trace : List Nat) : Tuple model.Val statePorts := .cons trace .nil

example : term.toGraph.run model (stateTuple [6]) = stateTuple [6, 7] := rfl
example : term.toGraph.toTerm = term := Term.toTerm_toGraph term

example : ((graph.nodes 2).inputs.get .head).producer = some 1 := rfl

-- An empty prefix rules out all producer vertices, and a state argument cannot supply a value.
example (origin : Origin statePorts [] valueTy) : False := by
  cases origin with
  | arg port => cases port with | tail port => cases port
  | output node _ => exact node.elim0

namespace IndependentRows

deriving instance DecidableEq for PortType

private abbrev one : Ports Ty := [valueTy]
private abbrev two : Ports Ty := [valueTy, valueTy]
private abbrev selection : Ports Ty := [.control 2, valueTy]

private inductive Step : Ports Ty → Ports Ty → Type where
  | offset (amount : Nat) : Step one one

private abbrev keys : NestedTheta.Equality.OpcodeCode Step where
  Key := Nat
  encode | .offset k => k
  injective := by
    intro _ _ x y same
    cases x
    cases y
    cases same
    rfl

private def pair (first second : Nat) (reversed : Bool) :
    NestedTheta.Term Step one [] [one, one] two :=
  .bind ⟨one, .base (.simple (.offset first)), .cons (.arg .head) .nil, fun j => j.elim0⟩
    (fun j => j.elim0)
    (.bind ⟨one, .base (.simple (.offset second)), .cons (.arg .head) .nil, fun j => j.elim0⟩
      (fun j => j.elim0) (.ret (if reversed then
        .cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil)
      else
        .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))))

private def chosenTerm (moved : Bool) : NestedTheta.Term Step selection [] [two] two :=
  .bind ⟨selection, .base (.gamma 0), .cons (.arg .head) (.cons (.arg (.tail .head)) .nil),
    fun _ => [one, one]⟩
    (fun arm => if arm.val = 1 ∧ moved then pair 9 2 true else pair 2 9 false)
    (.ret (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) (.tail .head)) .nil)))

private def chosen (moved : Bool) := (chosenTerm moved).toGraph

example : (pair 9 2 true).toGraph ≠ (pair 2 9 false).toGraph := by
  intro same
  have results := congrArg (fun g => g.results.addresses) same
  change [Address.output 1 0, Address.output 0 0] = [Address.output 0 0, Address.output 1 0] at results
  cases results

private def swap : Nat → Nat
  | 0 => 1
  | 1 => 0
  | i => i

private def swapSelected : NestedTheta.Isomorphism.Mapping :=
  fun path => if path = [(0, 1)] then ⟨swap, swap⟩ else ⟨id, id⟩

private def model : Model Step where
  value _ := Nat
  state _ := Unit
  run | .offset k, .cons n .nil => .cons ((show Nat from n) + k) .nil

private def selectedInput : Tuple model.Val selection := .cons ⟨1⟩ (.cons (10 : Nat) .nil)
private def expected : Tuple model.Val two := .cons (12 : Nat) (.cons (19 : Nat) .nil)

example : (chosen true).run model 1 selectedInput = some expected := rfl
example : (chosen false).run model 1 selectedInput = some expected := rfl

#eval show IO Unit from do
  unless (NestedTheta.Isomorphism.check keys swapSelected (chosen true) (chosen false)).isSome do
    throw (IO.userError "rejected a dependency-preserving row swap in the selected child")
  unless (NestedTheta.Isomorphism.check keys (fun _ => ⟨id, id⟩) (chosen true) (chosen false)).isNone do
    throw (IO.userError "accepted the wrong map for independently renumbered rows")

end IndependentRows

end Silmaril.SSA.RVSDG.Tests
