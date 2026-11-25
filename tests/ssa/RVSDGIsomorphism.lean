module

import Silmaril.SSA.RVSDG.Isomorphism.Petri.Thms

namespace Silmaril.SSA.RVSDG.Isomorphism.Tests

private abbrev Ty := PortType Unit Unit
private abbrev nty : Ty := .value ()
private abbrev sty : Ty := .state ()
private abbrev np : Ports Ty := [nty]
private abbrev sp : Ports Ty := [sty]
private abbrev both : Ports Ty := [nty, sty]
private abbrev entryPorts : Ports Ty := [.control 2, nty, sty]

private inductive Op : Ports Ty → Ports Ty → Type where
  | add (n : Nat) : Op np np
  | stamp (n : Nat) : Op sp sp

private def model : Model Op where
  value _ := Nat
  state _ := List Nat
  run
    | .add n, .cons x .nil => .cons ((show Nat from x) + n) .nil
    | .stamp n, .cons trace .nil => .cons ((show List Nat from trace) ++ [n]) .nil

private abbrev add {args : Ports Ty} {past : List (Ports Ty)} (n : Nat)
    (wire : Origin args past nty) : Node Op args past np :=
  ⟨np, .simple (.add n), .cons wire .nil, fun j => j.elim0⟩

private abbrev stamp {args : Ports Ty} {past : List (Ports Ty)} (n : Nat)
    (wire : Origin args past sty) : Node Op args past sp :=
  ⟨sp, .simple (.stamp n), .cons wire .nil, fun j => j.elim0⟩

private def leftArmTerm (arm : Fin 2) : Term Op both [] [np, sp] both :=
  let first : Node Op both [] np := add (4 + arm.val) (.arg .head)
  let second : Node Op both [np] sp := stamp (5 + arm.val) (.arg (.tail .head))
  .bind first (fun j => Fin.elim0 (show Fin 0 from j)) <|
    .bind second (fun j => Fin.elim0 (show Fin 0 from j)) <|
      .ret (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))

private def rightArmTerm (arm : Fin 2) : Term Op both [] [sp, np] both :=
  let first : Node Op both [] sp := stamp (5 + arm.val) (.arg (.tail .head))
  let second : Node Op both [sp] np := add (4 + arm.val) (.arg .head)
  .bind first (fun j => Fin.elim0 (show Fin 0 from j)) <|
    .bind second (fun j => Fin.elim0 (show Fin 0 from j)) <|
      .ret (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil))

private abbrev leftGamma : Node Op entryPorts [np, sp] both :=
  ⟨entryPorts, .gamma 0, .cons (.arg .head)
    (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil)), fun _ => [np, sp]⟩

private abbrev rightGamma : Node Op entryPorts [sp, np] both :=
  ⟨entryPorts, .gamma 0, .cons (.arg .head)
    (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil)), fun _ => [sp, np]⟩

private def leftTerm : Term Op entryPorts [] [np, sp, both] both :=
  let first : Node Op entryPorts [] np := add 1 (.arg (.tail .head))
  let second : Node Op entryPorts [np] sp := stamp 3 (.arg (.tail (.tail .head)))
  .bind first (fun j => Fin.elim0 (show Fin 0 from j)) <|
    .bind second (fun j => Fin.elim0 (show Fin 0 from j)) <|
      .bind leftGamma leftArmTerm <|
        .ret (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) .nil))

private def rightTerm : Term Op entryPorts [] [sp, np, both] both :=
  let first : Node Op entryPorts [] sp := stamp 3 (.arg (.tail (.tail .head)))
  let second : Node Op entryPorts [sp] np := add 1 (.arg (.tail .head))
  .bind first (fun j => Fin.elim0 (show Fin 0 from j)) <|
    .bind second (fun j => Fin.elim0 (show Fin 0 from j)) <|
      .bind rightGamma rightArmTerm <|
        .ret (.cons (.output (2 : Fin 3) .head) (.cons (.output (2 : Fin 3) (.tail .head)) .nil))

private def left := leftTerm.toGraph
private def right := rightTerm.toGraph

private def exchange {n : Nat} : Fin (n + 2) → Fin (n + 2) :=
  Fin.cases 1 (Fin.cases 0 (fun rest => rest.succ.succ))

private theorem exchange_twice {n : Nat} (i : Fin (n + 2)) : exchange (exchange i) = i := by
  refine Fin.cases ?_ (Fin.cases ?_ (fun i => ?_)) i <;> rfl

private def swapFirstTwo (n : Nat) : Fin (n + 2) ≃ Fin (n + 2) :=
  ⟨exchange, exchange, exchange_twice, exchange_twice⟩

private theorem childIso (arm : Fin 2) :
    Graph.Isomorphic Op (leftArmTerm arm).toGraph (rightArmTerm arm).toGraph := by
  refine .intro rfl rfl (swapFirstTwo 0) ?_ ?_ rfl ?_
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (fun j => j.elim0)) i
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (fun j => j.elim0)) i
  · intro i
    exact Fin.cases (fun j => j.elim0) (Fin.cases (fun j => j.elim0) (fun j => j.elim0)) i

private theorem renumbered : Graph.Isomorphic Op left right := by
  refine .intro rfl rfl (swapFirstTwo 1) ?_ ?_ rfl ?_
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => j.elim0))) i
  · intro i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => j.elim0))) i
  · intro i
    exact Fin.cases (fun j => j.elim0)
      (Fin.cases (fun j => j.elim0) (Fin.cases childIso (fun j => j.elim0))) i

example (m : Model Op) (input : Tuple m.Val entryPorts) : left.run m input = right.run m input :=
  renumbered.run_eq m input

private def input : Tuple model.Val entryPorts := .cons ⟨(1 : Fin 2)⟩ (.cons (10 : Nat) (.cons [] .nil))

example : right.run model input = .cons (16 : Nat) (.cons [3, 6] .nil) :=
  (renumbered.run_eq model input).symm.trans rfl

example (output : Tuple model.Val both) :
    Petri.Finishes model left input output ↔ Petri.Finishes model right input output :=
  renumbered.finishes_iff model input output

private def selectArg (p : Port [nty, nty] nty) : Graph Op [nty, nty] [] [] np :=
  (Term.ret (.cons (.arg p) .nil)).toGraph

-- The boundary wiring is part of isomorphism, even when the argument colours coincide.
example : ¬ Graph.Isomorphic Op (selectArg .head) (selectArg (.tail .head)) := by
  intro iso
  cases iso with
  | intro _ _ _ _ _ results _ => cases results

end Silmaril.SSA.RVSDG.Isomorphism.Tests
