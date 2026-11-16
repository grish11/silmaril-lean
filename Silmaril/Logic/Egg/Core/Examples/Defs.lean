module

public import Silmaril.Logic.Egg.Core.Explanation

@[expose] public section

namespace Silmaril.Logic.Egg.Core.Examples

open Silmaril.Logic.Institution.Examples

inductive Operator : (n : Nat) → (Fin n → Unit) → Unit → Type where
  | a : Operator 0 (fun _ => ()) ()
  | zero : Operator 0 (fun _ => ()) ()
  | add : Operator 2 (fun _ => ()) ()

abbrev signature : Signature := ⟨Unit, Operator⟩
abbrev context (n : Nat) : Fin n → signature.S := fun _ => ()
abbrev Term (n : Nat) := EQ.Term signature (context n) ()
def a {n : Nat} : Term n := .app .a Fin.elim0
def zero {n : Nat} : Term n := .app .zero Fin.elim0
def add {n : Nat} (x y : Term n) : Term n := .app .add (Fin.cases x (fun _ => y))

def addZero : Rule signature := ⟨1, context 1, [], ⟨(), add (.var 0) zero, .var 0⟩⟩
def rules : Set (Rule signature) := {addZero}
def initial : Term 0 := add (add a zero) zero

def model : Model signature where
  carrier _ := Nat
  op o := match o with
    | .a => fun _ => 7
    | .zero => fun _ => 0
    | .add => fun args => args 0 + args 1

/-- The omitted guard would wrongly equate 7+0 with 0 in the example algebra. -/
def guarded : Rule signature :=
  ⟨2, context 2, [⟨(), .var 0, zero⟩], ⟨(), add (.var 0) (.var 1), .var 1⟩⟩

end Silmaril.Logic.Egg.Core.Examples
