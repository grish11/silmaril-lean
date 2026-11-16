module

public import Silmaril.Logic.Egglog.Core.Thms

@[expose] public section

namespace Silmaril.Logic.Egglog.Core.Examples
open Silmaril.Logic.Institution.Examples

inductive Constructor : (n : Nat) → (Fin n → Unit) → Unit → Type where
  | number (value : Nat) : Constructor 0 (fun _ => ()) ()
inductive Predicate : (n : Nat) → (Fin n → Unit) → Type where
  | reachable : Predicate 1 (fun _ => ())
inductive TableSymbol : (n : Nat) → (Fin n → Unit) → Unit → Type where
  | next : TableSymbol 1 (fun _ => ()) ()

abbrev signature : Signature :=
  { S := Unit, Op := Constructor, Rel := Predicate, Function := TableSymbol }
abbrev context (n : Nat) : Fin n → signature.S := fun _ => ()
abbrev Term (n : Nat) := EQ.Term signature.toSignature (context n) ()
def number {n : Nat} (v : Nat) : Term n := .app (.number v) Fin.elim0
def lookup {n : Nat} (x y : Term n) : Atom signature (context n) :=
  .row .next (fun _ => x) y
def reachable {n : Nat} (x : Term n) : Atom signature (context n) :=
  .relation .reachable (fun _ => x)
def rule : Rule signature :=
  ⟨2, context 2, [lookup (.var 0) (.var 1)], reachable (.var 1)⟩

/-- Missing custom-table rows remain absent. -/
def emptyModel : Model signature where
  carrier _ := Nat
  op o := match o with | .number v => fun _ => v
  rel _ _ := False
  row _ _ _ := False
  functional _ _ _ _ h := h.elim

/-- The table is defined only at input zero. -/
def populatedModel : Model signature where
  carrier _ := Nat
  op o := match o with | .number v => fun _ => v
  rel r := match r with | .reachable => fun args => args 0 = 1
  row f := match f with | .next => fun args result => args 0 = 0 ∧ result = 1
  functional f := by
    cases f
    intro args x y hx hy
    exact hx.2.trans hy.2.symm

/-- Constructors may share a value; free-constructor disjointness is not assumed. -/
def quotientModel : Model signature where
  carrier _ := Unit
  op _ _ := ()
  rel _ _ := True
  row _ _ _ := False
  functional _ _ _ _ h := h.elim
end Silmaril.Logic.Egglog.Core.Examples
