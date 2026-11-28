module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Defs

/-! # Return encodings for finite feedback observations -/

@[expose] public section

open Silmaril.Elgot

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite

universe u v

abbrev Code.Large (c : Code) : Type 1 := Ty.denote (Lifted carriers) c.ty

/-- The native weak-tree model uses the larger universe. This equivalence
preserves every unit and sum tag. -/
def Code.raise (c : Code) : c.Value ≃ c.Large := (toSmall carriers c.ty).symm

/-- Interpret a table with native state and result encodings. Requests and
replies retain their original event types. -/
def Table.raised {Q K S B : Code} (M : Table Q K S B) :
    Machine carriers (Opcode.ask : Opcode Q K) S.Large B.Large where
  request s := M.request (S.raise.symm s)
  reply s r := Sum.map B.raise S.raise (M.reply (S.raise.symm s) r)

/-- Change the return encoding of an observation, retaining the exact typed
events and every reply continuation. -/
def mapResult {E : Type → Type} {A : Type u} {B : Type v} (f : A → B) :
    (n : Nat) → ITree.Approx E A n → ITree.Approx E B n
  | 0, _ => PUnit.unit
  | n + 1, obs => obs.map (fun
      | .ret a => .ret (f a)
      | .vis ev k => .vis ev (fun r => mapResult f n (k r)))

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
