module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Thms

/-! # Finite feedback tables over sums of unit -/

@[expose] public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.PaperExpression

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite

/-- Nonempty finite constructor codes. Distinct tree shapes can encode
different state spaces. -/
inductive Code
  | unit
  | sum (left right : Code)

def Code.ty : Code → Ty Unit
  | .unit => .unit
  | .sum l r => .coprod l.ty r.ty

abbrev carriers (_ : Unit) : Type := Unit

abbrev Code.Value (c : Code) : Type := Ty.denote carriers c.ty

/-- Render a finite code using closed constructor syntax. -/
def Code.literal {Φ : Type} : (c : Code) → c.Value → Expr Φ
  | .unit, _ => .unit
  | .sum l _, .inl v => .inl (l.literal v)
  | .sum _ r, .inr v => .inr (r.literal v)

/-- Select a closed row using a pure selector. A unit code has one row
and needs no case. -/
def Code.dispatch {Φ : Type} : (c : Code) → (c.Value → Expr Φ) → Expr Φ → Expr Φ
  | .unit, rows, _ => rows PUnit.unit
  | .sum l r, rows, arg =>
      .case arg (l.dispatch (fun x => rows (.inl x)) (.var 0))
        (r.dispatch (fun x => rows (.inr x)) (.var 0))

/-- A signature with a single request on the declared finite codes. -/
inductive Opcode (input reply : Code)
  | ask

instance {Q K : Code} : HasTy (Opcode Q K) (Ty Unit) :=
  ⟨fun _ => Q.ty, fun _ => K.ty⟩

abbrev Table (Q K S B : Code) := Machine carriers (Opcode.ask : Opcode Q K) S.Value B.Value

/-- A pure state map reifies by dispatching over the input state code. -/
def stateMap {Φ : Type} (S T : Code) (h : S.Value → T.Value) : Expr Φ :=
  S.dispatch (fun s => T.literal (h s)) (.var 0)

/-- Map the repeat state in a source control result, leaving returns intact. -/
def mapControl {Φ : Type} (_B : Code) {S T : Code} (h : S.Value → T.Value) : Expr Φ :=
  .case (.var 0) (.inl (.var 0)) (.inr (stateMap S T h))

variable {Q K S B : Code}

def Table.row (M : Table Q K S B) (s : S.Value) : Expr (Opcode Q K) :=
  .let₁ (.op .ask (Q.literal (M.request s)))
    (K.dispatch (fun r => (Code.sum B S).literal (M.reply s r)) (.var 0))

/-- Read the state code then run the corresponding single-request row. -/
def Table.source (M : Table Q K S B) : Expr (Opcode Q K) :=
  S.dispatch M.row (.var 0)

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
