module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Expansion.Defs

/-! # Native source representatives with up to two requests per round -/

@[expose] public section

open Silmaril.Isotope Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.TwoRequest

variable {n : Nat} {F : Family n} {S B : Code}

local notation "Ops" => Opcode F

/-- A first reply may select any one-request row, including its opcode,
constructor argument, and decision on the second reply. -/
inductive RowSyntax (F : Family n) (S B : Code) : Expr (Opcode F) → Type
  | one {a : Expr (Opcode F)} : Native.RowSyntax F S B a → RowSyntax F S B a
  | two (f : Opcode F) {a k : Expr (Opcode F)} :
      Closed f.argCode a → Decision (Native.RowSyntax F S B) f.replyCode k →
      RowSyntax F S B (.let₁ (.op f a) k)

def RowSyntax.read {a : Expr Ops} : RowSyntax F S B a → Plan F S B
  | .one r => .one r.read
  | .two f a k => .two f a.read (fun r => (k.read r).2.read)

/-- Independently written representatives of the actual native iterator,
with the declared effect bound and finite constructor control. -/
structure Program (F : Family n) (S B : Code) {ε : Type}
    [HasEff (Opcode F) ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] (e : ε) where
  initial : Expr (Opcode F)
  body : Expr (Opcode F)
  initialSyntax : Closed S initial
  bodySyntax : Decision (RowSyntax F S B) S body
  initTerm : Tm Empty (Opcode F) 0
  bodyTerm : Tm Empty (Opcode F) 1
  initial_lowers : initial.toLetIter 0 = some initTerm
  body_lowers : body.toLetIter 1 = some bodyTerm
  effects : ∀ f : Opcode F, instrEff f ≤ e
  iterative : IsIterative e

variable {ε : Type} [HasEff (Opcode F) ε] [SemilatticeSup ε] [OrderBot ε] [EffectIteration ε] {e : ε}

def Program.native (p : Program F S B e) : Tm Empty Ops 0 := .iter p.initTerm p.bodyTerm

def Program.plans (p : Program F S B e) : Plans F S B :=
  fun s => (p.bodySyntax.read s).2.read

def Program.start (p : Program F S B e) : p.plans.stateCode.Value := .inl p.initialSyntax.read

def Program.table (p : Program F S B e) : Table F p.plans.stateCode B :=
  p.plans.expand

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native.TwoRequest
