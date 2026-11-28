module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Defs
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Intrinsic.Defs

/-! # A typed source grammar for native finite feedback -/

@[expose] public section

open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless (Tm)
open Silmaril.Isotope.LetIter.PaperExpression

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native

variable {Φ : Type}

/-- Closed expressions built from the finite literal codec, possibly with
pure lets computing the payload of a constructor. -/
inductive Closed : Code → Expr Φ → Type
  | literal (c : Code) (v : c.Value) : Closed c (c.literal v)
  | letId {c : Code} {a : Expr Φ} : Closed c a → Closed c (.let₁ a (.var 0))
  | letInl {l r : Code} {a : Expr Φ} : Closed l a → Closed (.sum l r) (.let₁ a (.inl (.var 0)))
  | letInr {l r : Code} {a : Expr Φ} : Closed r a → Closed (.sum l r) (.let₁ a (.inr (.var 0)))

def Closed.read {c : Code} {a : Expr Φ} : Closed c a → c.Value
  | .literal _ v => v
  | .letId a => a.read
  | .letInl a => .inl a.read
  | .letInr a => .inr a.read

/-- Read the newest constructor slot. A leaf ignores the slot and the
ambient context. A pure let may copy the selector before continuing. -/
inductive Decision (Leaf : Expr Φ → Type) : Code → Expr Φ → Type
  | leaf {c : Code} {a : Expr Φ} : Leaf a → Decision Leaf c a
  | copy {c : Code} {a : Expr Φ} : Decision Leaf c a → Decision Leaf c (.let₁ (.var 0) a)
  | split {l r : Code} {a b : Expr Φ} :
      Decision Leaf l a → Decision Leaf r b → Decision Leaf (.sum l r) (.case (.var 0) a b)

def Decision.read {Leaf : Expr Φ → Type} {c : Code} {a : Expr Φ} :
    Decision Leaf c a → c.Value → (a : Expr Φ) × Leaf a
  | .leaf h, _ => ⟨_, h⟩
  | .copy d, v => d.read v
  | .split l _, .inl v => l.read v
  | .split _ r, .inr v => r.read v

variable {n : Nat} {F : Family n} {S B : Code}

local notation "Ops" => Opcode F

/-- A row returns a closed value or makes one request with an independently
written closed argument and a constructor decision on the reply. -/
inductive RowSyntax (F : Family n) (S B : Code) : Expr (Opcode F) → Type
  | ret {a : Expr (Opcode F)} : Closed B a → RowSyntax F S B (.inl a)
  | call (f : Opcode F) {a k : Expr (Opcode F)} :
      Closed f.argCode a → Decision (Closed (Code.sum B S)) f.replyCode k →
      RowSyntax F S B (.let₁ (.op f a) k)

def RowSyntax.read {a : Expr Ops} : RowSyntax F S B a → Row F S B
  | .ret v => .ret v.read
  | .call f a replies => .call f a.read (fun r => (replies.read r).2.read)

/-- Source representatives are checked against the actual initializer and
step terms. Their grammar permits pure lets, ignored selectors, and reply
cases, with the exact native endpoint type and effect fixed by the codes
and supplied bound. -/
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

def Program.start (p : Program F S B e) : S.Value := p.initialSyntax.read

def Program.table (p : Program F S B e) : Table F S B :=
  fun s => (p.bodySyntax.read s).2.read

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Native
