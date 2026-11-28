module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Defs

/-! # Finite feedback rows with a reply-selected second request -/

@[expose] public section

open Silmaril.Isotope.LetIter.PaperExpression

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n} {S B : Code}

/-- A row can perform the original single step, or dispatch its first
reply to a second row with an independently typed request. -/
inductive Plan (F : Family n) (S B : Code)
  | one (row : Row F S B)
  | two (first : Opcode F) (argument : first.argCode.Value)
      (second : first.replyCode.Value → Row F S B)

def Plan.source : Plan F S B → Expr (Opcode F)
  | .one row => row.source
  | .two f x k => .let₁ (.op f (f.argCode.literal x)) (f.replyCode.dispatch (fun r => (k r).source) (.var 0))

abbrev Plans (F : Family n) (S B : Code) := S.Value → Plan F S B

def Plans.source (M : Plans F S B) : Expr (Opcode F) :=
  S.dispatch (fun s => (M s).source) (.var 0)

def Plan.replyCode : Plan F S B → Code
  | .one _ => .unit
  | .two f _ _ => f.replyCode

def Plan.second : (p : Plan F S B) → p.replyCode.Value → Row F S B
  | .one r, _ => r
  | .two _ _ k, v => k v

namespace Code

/-- Replace each leaf of the state code by the reply code specific to that
state. One-step rows receive a unit slot that no original row targets. -/
def dependent : (s : Code) → (s.Value → Code) → Code
  | .unit, p => p PUnit.unit
  | .sum l r, p => .sum (dependent l (fun v => p (.inl v))) (dependent r (fun v => p (.inr v)))

def encode : (s : Code) → (p : s.Value → Code) → (v : s.Value) → (p v).Value → (Code.dependent s p).Value
  | .unit, _, .unit, x => x
  | .sum l _, p, .inl v, x => .inl (encode l (fun v => p (.inl v)) v x)
  | .sum _ r, p, .inr v, x => .inr (encode r (fun v => p (.inr v)) v x)

def decode : (s : Code) → (p : s.Value → Code) → (Code.dependent s p).Value → (v : s.Value) × (p v).Value
  | .unit, _, x => ⟨PUnit.unit, x⟩
  | .sum l _, p, .inl x =>
      let d := decode l (fun v => p (.inl v)) x
      ⟨.inl d.1, d.2⟩
  | .sum _ r, p, .inr x =>
      let d := decode r (fun v => p (.inr v)) x
      ⟨.inr d.1, d.2⟩

end Code

def Plans.pending (M : Plans F S B) : Code :=
  Code.dependent S (fun s => (M s).replyCode)

abbrev Plans.stateCode (M : Plans F S B) : Code := Code.sum S M.pending

def Plan.expandFirst (P : Code) : (row : Plan F S B) → (row.replyCode.Value → P.Value) →
    Row F (Code.sum S P) B
  | .one r, _ => r.map Sum.inl
  | .two f x _, encode => .call f x (fun r => .inr (.inr (encode r)))

/-- Each original state issues its first request. A two-request row
records the first reply in a pending state. The pending row issues the
selected second request and sends any repeat back to an original state. -/
def Plans.expand (M : Plans F S B) : Table F M.stateCode B
  | .inl s => (M s).expandFirst M.pending (Code.encode S (fun s => (M s).replyCode) s)
  | .inr v =>
    let pair := Code.decode S (fun s => (M s).replyCode) v
    ((M pair.1).second pair.2).map Sum.inl

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous
