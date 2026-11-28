module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Defs

/-! # Contracting terminal targets of finite feedback -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n} {S B : Code}

def Table.contractReply (M : Table F S B) : B.Value ⊕ S.Value → B.Value ⊕ S.Value
  | .inl b => .inl b
  | .inr t =>
    match M t with
    | .ret b => .inl b
    | .call .. => .inr t

/-- A reply that would repeat into an immediate return can return its value
directly. All terminal rows, requests, and other repeats are preserved. -/
def Table.contract (M : Table F S B) : Table F S B := fun s =>
  match M s with
  | .ret v => .ret v
  | .call f x k => .call f x (fun r => M.contractReply (k r))


end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous
