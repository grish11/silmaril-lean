module

public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Expansion.Defs

/-! # Finite feedback plans with pure transfers -/

@[expose] public section

open Silmaril.Isotope.LetIter.PaperExpression

namespace Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n} {S T B : Code}

/-- An expanded row can also return a constructor-coded next state without a request. -/
inductive TransferRow (F : Family n) (S B : Code)
  | ordinary (row : Row F S B)
  | transfer (target : S.Value)

def TransferRow.source : TransferRow F S B → Expr (Opcode F)
  | .ordinary row => row.source
  | .transfer target => .inr (S.literal target)

def TransferRow.map (h : S.Value → T.Value) : TransferRow F S B → TransferRow F T B
  | .ordinary row => .ordinary (row.map h)
  | .transfer target => .transfer (h target)

abbrev TransferTable (F : Family n) (S B : Code) := S.Value → TransferRow F S B

def TransferTable.source (M : TransferTable F S B) : Expr (Opcode F) :=
  S.dispatch (fun s => (M s).source) (.var 0)

/-- An existing expansion plan or an immediate transfer to an original state. -/
inductive TransferPlan (F : Family n) (S B : Code)
  | ordinary (plan : Plan F S B)
  | transfer (target : S.Value)

def TransferPlan.source : TransferPlan F S B → Expr (Opcode F)
  | .ordinary plan => plan.source
  | .transfer target => .inr (S.literal target)

def TransferPlan.replyCode : TransferPlan F S B → Code
  | .ordinary plan => plan.replyCode
  | .transfer _ => .unit

/-- The unit pending slot of a pure transfer is unused, as with an ordinary one-step plan. -/
def TransferPlan.second : (p : TransferPlan F S B) → p.replyCode.Value → TransferRow F S B
  | .ordinary plan, reply => .ordinary (plan.second reply)
  | .transfer target, _ => .transfer target

def TransferPlan.expandFirst (P : Code) : (p : TransferPlan F S B) → (p.replyCode.Value → P.Value) →
    TransferRow F (.sum S P) B
  | .ordinary plan, encode => .ordinary (plan.expandFirst P encode)
  | .transfer target, _ => .transfer (.inl target)

abbrev TransferPlans (F : Family n) (S B : Code) := S.Value → TransferPlan F S B

def TransferPlans.source (M : TransferPlans F S B) : Expr (Opcode F) :=
  S.dispatch (fun s => (M s).source) (.var 0)

def TransferPlans.pending (M : TransferPlans F S B) : Code :=
  Code.dependent S (fun s => (M s).replyCode)

abbrev TransferPlans.stateCode (M : TransferPlans F S B) : Code := .sum S M.pending

def TransferPlans.expand (M : TransferPlans F S B) : TransferTable F M.stateCode B
  | .inl s => (M s).expandFirst M.pending (Code.encode S (fun s => (M s).replyCode) s)
  | .inr v =>
    let pair := Code.decode S (fun s => (M s).replyCode) v
    ((M pair.1).second pair.2).map Sum.inl

def Plans.withTransfers (M : Plans F S B) : TransferPlans F S B :=
  fun s => .ordinary (M s)

theorem Plans.withTransfers_source (M : Plans F S B) : M.withTransfers.source = M.source :=
  rfl

theorem Plans.withTransfers_expand (M : Plans F S B) (v : M.stateCode.Value) :
    M.withTransfers.expand v = .ordinary (M.expand v) := by
  cases v <;> rfl

theorem Plans.withTransfers_expanded_source (M : Plans F S B) :
    M.withTransfers.expand.source = M.expand.source := by
  change M.stateCode.dispatch (fun s => (M.withTransfers.expand s).source) (.var 0) =
    M.stateCode.dispatch (fun s => (M.expand s).source) (.var 0)
  exact congrArg (fun rows => M.stateCode.dispatch rows (.var 0))
    (funext fun s => congrArg TransferRow.source (M.withTransfers_expand s))

end Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous
