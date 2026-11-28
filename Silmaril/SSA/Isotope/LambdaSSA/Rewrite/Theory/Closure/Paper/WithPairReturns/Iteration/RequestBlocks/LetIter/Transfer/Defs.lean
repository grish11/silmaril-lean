module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Defs
public import Silmaril.SSA.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous.Terminal.Expansion.Transfer.Defs

/-! # Normalized tables with direct, pending-reply and pure transfer rows -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Transfer

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n} {S B I O : Code}

local notation "Ops" => Opcode F
local notation "U" => Code.unit

/-- A normalized transfer-enabled plan table, indexed by its original-state code. -/
inductive Rows (F : Family n) (S B : Code) : Code → Type
  | leaf (p : TransferPlan F S B) : Rows F S B .unit
  | split {L R : Code} : Rows F S B L → Rows F S B R → Rows F S B (.sum L R)

def Rows.plans : {I : Code} → Rows F S B I → I.Value → TransferPlan F S B
  | _, .leaf p, _ => p
  | _, .split l _, .inl v => l.plans v
  | _, .split _ r, .inr v => r.plans v

abbrev Rows.pending (t : Rows F S B I) : Code :=
  Code.dependent I (fun v => (t.plans v).replyCode)

/-- Direct rows transfer their control result to `done`. Two-request rows
send the first reply to `pending`, retaining its state code. -/
def Rows.firstMap :
    {I : Code} → (t : Rows F S B I) →
      ((Code.sum B S).Value → O.Value) → (t.pending.Value → O.Value) → Step F I O
  | _, .leaf (.ordinary (.one r)), done, _ => Step.mapOut done (row r U)
  | _, .leaf (.ordinary (.two f x _)), _, pending => .call f x (literals f.replyCode pending)
  | _, .leaf (.transfer target), done, _ => .lit (done (.inr target))
  | _, .split l r, done, pending =>
    .split (l.firstMap done (fun v => pending (.inl v))) (r.firstMap done (fun v => pending (.inr v)))

def Rows.second : {I : Code} → (t : Rows F S B I) → Step F t.pending (.sum B S)
  | _, .leaf (.ordinary (.one r)) => row r U
  | _, .leaf (.ordinary (.two f _ k)) => tabulate f.replyCode (fun v => row (k v) U)
  | _, .leaf (.transfer target) => .lit (.inr target)
  | _, .split l r => .split l.second r.second

def Rows.fused : {I : Code} → Rows F S B I → Step F I (.sum B S)
  | _, .leaf (.ordinary (.one r)) => row r U
  | _, .leaf (.ordinary (.two f x k)) => .call f x (tabulate f.replyCode (fun v => row (k v) U))
  | _, .leaf (.transfer target) => .lit (.inr target)
  | _, .split l r => .split l.fused r.fused

def Rows.first (t : Rows F S B I) : Step F I (.sum (.sum B S) t.pending) :=
  t.firstMap Sum.inl Sum.inr

def Rows.expanded (t : Rows F S B S) : Step F (.sum S t.pending) (.sum B (.sum S t.pending)) :=
  .split (t.firstMap (Sum.map id Sum.inl) (fun v => .inr (.inr v)))
    (Step.mapOut (O := .sum B S) (P := .sum B (.sum S t.pending)) (Sum.map id Sum.inl) t.second)

def fusedLoop (t : Rows F S B S) (init : S.Value) : NTm F 0 :=
  .iter (nativeValue 0 S init) (t.fused.native 0)

def expandedLoop (t : Rows F S B S) (init : S.Value) : NTm F 0 :=
  .iter (nativeValue 0 (.sum S t.pending) (.inl init)) (t.expanded.native 0)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Transfer
