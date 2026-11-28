module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Transfer.Defs

/-! # Normalized tables with direct rows and pending-reply rows -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Mixed

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n} {S B I O : Code}

/-- A normalized #3846 table can freely mix the two existing plan forms. -/
inductive Rows (F : Family n) (S B : Code) : Code → Type
  | leaf (p : Plan F S B) : Rows F S B .unit
  | split {L R : Code} : Rows F S B L → Rows F S B R → Rows F S B (.sum L R)

def Rows.plans : {I : Code} → Rows F S B I → I.Value → Plan F S B
  | _, .leaf p, _ => p
  | _, .split l _, .inl v => l.plans v
  | _, .split _ r, .inr v => r.plans v

def Rows.withTransfers : {I : Code} → Rows F S B I → Transfer.Rows F S B I
  | _, .leaf p => .leaf (.ordinary p)
  | _, .split l r => .split l.withTransfers r.withTransfers

abbrev Rows.pending (t : Rows F S B I) : Code := t.withTransfers.pending

abbrev Rows.firstMap (t : Rows F S B I)
    (done : (Code.sum B S).Value → O.Value) (pending : t.pending.Value → O.Value) : Step F I O :=
  t.withTransfers.firstMap done pending

abbrev Rows.second (t : Rows F S B I) : Step F t.pending (.sum B S) :=
  t.withTransfers.second

abbrev Rows.fused (t : Rows F S B I) : Step F I (.sum B S) :=
  t.withTransfers.fused

abbrev Rows.first (t : Rows F S B I) : Step F I (.sum (.sum B S) t.pending) :=
  t.withTransfers.first

abbrev Rows.expanded (t : Rows F S B S) : Step F (.sum S t.pending) (.sum B (.sum S t.pending)) :=
  t.withTransfers.expanded

def fusedLoop (t : Rows F S B S) (init : S.Value) : NTm F 0 :=
  Transfer.fusedLoop t.withTransfers init

def expandedLoop (t : Rows F S B S) (init : S.Value) : NTm F 0 :=
  Transfer.expandedLoop t.withTransfers init

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Mixed
