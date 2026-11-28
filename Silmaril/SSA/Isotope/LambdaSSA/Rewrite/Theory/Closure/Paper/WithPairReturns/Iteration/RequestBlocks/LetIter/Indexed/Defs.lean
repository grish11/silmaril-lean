module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.LetIter.Defs

/-! # Indexed pending-reply codes for normalized LetIter tables -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Indexed

open Silmaril Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LetIter.PaperExpression
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite
open Silmaril.Isotope.LetIter.PaperExpression.Source.FreeTree.Response.Structured.Feedback.Finite.Heterogeneous

variable {n : Nat} {F : Family n} {I P S B : Code}

local notation "Ops" => Opcode F
local notation "U" => Code.unit

/-- All original states have a first request. Its reply selects a
one-request row or immediate return at the common return-or-repeat code. -/
inductive Rows (F : Family n) (S B : Code) : Code → Type
  | leaf (f : Opcode F) : f.argCode.Value → (f.replyCode.Value → Row F S B) → Rows F S B .unit
  | split {L R : Code} : Rows F S B L → Rows F S B R → Rows F S B (.sum L R)

def Rows.plans : {I : Code} → Rows F S B I → I.Value → Plan F S B
  | _, .leaf f x k, _ => .two f x k
  | _, .split l _, .inl v => l.plans v
  | _, .split _ r, .inr v => r.plans v

abbrev Rows.pending (t : Rows F S B I) : Code :=
  Code.dependent I (fun v => (t.plans v).replyCode)

def Rows.firstMap : {I : Code} → (t : Rows F S B I) → (t.pending.Value → P.Value) → Step F I P
  | _, .leaf f x _, tag => .call f x (literals f.replyCode tag)
  | _, .split l r, tag =>
    .split (l.firstMap (fun v => tag (.inl v))) (r.firstMap (fun v => tag (.inr v)))

def Rows.second : {I : Code} → (t : Rows F S B I) → Step F t.pending (.sum B S)
  | _, .leaf f _ k => tabulate f.replyCode (fun v => row (k v) U)
  | _, .split l r => .split l.second r.second

def Rows.fused : {I : Code} → Rows F S B I → Step F I (.sum B S)
  | _, .leaf f x k => .call f x (tabulate f.replyCode (fun v => row (k v) U))
  | _, .split l r => .split l.fused r.fused

def Rows.first (t : Rows F S B I) : Step F I t.pending := t.firstMap id

def Rows.expanded (t : Rows F S B S) : Step F (.sum S t.pending) (.sum B (.sum S t.pending)) :=
  .split (t.firstMap (fun v => .inr (.inr v)))
    (Step.mapOut (O := .sum B S) (P := .sum B (.sum S t.pending)) (Sum.map id Sum.inl) t.second)

def fusedNative (t : Rows F S B S) (init : S.Value) : NTm F 0 :=
  .iter (nativeValue 0 S init) (t.fused.native 0)

def expandedNative (t : Rows F S B S) (init : S.Value) : NTm F 0 :=
  .iter (nativeValue 0 (.sum S t.pending) (.inl init)) (t.expanded.native 0)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.RequestBlockTransport.Indexed
