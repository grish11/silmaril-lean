module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.Defs

/-! # Recognize full quotes of live typed projections -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance canonicalQuotesHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

deriving instance DecidableEq for Finite.Expr

/-- Full quotes have a split at every positive remaining width, and
only literals at width zero. This check avoids generating full tables for
compact expressions. -/
def hasFullQuoteShape : {n : Nat} → Finite.Expr n → Bool
  | 0, .literal _ => true
  | _ + 1, .split low high => hasFullQuoteShape low && hasFullQuoteShape high
  | _, _ => false

/-- A successful recognition is evidence of the exact full quote of a slot. -/
def recognizeProjectionQuote {n : Nat} (e : Finite.Expr n) :
    Option {i : Fin n // e = Finite.Expr.quote n (fun row => row i)} :=
  if hasFullQuoteShape e then
    (List.finRange n).findSome? fun i =>
      if h : e = Finite.Expr.quote n (fun row => row i) then some ⟨i, h⟩ else none
  else none

/-- Keep the pure test grammar intact except for genuine projection quotes.
The index is resolved through the compiler's actual slot map when emitted. -/
def _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement.ReadTree.contractProjectionQuotes
    {L : List (Ty Empty)} : {n : Nat} → ReadTree L n → ReadTree L n
  | _, .ret emits pos i => .ret emits pos i
  | _, .retExpr emits pos e =>
    match recognizeProjectionQuote e with
    | some q => .ret emits pos q.val
    | none => .retExpr emits pos e
  | _, .request emits label bound left right =>
    .request emits label bound left.contractProjectionQuotes right.contractProjectionQuotes
  | _, .testRequest emits test low lowBound highBound fl fr tl tr =>
    .testRequest emits test low lowBound highBound
      fl.contractProjectionQuotes fr.contractProjectionQuotes tl.contractProjectionQuotes tr.contractProjectionQuotes

/-- Preserve the original matched-guard decisions and contract projection
quotes only in the retained continuation subtrees. -/
def SelectedAt.projectionCanonicalRegion {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    Region signature.Instr :=
  p.traversal.renderWith ReadTree.contractProjectionQuotes

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
