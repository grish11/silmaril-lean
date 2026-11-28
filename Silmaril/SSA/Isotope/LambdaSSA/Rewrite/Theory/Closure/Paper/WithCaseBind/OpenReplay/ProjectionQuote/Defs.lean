module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Defs

/-! # Quoting direct retained projections in a witnessed tree -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement

open Silmaril
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

/-- Expand each direct slot return to its full projection table, keeping
the request and test nodes, emit lists, and typed exits. -/
def ReadTree.quoteProjections {L : List (Ty Empty)} : {n : Nat} → ReadTree L n → ReadTree L n
  | n, .ret emits pos i => .retExpr emits pos (Finite.Expr.quote n (fun env => env i))
  | _, .retExpr emits pos e => .retExpr emits pos e
  | _, .request emits label bound l r =>
    .request emits label bound l.quoteProjections r.quoteProjections
  | _, .testRequest emits test label low high fl fr tl tr =>
    .testRequest emits test label low high
      fl.quoteProjections fr.quoteProjections tl.quoteProjections tr.quoteProjections

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement
