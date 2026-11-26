module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.ProjectionQuotes.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalProjectionQuotes

/-! # Native soundness and idempotence for live projection quotes -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local instance canonicalQuotesThmsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- The recognizer recovers the exact quoted coordinate. -/
theorem recognizeProjectionQuote_exact {n : Nat} (i : Fin n) :
    recognizeProjectionQuote (Finite.Expr.quote n (fun row => row i)) = some ⟨i, rfl⟩ :=
  CanonicalProjectionQuotes.recognize_exact i

/-- Contracting the terminal quotes again leaves the selected tree unchanged. -/
theorem contractProjectionQuotes_idempotent {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n) :
    p.contractProjectionQuotes.contractProjectionQuotes = p.contractProjectionQuotes :=
  CanonicalProjectionQuotes.contract_idempotent p

/-- Repeating the terminal pass on the retained subtrees emits the same region. -/
theorem SelectedAt.projectionCanonical_idempotent {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    p.traversal.renderWith (fun tree => tree.contractProjectionQuotes.contractProjectionQuotes) =
      p.projectionCanonicalRegion :=
  congrArg p.traversal.renderWith (by
    funext _ tree
    exact contractProjectionQuotes_idempotent tree)

/-- Equal exact typed projections compile to the same terminal, even when
the source uses different logical indices and widths. -/
theorem contractProjectionQuotes_same_projection {X : Ty Empty} {L : List (Ty Empty)} {n m : Nat}
    (pos : Position L) (emits : List Bool)
    (left : Fin n → Term signature.Instr X Bit) (right : Fin m → Term signature.Instr X Bit)
    (i : Fin n) (j : Fin m) (same : left i = right j) :
    ((ReadTree.retExpr emits pos (Finite.Expr.quote n (fun row => row i))).contractProjectionQuotes).selectedWith left =
      (ReadTree.ret emits pos j).selectedWith right :=
  CanonicalProjectionQuotes.contract_same_projection pos emits left right i j same

theorem SelectedAt.projectionCanonical_typed {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    ValueBranches [X] p.projectionCanonicalRegion L :=
  CanonicalProjectionQuotes.canonical_typed p

/-- The canonical region has the original physical input and ordered exits. -/
@[expose] def SelectedAt.projectionCanonical {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    ScopedTarget X L :=
  ⟨p.projectionCanonicalRegion, p.projectionCanonical_typed⟩

/-- Contracting a live projection quote preserves the original packed arrow. -/
theorem SelectedAt.packed_projectionCanonical {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    p.packedSource = p.projectionCanonical.packed :=
  CanonicalProjectionQuotes.packed_canonical p

/-- Compare after contracting exact live projection quotes. Acceptance
carries native equality of the actual original packed arrows. -/
@[expose] def SelectedAt.compareProjectionQuotes {X : Ty Empty} {L : List (Ty Empty)} (left right : SelectedAt X L) :
    EqualityVerdict (left.packedSource = right.packedSource) :=
  match left.projectionCanonical.compare right.projectionCanonical with
  | .equal h => .equal (left.packed_projectionCanonical.trans ((congrArg ScopedTarget.packed h).trans
      right.packed_projectionCanonical.symm))
  | .unknown => .unknown

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
