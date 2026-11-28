module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.CanonicalLive.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveSelected

/-! # Readback separation for canonical live selected programs -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.CanonicalLive

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.OpenReplay
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance canonicalLiveThmsHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy
/-- Interpret the actual packed selected tree in the validated model for
the selected seed. The table grammar is reflected in its witnessed normal form. -/
theorem readTree_map_outcomes {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n)
    (env : Finite.Assignment n) :
    ((CanonicalLive.payloadDenote.map (ScopedTarget.packed (X := replyContext n) (L := L)
      p.selected.elaborate)).of (replyInput n env)).outcomes = p.witnessed.normal.outcomes env :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveSelected.readTree_map_outcomes p env

/-- The validated payload model evaluates the actual selected packed arrow. -/
theorem map_outcomes {L : List (Ty Empty)} {n : Nat} (p : CanonicalLive L n) (env : Finite.Assignment n) :
    ((CanonicalLive.payloadDenote.map p.target.packed).of (replyInput n env)).outcomes = p.normal.outcomes env :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveSelected.map_outcomes p env

/-- Every exposed slot ranges over both bits. Structural unit frames are
absent from the logical assignment, and a tested slot is deleted in its arms. -/
theorem projection_ne_constant {n : Nat} (slot : Fin n) (bit : Bool) :
    (fun env : Finite.Assignment n => env slot) ≠ fun _ => bit :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveSelected.projection_ne_constant slot bit

/-- Observations at every assignment recover the canonical selected program. -/
theorem eq_of_observations {L : List (Ty Empty)} {n : Nat} (p q : CanonicalLive L n)
    (h : ∀ env, ((CanonicalLive.payloadDenote.map p.target.packed).of (replyInput n env)).outcomes =
      ((CanonicalLive.payloadDenote.map q.target.packed).of (replyInput n env)).outcomes) : p = q :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveSelected.eq_of_observations p q h

/-- Exact readback equality characterizes native packed equality on canonical programs. -/
theorem readback_eq_iff_packed {L : List (Ty Empty)} {n : Nat} (p q : CanonicalLive L n) :
    p.readback = q.readback ↔ p.target.packed = q.target.packed :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveSelected.readback_eq_iff_packed p q

/-- Distinct canonical readbacks have different outcomes in a model validated for the selected seed. -/
theorem readback_ne_separated {L : List (Ty Empty)} {n : Nat} (p q : CanonicalLive L n)
    (ne : p.readback ≠ q.readback) :
    ∃ env, ((CanonicalLive.payloadDenote.map p.target.packed).of (replyInput n env)).outcomes ≠
      ((CanonicalLive.payloadDenote.map q.target.packed).of (replyInput n env)).outcomes :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveSelected.readback_ne_separated p q ne

/-- On sources with exact canonical-target admission, projection-quote comparison decides native packed equality. -/
theorem projection_compare_iff {L : List (Ty Empty)} {n : Nat} (left right : SelectedAt (replyContext n) L)
    (p q : CanonicalLive L n) (hl : left.projectionCanonical = p.target) (hr : right.projectionCanonical = q.target) :
    (left.compareProjectionQuotes right).accepted = true ↔ left.packedSource = right.packedSource :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveSelected.projection_compare_iff left right p q hl hr

/-- An admitted readback mismatch separates the original packed sources in the validated model. -/
theorem admitted_readback_ne_separated {L : List (Ty Empty)} {n : Nat} (left right : SelectedAt (replyContext n) L)
    (p q : CanonicalLive L n) (hl : left.projectionCanonical = p.target) (hr : right.projectionCanonical = q.target)
    (ne : p.readback ≠ q.readback) :
    ∃ env, ((CanonicalLive.payloadDenote.map left.packedSource).of (replyInput n env)).outcomes ≠
      ((CanonicalLive.payloadDenote.map right.packedSource).of (replyInput n env)).outcomes :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CanonicalLiveSelected.admitted_readback_ne_separated left right p q hl hr ne

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.CanonicalLive
