module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseReplyAgreement

/-! # The selected and witnessed observations of finite payload requests -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement

open Silmaril CategoryTheory
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply (Trace)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit signature model modelCoherent)
open Silmaril.Semantics.NondeterministicTrace (Tagged)
open Silmaril.Isotope.LetIter.Semantics.Categorical (boundEnv)
open Paper.WithProjectionReturnsAndUnitEta (denoteArrow)
open Paper.WithProjectionReturnsAndUnitEta.ExitPacking (packArrow)

local notation "J" => Kleisli.J (m := Trace)
local notation "M" => Kleisli.types

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- The packed selected tree and the witnessed LetCase program have the same
set of tagged outcomes. Both use the published payload separator's algebra and
the source program's emit prefixes, bound replies and ordered exit positions. -/
theorem DirectProgram.packedOutcomes_eq (H : Ty Empty) (L : List (Ty Empty)) (p : DirectProgram (H :: L)) :
    letI := Kleisli.instructions model
    let := modelCoherent
    ((denoteArrow J M (fun _ _ => ⟨rfl, rfl⟩) (packArrow p.selected.elaborate.property)).of PUnit.unit).outcomes =
      Reply.Payload.programOutcomes H L p.val :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseReplyAgreement.packed_outcomes H L p

/-- The packed intrinsic arrow at unit gives the concrete computation of
the separator's actual witnessed LetCase program in the closed environment. -/
theorem DirectProgram.denote_agrees (H : Ty Empty) (L : List (Ty Empty)) (p : DirectProgram (H :: L)) :
    letI := Kleisli.instructions model
    let := modelCoherent
    (denoteArrow J M (fun _ _ => ⟨rfl, rfl⟩) (packArrow p.selected.elaborate.property)).of PUnit.unit =
      Kleisli.run model (Reply.Payload.program H L p.val).toLetCase.2
        (boundEnv Kleisli.value (β := .nil) PUnit.unit) :=
  Tagged.outcomes_injective (p.packedOutcomes_eq H L)

/-- Every concrete point of the retained product comes from an assignment. -/
theorem replyInput_surjective (n : Nat) : Function.Surjective (replyInput n) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseReplyAgreement.replyInput_surjective n

/-- The actual packed arrow at any retained assignment has the witnessed
outcomes at that assignment. The selected tree and arrow are independent of
the assignment. -/
theorem ReadTree.packedOutcomes_at_assignment {L : List (Ty Empty)} {n : Nat} (p : ReadTree L n)
    (env : Reply.Payload.Finite.Assignment n) :
    letI := Kleisli.instructions model
    let := modelCoherent
    ((denoteArrow J M (fun _ _ => ⟨rfl, rfl⟩) (packArrow p.selected.elaborate.property)).of (replyInput n env)).outcomes =
      p.witnessed.normal.outcomes env :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseReplyAgreement.readTree_packed_assignment p env

/-- The selected fold and the actual witnessed finite tree have equal
packed observations. A retained-bit test selects its next request and keeps
the untested replies in scope. Returns can compute expressions or quoted
finite tables over the live replies. -/
theorem ReadTree.packedOutcomes_eq (H : Ty Empty) (L : List (Ty Empty)) (p : ReadTree (H :: L) 0) :
    letI := Kleisli.instructions model
    let := modelCoherent
    ((denoteArrow J M (fun _ _ => ⟨rfl, rfl⟩) (packArrow p.selected.elaborate.property)).of PUnit.unit).outcomes =
      Reply.Payload.Finite.programOutcomes H L p.witnessed :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseReplyAgreement.readTree_packed_outcomes H L p

/-- In the validated separator model the packed intrinsic computation
equals evaluation of the same finite witnessed LetCase tree. -/
theorem ReadTree.denote_agrees (H : Ty Empty) (L : List (Ty Empty)) (p : ReadTree (H :: L) 0) :
    letI := Kleisli.instructions model
    let := modelCoherent
    (denoteArrow J M (fun _ _ => ⟨rfl, rfl⟩) (packArrow p.selected.elaborate.property)).of PUnit.unit =
      Kleisli.run model (Reply.Payload.Finite.program H L p.witnessed).toLetCase.2
        (boundEnv Kleisli.value (β := .nil) PUnit.unit) :=
  Tagged.outcomes_injective (p.packedOutcomes_eq H L)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.ReplyAgreement
