module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.Gap.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.ProjectionQuote.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms

/-! # The selected comparison is strictly weaker than native packed equality -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedGuardComparisonGap

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open CaseTree.ReplyAgreement.NativeReplay (case_congr)
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Paper.WithCaseBind.OpenReplay
open Paper.WithCaseBind.OpenReplay.ComparisonGap
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

private abbrev leftInitial := fun i => retainSlot (A := unit) (ReplyFrame.standardSlots 2 i).term
private abbrev rightInitial := fun i => retainSlot (A := unit) (quoteSlots i).term
private abbrev leftScope := bindReply leftInitial
private abbrev rightScope := bindReply rightInitial
private abbrev leftSurvivors := guardReplies leftScope (2 : Fin 3)
private abbrev rightSurvivors := guardReplies rightScope (1 : Fin 4)

private theorem terminal_eq :
    selectedEq (selectTerminal secondExit (.read 2) leftSurvivors [true, false])
      (selectTerminal secondExit (Finite.Expr.quote 4 (fun row => row 2)) rightSurvivors [true, false]) := by
  have drop (i : Fin 3) := retainSlot_discards (A := unit) (quoteSlots i).term (frameSlot_discards (quoteSlots i))
  exact (projection_quote 2 secondExit rightSurvivors [true, false]
    (fun j _ => guardReplies_discards rightScope (bindReply_discards rightInitial drop) 1 j)).symm

private theorem stay {X : Ty Empty} (p : CaseTree signature.Instr X Exits) : selectedEq p p :=
  .refl p.elaborate.property.hasType

set_option backward.isDefEq.respectTransparency false in
theorem source_eq : selectedEq direct.source quoted.source := by
  apply case_congr
  · apply case_congr
    · apply case_congr
      · exact case_congr _ (stay _) terminal_eq
      · exact case_congr _ (stay _) (stay _)
    · exact stay _
  · exact stay _

theorem packed_eq : direct.packedSource = quoted.packedSource :=
  (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
    (source_eq.lsubstPost direct.source.elaborate.property quoted.source.elaborate.property
      (fun _ _ hi => (packExits_valueFamily _ Exits hi).hasType))

private def caseCount : Region signature.Instr → Nat
  | .br .. => 0
  | .case _ l r => 1 + caseCount l + caseCount r
  | .let₁ _ r | .let₂ _ r => caseCount r
  | .cfg entry _ _ => caseCount entry

theorem normalized_ne : direct.normalized ≠ quoted.normalized :=
  fun h => (Nat.ne_of_lt (by decide : caseCount direct.normalized.val < caseCount quoted.normalized.val))
    (congrArg (fun r => caseCount r.val) h)

theorem readbacks_ne :
    (AcyclicSyntax.read direct.normalized.val).map Subtype.val ≠
      (AcyclicSyntax.read quoted.normalized.val).map Subtype.val := by
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp direct.normalized_readable
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp quoted.normalized_readable
  intro eq
  simp only [hl, hr, Option.map_some, Option.some.injEq] at eq
  exact normalized_ne (Subtype.ext (AcyclicSyntax.read_eq_region l r eq))

theorem compare_unknown : direct.compare quoted = .unknown := by
  cases result : direct.compare quoted with
  | unknown => rfl
  | equal _ =>
    exact False.elim (normalized_ne ((direct.compare_accepted_iff quoted).1 (by rw [result]; rfl)))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedGuardComparisonGap
