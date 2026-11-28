module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.OrderedTables.RequestOperands.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms

/-! # Native replay of the sequenced unit operand -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedRequestOperands

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.OpenReplay
open OrderedTables OrderedTables.RequestOperands
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local notation "E" => Paper.Extension.Eqv Seed

private def choiceAt {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    (choice : Choice frame) (v : ReplyFrame.Value Γ frame) : Bool × ReplyFrame.UnitValue Γ :=
  match choice with
  | .read slot => slot.read v
  | .literal b => (b, ⟨.unit, .unit⟩)

private theorem choice_returns_at {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    (choice : Choice frame) (v : ReplyFrame.Value Γ frame) :
    E Γ (Paper.RetainedLet.returnOnce (choice.elaborate.val.subst (Tm.singleSubst v.elaborate.val)))
      (.br 0 (replyBitTag (choiceAt choice v).1 (choiceAt choice v).2.val)) [Bit] := by
  cases choice with
  | read slot => exact frameSlot_returns_at slot v
  | literal b =>
    cases b
    · exact .paper (.cfgEta (.native (.letValue (.inl .unit) (.br rfl (.var (i := 0) rfl)))))
    · exact .paper (.cfgEta (.native (.letValue (.inr .unit) (.br rfl (.var (i := 0) rfl)))))

private theorem resolved_tag {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    (choice : Choice frame) (v : ReplyFrame.Value Γ frame) (known : CompactTerminal.Known frame) (b : Bool)
    (valid : FactsHold known v) (found : choice.resolve? known = some b) :
    (choiceAt choice v).1 = b := by
  cases choice with
  | read slot => exact valid slot b found
  | literal value => exact Option.some.inj found

private theorem packet_subst {Γ : List (Ty Empty)} {X : Ty Empty} {a : Tm signature.Instr}
    (ha : Tm.BranchValue Γ a X) :
    ∀ ⦃i D⦄, At [X] i D → Tm.BranchValue Γ (Tm.singleSubst a i) D := by
  intro i D hi
  cases i with
  | zero => cases Option.some.inj hi; exact ha
  | succ i => simp [At] at hi

private theorem lifted_packet_subst {Γ : List (Ty Empty)} {X : Ty Empty} {a : Tm signature.Instr}
    (ha : Tm.BranchValue Γ a X) :
    ∀ ⦃i D⦄, At [unit, X] i D → Tm.BranchValue (unit :: Γ) (Tm.liftSubst (Tm.singleSubst a) i) D := by
  intro i D hi
  cases i with
  | zero => cases Option.some.inj hi; exact .var (i := 0) rfl
  | succ i => exact rename_branch (Ren.wk Γ unit) (packet_subst ha hi)

private theorem unused_payload {r : Region signature.Instr} {a u : Tm signature.Instr} :
    (((r.renameVars Nat.succ).substVars (Tm.liftSubst (Tm.singleSubst a))).substVars (Tm.singleSubst u)) =
      r.substVars (Tm.singleSubst a) := by
  rw [substVars_renameVars, substVars_comp]
  apply congrArg r.substVars
  funext i
  change (((Tm.singleSubst a) i).rename Nat.succ).subst (Tm.singleSubst u) = (Tm.singleSubst a) i
  rw [Tm.subst_rename, show Tm.singleSubst u ∘ Nat.succ = Tm.var from rfl, Tm.subst_var]

set_option backward.isDefEq.respectTransparency false in
theorem source_at {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)}
    (p : UnitRequest X L) (choice : Choice frame) (known : CompactTerminal.Known frame) (b : Bool)
    (v : ReplyFrame.Value Γ frame) (valid : FactsHold known v) (found : choice.resolve? known = some b) :
    E Γ ((p.source choice).val.substVars (Tm.singleSubst v.elaborate.val))
      ((p.quote b).val.substVars (Tm.singleSubst v.elaborate.val)) L := by
  let observed := choiceAt choice v
  let low := (p.quote false).property.renameVars (Ren.wk [X] unit)
  let high := (p.quote true).property.renameVars (Ren.wk [X] unit)
  have select := case_choose_bit observed.1 (choice.elaborate.property.subst
      (fun _ _ hi => (packet_subst v.elaborate.property hi).hasType))
    observed.2.property (low.substVars (lifted_packet_subst v.elaborate.property))
    (high.substVars (lifted_packet_subst v.elaborate.property)) (choice_returns_at choice v)
  have tag : observed.1 = b := resolved_tag choice v known b valid found
  rw [tag] at select
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at select
    rw [unused_payload] at select
    exact select
  · simp only [↓reduceIte] at select
    rw [unused_payload] at select
    exact select

set_option backward.isDefEq.respectTransparency false in
theorem guarded_replay {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)}
    (p : Guarded frame L) (tags : Bool × Bool) (found : p.tags? = some tags) :
    E [X] p.source.val (p.quote tags).val L := by
  simp only [Guarded.tags?, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
  obtain ⟨l, hl, r, hr, rfl⟩ := found
  apply frame_case_ext frame p.source.property.hasType (p.quote (l, r)).property.hasType
  intro Γ v
  let guardPayload := ReplyFrame.Value.unit v (p.guard.read v).2
  have empty : FactsHold (fun _ => none) v := by intro _ _ impossible; cases impossible
  have arm (chosenTag label : Bool) (plan : UnitRequest (product (product X unit) Bit) L)
      (arg : Choice (.bit (.unit frame))) (residual : Bool)
      (exactTag : (p.guard.read v).1 = chosenTag)
      (resolved : arg.resolve? (p.branchFacts chosenTag) = some residual) :
      E Γ ((firstRequest label (plan.source arg)).val.substVars (Tm.singleSubst guardPayload.elaborate.val))
        ((firstRequest label (plan.quote residual)).val.substVars (Tm.singleSubst guardPayload.elaborate.val)) L := by
    have later (reply : Bool) :=
      source_at plan arg (p.branchFacts chosenTag) residual (extendReply guardPayload reply)
        (guardFacts_hold empty p.guard chosenTag reply exactTag) resolved
    exact request_regions_at [] label guardPayload
      (plan.source arg).property (plan.source arg).property (plan.quote residual).property (plan.quote residual).property
      later later
  have source := framed_case_at p.guard p.emits v
    (firstRequest p.firstLabel (p.onFalse.source p.falseChoice)).property
    (firstRequest (!p.firstLabel) (p.onTrue.source p.trueChoice)).property
  have target := framed_case_at p.guard p.emits v
    (firstRequest p.firstLabel (p.onFalse.quote l)).property
    (firstRequest (!p.firstLabel) (p.onTrue.quote r)).property
  refine source.trans ((prependEmits_congr p.emits ?_).trans target.symm)
  cases chosen : (p.guard.read v).1
  · exact arm false p.firstLabel p.onFalse p.falseChoice l chosen hl
  · exact arm true (!p.firstLabel) p.onTrue p.trueChoice r chosen hr

theorem packed_eq_of_recovered {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)}
    (p : Guarded frame L) (q : ScopedTarget X L) (found : p.recover? = some q) :
    p.source.packed = q.packed := by
  simp only [Guarded.recover?, Option.map_eq_some_iff] at found
  obtain ⟨tags, ht, rfl⟩ := found
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
    ((guarded_replay p tags ht).lsubstPost p.source.property (p.quote tags).property
      (fun _ _ hi => (packExits_valueFamily _ L hi).hasType))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedRequestOperands
