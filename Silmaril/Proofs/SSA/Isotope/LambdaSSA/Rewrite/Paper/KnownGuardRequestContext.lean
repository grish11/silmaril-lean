module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms

/-! # Native alignment of certified request contexts -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.KnownGuardRequestContext

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.OpenReplay

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local notation "E" => Paper.Extension.Eqv Seed

private theorem weakenBranchValue {Γ : List (Ty Empty)} {A X : Ty Empty} {a : Tm signature.Instr}
    (h : Tm.BranchValue Γ a X) : Tm.BranchValue (A :: Γ) (a.rename Nat.succ) X := by
  rw [Tm.rename_eq_subst]
  exact h.subst (fun _ _ hi => .var (Ren.wk Γ A hi))

theorem context_typed {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} {known : Term signature.Instr X Bit}
    (c : KnownGuardContext L slots known) (payload : Term signature.Instr X unit) (b : Bool) :
    ValueBranches [X] (c.pruned payload b) L := by
  induction c with
  | @keep _ _ slots _ tree => exact (tree.selectedWith slots).elaborate.property
  | @prune _ _ slots _ test guard _ =>
    exact prependEmits_typed guard.emits
      (.let₁ payload.elaborate.property (applyPacked_typed_exits (guard.live test slots b).elaborate.property))
  | @request Y _ _ _ emits label left right ihl ihr =>
    let carried := Term.seq (.fst Y Bit) payload
    exact .case (emitPrefix emits (.call (show signature.Instr from Op.ask label) .unit)).elaborate.property
      (applyPacked_typed_exits (ihl carried)) (applyPacked_typed_exits (ihr carried))

theorem split_typed {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} (p : KnownGuardSplit L slots) :
    ValueBranches [X] p.pruned L :=
  .case (emitPrefix p.emits (slots p.test)).elaborate.property
    (applyPacked_typed_exits (context_typed p.onFalse (.snd X unit) false))
    (applyPacked_typed_exits (context_typed p.onTrue (.snd X unit) true))

set_option backward.isDefEq.respectTransparency false in
theorem context_at {Γ L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} {known : Term signature.Instr X Bit}
    (c : KnownGuardContext L slots known) (payload : Term signature.Instr X unit) (b : Bool)
    {packet u : Tm signature.Instr} (hp : Tm.BranchValue Γ packet X) (hu : Tm.BranchValue Γ u unit)
    (knownTag : ReturnsAt (Γ := Γ) known packet (if b then .inr u else .inl u))
    (knownUnit : ReturnsAt (Γ := Γ) payload packet u) :
    E Γ ((c.tree.selectedWith slots).elaborate.val.substVars (Tm.singleSubst packet))
      ((c.pruned payload b).substVars (Tm.singleSubst packet)) L := by
  induction c generalizing Γ packet u with
  | @keep _ _ slots _ tree =>
    apply Paper.Extension.Eqv.refl
    exact ((tree.selectedWith slots).elaborate.property.substVars (θ := Tm.singleSubst packet) (by
      intro i A hi
      cases i with
      | zero => cases Option.some.inj hi; exact hp
      | succ i => simp [At] at hi)).hasType
  | @prune _ _ slots _ test guard survives =>
    have knownTest : ReturnsAt (Γ := Γ) (slots test) packet (if b then .inr u else .inl u) := by
      rw [survives]
      exact knownTag
    have eq := framed_prune_at (slots test) payload guard.emits hp hu b knownTest knownUnit
      (guard.live test slots false).elaborate.property (guard.live test slots true).elaborate.property
    cases b
    · exact eq
    · exact eq
  | @request Y _ slots known emits label left right ihl ihr =>
    let carried := Term.seq (.fst Y Bit) payload
    have hp' : Tm.BranchValue (Bit :: Γ) (.pair (packet.rename Nat.succ) (.var 0)) (product Y Bit) :=
      .pair (weakenBranchValue hp) (.var (i := 0) rfl)
    have hu' : Tm.BranchValue (Bit :: Γ) (u.rename Nat.succ) unit := weakenBranchValue hu
    have tag' := retain_return_under_binder (A := Bit) known hp knownTag
    have renameTag : (if b then Tm.inr u else .inl u).rename Nat.succ =
        (if b then .inr (u.rename Nat.succ) else .inl (u.rename Nat.succ)) := by cases b <;> rfl
    rw [renameTag] at tag'
    have unit' := retain_return_under_binder (A := Bit) payload hp knownUnit
    exact packed_case_congr_at (emitPrefix emits (.call (show signature.Instr from Op.ask label) .unit)) hp
      (left.tree.selectedWith (bindReply slots)).elaborate.property
      (right.tree.selectedWith (bindReply slots)).elaborate.property
      (context_typed left carried b) (context_typed right carried b)
      (ihl carried hp' hu' tag' unit') (ihr carried hp' hu' tag' unit')

set_option backward.isDefEq.respectTransparency false in
theorem eq_pruned {L : List (Ty Empty)} {X : Ty Empty} {n : Nat} {frame : ReplyFrame X}
    (slots : Fin n → ReplyFrame.Slot frame) (p : KnownGuardSplit L (fun j => (slots j).term)) :
    E [X] p.source.elaborate.val p.pruned L := by
  let slot := slots p.test
  let retained := fun j => retainSlot (A := unit) (slots j).term
  let payload := Term.snd (Φ := signature.Instr) X unit
  apply frame_case_ext frame p.source.elaborate.property.hasType (split_typed p).hasType
  intro Γ v
  let u := (slot.read v).2
  have packet := Tm.BranchValue.pair v.elaborate.property u.property
  have facts := prior_guard_returns slot v
  have source := framed_case_at slot p.emits v (p.onFalse.tree.selectedWith retained).elaborate.property
    (p.onTrue.tree.selectedWith retained).elaborate.property
  have target := framed_case_at slot p.emits v (context_typed p.onFalse payload false)
    (context_typed p.onTrue payload true)
  refine source.trans ((prependEmits_congr p.emits ?_).trans target.symm)
  cases h : (slot.read v).1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have tag := facts.1
    rw [h] at tag
    exact context_at p.onFalse payload false packet u.property tag facts.2
  · simp only [↓reduceIte]
    have tag := facts.1
    rw [h] at tag
    exact context_at p.onTrue payload true packet u.property tag facts.2

theorem packed_eq_pruned {L : List (Ty Empty)} {n : Nat} (p : KnownGuardSplit L (readReply n)) :
    p.packedSource = Paper.Extension.Singleton.ofRegion Seed (split_typed p).packExits := by
  have atStandard : ∀ q : KnownGuardSplit L (readReply n), E [replyContext n] q.source.elaborate.val q.pruned L := by
    rw [← standardSlots_term n]
    exact eq_pruned (ReplyFrame.standardSlots n)
  have native := atStandard p
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
    (native.lsubstPost p.source.elaborate.property (split_typed p)
      (fun _ _ hi => (packExits_valueFamily _ L hi).hasType))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.KnownGuardRequestContext
