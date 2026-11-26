module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms

/-! # Native rewriting through certified selected guards -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GuardTraversal

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.OpenReplay
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay.KnownGuardTraversal (requestTerm requestRegion retainPayload)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy
local notation "E" => Paper.Extension.Eqv Seed

theorem guardSurvives_iff {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (slots : Fin (n + 1) → ReplyFrame.Slot frame) (known : ReplyFrame.Slot frame) (test : Fin (n + 1)) :
    KnownGuardTraversal.guardSurvives slots known test = true ↔
      ∃ j, ReplyFrame.guardSlots slots test j = .retainBit (.retainUnit known) := by
  have untested : KnownGuardTraversal.guardSurvives slots known test = true ↔
      ∃ i, slots (test.succAbove i) = known := by
    simp [KnownGuardTraversal.guardSurvives, List.any_eq_true]
  rw [untested]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.succ, congrArg (fun s => ReplyFrame.Slot.retainBit (.retainUnit s)) hi⟩
  · rintro ⟨j, hj⟩
    cases j using Fin.cases with
    | zero => cases hj
    | succ i =>
      refine ⟨i, ?_⟩
      change ReplyFrame.Slot.retainBit (.retainUnit (slots (test.succAbove i))) =
        ReplyFrame.Slot.retainBit (.retainUnit known) at hj
      cases hj
      rfl

private theorem request_typed {L : List (Ty Empty)} {X : Ty Empty}
    (a : Term signature.Instr X (coprod Bit Bit)) {l r : Region signature.Instr}
    (hl : ValueBranches [product X Bit] l L) (hr : ValueBranches [product X Bit] r L) :
    ValueBranches [X] (requestRegion a l r) L :=
  .case a.elaborate.property (applyPacked_typed_exits hl) (applyPacked_typed_exits hr)

set_option backward.isDefEq.respectTransparency false in
theorem render_typed {L : List (Ty Empty)} {tag : Bool} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} {known : Term signature.Instr X Bit} {p : ReadTree L n}
    (c : KnownGuardTraversal L tag slots known p) (rewriteKept : ∀ {n}, ReadTree L n → ReadTree L n)
    (payload : Term signature.Instr X unit) :
    ValueBranches [X] (c.renderWith rewriteKept payload) L := by
  induction c with
  | @keep _ _ slots _ p => exact ((rewriteKept p).selectedWith slots).elaborate.property
  | request emits label _ _ _ ihl ihr =>
    exact request_typed (requestTerm emits label) (ihl (retainPayload payload)) (ihr (retainPayload payload))
  | @guard Y _ slots _ _ _ _ _ emits test low _ _ _ _ _ _ ifl ifr itl itr =>
    let carried := retainPayload (A := Bit) (retainPayload (A := unit) payload)
    exact .case (emitPrefix emits (slots test)).elaborate.property
      (applyPacked_typed_exits (request_typed (requestTerm [] low) (ifl carried) (ifr carried)))
      (applyPacked_typed_exits (request_typed (requestTerm [] (!low)) (itl carried) (itr carried)))
  | prune emits _ low _ _ _ _ _ ihl ihr =>
    let carried := retainPayload (A := Bit) (retainPayload (A := unit) payload)
    exact prependEmits_typed emits (.let₁ payload.elaborate.property
      (applyPacked_typed_exits (request_typed (requestTerm [] (if tag then !low else low)) (ihl carried) (ihr carried))))

theorem pruned_typed {L : List (Ty Empty)} {tag : Bool} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} {known : Term signature.Instr X Bit} {p : ReadTree L n}
    (c : KnownGuardTraversal L tag slots known p) (payload : Term signature.Instr X unit) :
    ValueBranches [X] (c.pruned payload) L :=
  render_typed c (fun p => p) payload

private structure KnownAt (Γ : List (Ty Empty)) {X : Ty Empty}
    (known : Term signature.Instr X Bit) (payload : Term signature.Instr X unit)
    (tag : Bool) (packet u : Tm signature.Instr) : Prop where
  packet_typed : Tm.BranchValue Γ packet X
  unit_typed : Tm.BranchValue Γ u unit
  bit_return : ReturnsAt (Γ := Γ) known packet (if tag then .inr u else .inl u)
  unit_return : ReturnsAt (Γ := Γ) payload packet u

private theorem weaken {Γ : List (Ty Empty)} {X A : Ty Empty} {v : Tm signature.Instr}
    (h : Tm.BranchValue Γ v X) : Tm.BranchValue (A :: Γ) (v.rename Nat.succ) X := by
  rw [Tm.rename_eq_subst]
  exact h.subst (fun _ _ hi => .var (Ren.wk Γ A hi))

private theorem KnownAt.retain {Γ : List (Ty Empty)} {X : Ty Empty}
    {known : Term signature.Instr X Bit} {payload : Term signature.Instr X unit}
    {tag : Bool} {packet u : Tm signature.Instr}
    (h : KnownAt Γ known payload tag packet u) (A : Ty Empty) :
    KnownAt (A :: Γ) (retainSlot (A := A) known) (retainPayload (A := A) payload) tag
      (.pair (packet.rename Nat.succ) (.var 0)) (u.rename Nat.succ) := by
  have bit := retain_return_under_binder (A := A) known h.packet_typed h.bit_return
  have renameTag : (if tag then Tm.inr u else .inl u).rename Nat.succ =
      (if tag then .inr (u.rename Nat.succ) else .inl (u.rename Nat.succ)) := by cases tag <;> rfl
  rw [renameTag] at bit
  exact ⟨.pair (weaken h.packet_typed) (.var (i := 0) rfl), weaken h.unit_typed, bit,
    retain_return_under_binder (A := A) payload h.packet_typed h.unit_return⟩

set_option backward.isDefEq.respectTransparency false in
private theorem context_at {Γ L : List (Ty Empty)} {tag : Bool} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} {known : Term signature.Instr X Bit} {p : ReadTree L n}
    (c : KnownGuardTraversal L tag slots known p) {payload : Term signature.Instr X unit}
    {packet u : Tm signature.Instr} (h : KnownAt Γ known payload tag packet u) :
    E Γ ((p.selectedWith slots).elaborate.val.substVars (Tm.singleSubst packet))
      ((c.pruned payload).substVars (Tm.singleSubst packet)) L := by
  induction c generalizing Γ packet u with
  | @keep _ _ slots _ p =>
    apply Paper.Extension.Eqv.refl
    exact ((p.selectedWith slots).elaborate.property.substVars (θ := Tm.singleSubst packet) (by
      intro i T hi
      cases i with
      | zero => cases Option.some.inj hi; exact h.packet_typed
      | succ i => simp [At] at hi)).hasType
  | @request _ _ slots _ l r emits label _ cl cr il ir =>
    let carried := retainPayload (A := Bit) payload
    exact packed_case_congr_at (requestTerm emits label) h.packet_typed
      (l.selectedWith (bindReply slots)).elaborate.property (r.selectedWith (bindReply slots)).elaborate.property
      (pruned_typed cl carried) (pruned_typed cr carried) (il (h.retain Bit)) (ir (h.retain Bit))
  | @guard Y _ slots _ fl fr tl tr emits test low _ _ cfl cfr ctl ctr ifl ifr itl itr =>
    let scope := guardReplies slots test
    let carried := retainPayload (A := Bit) (retainPayload (A := unit) payload)
    let oldLow := (selectRequest [] low (fl.selectedWith scope) (fr.selectedWith scope)).elaborate
    let oldHigh := (selectRequest [] (!low) (tl.selectedWith scope) (tr.selectedWith scope)).elaborate
    let lowTerm := requestTerm (X := product Y unit) [] low
    let highTerm := requestTerm (X := product Y unit) [] (!low)
    let newLow := request_typed lowTerm (pruned_typed cfl carried) (pruned_typed cfr carried)
    let newHigh := request_typed highTerm (pruned_typed ctl carried) (pruned_typed ctr carried)
    have framed := h.retain unit
    have replies := framed.retain Bit
    have lo := packed_case_congr_at lowTerm framed.packet_typed
      (fl.selectedWith scope).elaborate.property (fr.selectedWith scope).elaborate.property
      (pruned_typed cfl carried) (pruned_typed cfr carried) (ifl replies) (ifr replies)
    have hi := packed_case_congr_at highTerm framed.packet_typed
      (tl.selectedWith scope).elaborate.property (tr.selectedWith scope).elaborate.property
      (pruned_typed ctl carried) (pruned_typed ctr carried) (itl replies) (itr replies)
    exact packed_case_congr_at (emitPrefix emits (slots test)) h.packet_typed oldLow.property oldHigh.property
      newLow newHigh lo hi
  | @prune Y _ slots _ fl fr tl tr emits test low _ _ agreement cl cr il ir =>
    let scope := guardReplies slots test
    let carried := retainPayload (A := Bit) (retainPayload (A := unit) payload)
    let oldLow := (selectRequest [] low (fl.selectedWith scope) (fr.selectedWith scope)).elaborate
    let oldHigh := (selectRequest [] (!low) (tl.selectedWith scope) (tr.selectedWith scope)).elaborate
    let l := (if tag then tl else fl).selectedWith scope
    let r := (if tag then tr else fr).selectedWith scope
    let a := requestTerm (X := product Y unit) [] (if tag then !low else low)
    let oldLive := (selectRequest [] (if tag then !low else low) l r).elaborate
    let newLive := request_typed a (pruned_typed cl carried) (pruned_typed cr carried)
    have knownTest := agreement.symm ▸ h.bit_return
    have choose := framed_prune_at (slots test) payload emits h.packet_typed h.unit_typed tag
      knownTest h.unit_return oldLow.property oldHigh.property
    have live : (if tag then oldHigh.val else oldLow.val) = oldLive.val := by cases tag <;> rfl
    rw [live] at choose
    have framed := h.retain unit
    have replies := framed.retain Bit
    have step := packed_case_congr_at a framed.packet_typed l.elaborate.property r.elaborate.property
      (pruned_typed cl carried) (pruned_typed cr carried) (il replies) (ir replies)
    exact choose.trans (packed_let_congr_at emits payload h.packet_typed oldLive.property newLive step)

theorem eq_pruned_at {Γ L : List (Ty Empty)} {tag : Bool} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} {known : Term signature.Instr X Bit} {p : ReadTree L n}
    (c : KnownGuardTraversal L tag slots known p) (payload : Term signature.Instr X unit)
    {packet u : Tm signature.Instr} (hp : Tm.BranchValue Γ packet X) (hu : Tm.BranchValue Γ u unit)
    (bitFact : ReturnsAt (Γ := Γ) known packet (if tag then .inr u else .inl u))
    (unitFact : ReturnsAt (Γ := Γ) payload packet u) :
    E Γ ((p.selectedWith slots).elaborate.val.substVars (Tm.singleSubst packet))
      ((c.pruned payload).substVars (Tm.singleSubst packet)) L :=
  context_at c ⟨hp, hu, bitFact, unitFact⟩

theorem split_typed {L : List (Ty Empty)} {X : Ty Empty} {n : Nat}
    {p : SelectedGuardSplit L n} {terms : Fin n → Term signature.Instr X Bit} (t : GuardSplitTraversal p terms) :
    ValueBranches [X] t.pruned L :=
  .case (emitPrefix p.emits (terms p.test)).elaborate.property
    (applyPacked_typed_exits (pruned_typed t.onFalse (.snd X unit)))
    (applyPacked_typed_exits (pruned_typed t.onTrue (.snd X unit)))

set_option backward.isDefEq.respectTransparency false in
theorem split_eq_pruned {L : List (Ty Empty)} {X : Ty Empty} {n : Nat} {frame : ReplyFrame X}
    (slots : Fin n → ReplyFrame.Slot frame) {terms : Fin n → Term signature.Instr X Bit}
    (mapEq : (fun j => (slots j).term) = terms) {p : SelectedGuardSplit L n} (t : GuardSplitTraversal p terms) :
    E [X] (p.sourceWith terms).elaborate.val t.pruned L := by
  subst terms
  let slot := slots p.test
  let retained := fun j => retainSlot (A := unit) (slots j).term
  let payload := Term.snd (Φ := signature.Instr) X unit
  apply frame_case_ext frame (p.sourceWith (fun j => (slots j).term)).elaborate.property.hasType (split_typed t).hasType
  intro Γ v
  let u := (slot.read v).2
  have packet := Tm.BranchValue.pair v.elaborate.property u.property
  have facts := prior_guard_returns slot v
  have source := framed_case_at slot p.emits v (p.onFalse.selectedWith retained).elaborate.property
    (p.onTrue.selectedWith retained).elaborate.property
  have target := framed_case_at slot p.emits v (pruned_typed t.onFalse payload) (pruned_typed t.onTrue payload)
  refine source.trans ((prependEmits_congr p.emits ?_).trans target.symm)
  cases h : (slot.read v).1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have bit := facts.1
    rw [h] at bit
    exact eq_pruned_at t.onFalse payload packet u.property bit facts.2
  · simp only [↓reduceIte]
    have bit := facts.1
    rw [h] at bit
    exact eq_pruned_at t.onTrue payload packet u.property bit facts.2

theorem split_packed_eq_pruned {L : List (Ty Empty)} {X : Ty Empty} {n : Nat} {frame : ReplyFrame X}
    (slots : Fin n → ReplyFrame.Slot frame) {terms : Fin n → Term signature.Instr X Bit}
    (mapEq : (fun j => (slots j).term) = terms) {p : SelectedGuardSplit L n} (t : GuardSplitTraversal p terms) :
    Paper.Extension.Singleton.ofRegion Seed (p.sourceWith terms).elaborate.property.packExits =
      Paper.Extension.Singleton.ofRegion Seed (split_typed t).packExits :=
  (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
    ((split_eq_pruned slots mapEq t).lsubstPost (p.sourceWith terms).elaborate.property (split_typed t)
      (fun _ _ hi => (packExits_valueFamily _ L hi).hasType))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.GuardTraversal
