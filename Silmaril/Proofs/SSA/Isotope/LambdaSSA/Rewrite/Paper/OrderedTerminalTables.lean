module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.OrderedTables.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Frames.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Packed.ReplyAgreement.NativeReplay.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.RedundantTest.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.PacketCases.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Thms

/-! # Native recovery of ordered truth-table quotations -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedTerminalTables

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region CategoryTheory
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open CaseTree.ReplyAgreement.NativeReplay (case_congr)
open Paper.WithCaseBind.OpenReplay
open OrderedTables
open Paper.WithCaseBind.SelectedTerminal (Seed)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

local notation "E" => Paper.Extension.Eqv Seed

private theorem renameFrame_elaborate {Γ Δ : List (Ty Empty)} {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ)
    {X : Ty Empty} {frame : ReplyFrame X} (v : ReplyFrame.Value Γ frame) :
    (renameFrame hρ v).elaborate.val = v.elaborate.val.rename ρ := by
  induction v with
  | base => rfl
  | unit v u ih => simp [renameFrame, ReplyFrame.Value.elaborate, Tm.rename, ih]
  | bit v b u ih => cases b <;> simp [renameFrame, ReplyFrame.Value.elaborate, Tm.rename, ih]

private theorem read_renameFrame {Γ Δ : List (Ty Empty)} {ρ : Nat → Nat} (hρ : Ren Γ Δ ρ)
    {X : Ty Empty} {frame : ReplyFrame X} (slot : ReplyFrame.Slot frame) (v : ReplyFrame.Value Γ frame) :
    (slot.read (renameFrame hρ v)).1 = (slot.read v).1 := by
  induction slot with
  | newest => cases v; rfl
  | retainUnit _ ih => cases v; exact ih _
  | retainBit _ ih => cases v; exact ih _

private theorem replyFacts_hold {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    {v : ReplyFrame.Value Γ frame} {known : CompactTerminal.Known frame} (valid : FactsHold known v)
    (b : Bool) : FactsHold (replyFacts known) (extendReply v b) := by
  intro slot tag found
  cases slot with
  | newest => cases found
  | retainBit old =>
    change (old.read (renameFrame ((Ren.wk Γ Bit).comp (Ren.wk (Bit :: Γ) unit)) v)).1 = tag
    rw [read_renameFrame]
    exact valid old tag found

theorem guardFacts_hold {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    {v : ReplyFrame.Value Γ frame} {known : CompactTerminal.Known frame} (valid : FactsHold known v)
    (slot : ReplyFrame.Slot frame) (tag reply : Bool) (chosen : (slot.read v).1 = tag) :
    FactsHold (guardFacts known slot tag) (extendReply (.unit v (slot.read v).2) reply) := by
  apply replyFacts_hold
  intro query bit seen
  cases query with
  | retainUnit old =>
    change CompactTerminal.remember known slot tag old = some bit at seen
    change (old.read v).1 = bit
    by_cases same : old = slot
    · subst old
      simp [CompactTerminal.remember] at seen
      exact chosen.trans seen
    · apply valid old bit
      simpa [CompactTerminal.remember, same] using seen

private theorem single_values {Γ : List (Ty Empty)} {X : Ty Empty} {a : Tm signature.Instr}
    (ha : Tm.BranchValue Γ a X) :
    ∀ ⦃i D⦄, At [X] i D → Tm.BranchValue Γ (Tm.singleSubst a i) D := by
  intro i D hi
  cases i with
  | zero => cases Option.some.inj hi; exact ha
  | succ i => simp [At] at hi

private abbrev atFrame {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X} {L : List (Ty Empty)}
    (p : CaseTree signature.Instr X L) (v : ReplyFrame.Value Γ frame) : Region signature.Instr :=
  p.elaborate.val.substVars (Tm.singleSubst v.elaborate.val)

private theorem opened_reply {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    {L : List (Ty Empty)} {r : Region signature.Instr} (hr : ValueBranches [product X Bit] r L)
    (v : ReplyFrame.Value Γ frame) (b : Bool) :
    ((r.substVars (Tm.singleSubst (.pair (v.elaborate.val.rename Nat.succ) (.var 0)))).substVars
      (bitBranch 0 b)) = r.substVars (Tm.singleSubst (extendReply v b).elaborate.val) := by
  rw [substVars_comp]
  apply Paper.SingletonReification.SingleCfg.singleton_subst hr.hasType
  have shifted : (v.elaborate.val.rename Nat.succ).subst (bitBranch 0 b) =
      v.elaborate.val.rename (Nat.succ ∘ Nat.succ) := by
    rw [Tm.subst_rename, Tm.rename_eq_subst]
    rfl
  cases b <;> simp [Tm.singleSubst, Tm.consSubst, Tm.subst, extendReply, ReplyFrame.Value.elaborate,
    shifted, bitBranch, replyBitTag] <;>
    exact (renameFrame_elaborate ((Ren.wk Γ Bit).comp (Ren.wk (Bit :: Γ) unit)) v).symm

theorem request_regions_at {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    {L : List (Ty Empty)} (emits : List Bool) (label : Bool) (v : ReplyFrame.Value Γ frame)
    {l r l' r' : Region signature.Instr}
    (hl : ValueBranches [product X Bit] l L) (hr : ValueBranches [product X Bit] r L)
    (hl' : ValueBranches [product X Bit] l' L) (hr' : ValueBranches [product X Bit] r' L)
    (left : ∀ b, E (unit :: Bit :: Γ) (l.substVars (Tm.singleSubst (extendReply v b).elaborate.val))
      (l'.substVars (Tm.singleSubst (extendReply v b).elaborate.val)) L)
    (right : ∀ b, E (unit :: Bit :: Γ) (r.substVars (Tm.singleSubst (extendReply v b).elaborate.val))
      (r'.substVars (Tm.singleSubst (extendReply v b).elaborate.val)) L) :
    E Γ ((KnownGuardTraversal.requestRegion (KnownGuardTraversal.requestTerm (X := X) emits label) l r).substVars
        (Tm.singleSubst v.elaborate.val))
      ((KnownGuardTraversal.requestRegion (KnownGuardTraversal.requestTerm (X := X) emits label) l' r').substVars
        (Tm.singleSubst v.elaborate.val)) L := by
  have arm {p q : Region signature.Instr}
      (hp : ValueBranches [product X Bit] p L) (hq : ValueBranches [product X Bit] q L)
      (rows : ∀ b, E (unit :: Bit :: Γ) (p.substVars (Tm.singleSubst (extendReply v b).elaborate.val))
        (q.substVars (Tm.singleSubst (extendReply v b).elaborate.val)) L) :
      E (Bit :: Γ) (p.substVars (Tm.singleSubst (.pair (v.elaborate.val.rename Nat.succ) (.var 0))))
        (q.substVars (Tm.singleSubst (.pair (v.elaborate.val.rename Nat.succ) (.var 0)))) L := by
    have packet : Tm.BranchValue (Bit :: Γ) (.pair (v.elaborate.val.rename Nat.succ) (.var 0)) (product X Bit) :=
      .pair (rename_branch (Ren.wk Γ Bit) v.elaborate.property) (.var rfl)
    apply bit_case_ext (i := 0) rfl (hp.substVars (single_values packet)).hasType
      (hq.substVars (single_values packet)).hasType
    intro b
    rw [opened_reply hp v b, opened_reply hq v b]
    exact rows b
  exact packed_case_congr_at (KnownGuardTraversal.requestTerm (X := X) emits label) v.elaborate.property
    hl hr hl' hr' (arm hl hl' left) (arm hr hr' right)

private theorem request_at {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    {L : List (Ty Empty)} (emits : List Bool) (label : Bool) (v : ReplyFrame.Value Γ frame)
    {l r l' r' : CaseTree signature.Instr (product X Bit) L}
    (left : ∀ b, E (unit :: Bit :: Γ) (atFrame l (extendReply v b)) (atFrame l' (extendReply v b)) L)
    (right : ∀ b, E (unit :: Bit :: Γ) (atFrame r (extendReply v b)) (atFrame r' (extendReply v b)) L) :
    E Γ (atFrame (selectRequest emits label l r) v) (atFrame (selectRequest emits label l' r') v) L :=
  request_regions_at emits label v l.elaborate.property r.elaborate.property l'.elaborate.property
    r'.elaborate.property left right

private theorem guard_at {Γ : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X}
    {L : List (Ty Empty)} (slot : ReplyFrame.Slot frame) (emits : List Bool) (v : ReplyFrame.Value Γ frame)
    {l r l' r' : CaseTree signature.Instr (product X unit) L}
    (left : (slot.read v).1 = false → E Γ (atFrame l (.unit v (slot.read v).2))
      (atFrame l' (.unit v (slot.read v).2)) L)
    (right : (slot.read v).1 = true → E Γ (atFrame r (.unit v (slot.read v).2))
      (atFrame r' (.unit v (slot.read v).2)) L) :
    E Γ (atFrame (.case unit unit (emitPrefix emits slot.term) l r) v)
      (atFrame (.case unit unit (emitPrefix emits slot.term) l' r') v) L := by
  have source := framed_case_at slot emits v l.elaborate.property r.elaborate.property
  have target := framed_case_at slot emits v l'.elaborate.property r'.elaborate.property
  refine source.trans ((prependEmits_congr emits ?_).trans target.symm)
  cases chosen : (slot.read v).1
  · exact left chosen
  · exact right chosen

theorem frame_eq {X : Ty Empty} (frame other : ReplyFrame X) : frame = other := by
  induction frame with
  | base => cases other; rfl
  | unit frame ih => cases other; congr 1; exact ih _
  | bit frame ih => cases other; congr 1; exact ih _

theorem bindSlots_injective {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (slots : Fin n → ReplyFrame.Slot frame) (distinct : Function.Injective slots) :
    Function.Injective (ReplyFrame.bindSlots slots) := by
  intro i j eq
  cases i using Fin.cases <;> cases j using Fin.cases
  · rfl
  · cases eq
  · cases eq
  · exact congrArg Fin.succ (distinct (ReplyFrame.Slot.retainBit.inj eq))

theorem guardSlots_injective {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (slots : Fin (n + 1) → ReplyFrame.Slot frame) (distinct : Function.Injective slots) (test : Fin (n + 1)) :
    Function.Injective (ReplyFrame.guardSlots slots test) :=
  bindSlots_injective _ (fun _ _ eq =>
    Fin.succAbove_right_injective (distinct (ReplyFrame.Slot.retainUnit.inj eq)))

theorem standardSlots_injective : ∀ n, Function.Injective (ReplyFrame.standardSlots n)
  | 0 => fun i => i.elim0
  | n + 1 => bindSlots_injective _ (standardSlots_injective n)

private theorem locate_eq {X : Ty Empty} {frame : ReplyFrame X} {n : Nat}
    (kept : Fin n → ReplyFrame.Slot frame) (slot : ReplyFrame.Slot frame) (i : Fin n)
    (found : locate kept slot = some i) : kept i = slot := by
  unfold locate at found
  have hit := List.find?_some found
  let := ReplyFrame.Slot.decEq frame
  exact of_decide_eq_true hit

private theorem readWithFacts_rows {X : Ty Empty} {frame : ReplyFrame X} {Γ : List (Ty Empty)} {n : Nat}
    (slot : ReplyFrame.Slot frame) (kept : Fin n → ReplyFrame.Slot frame)
    (known : CompactTerminal.Known frame) (table : Finite.Table n)
    (found : readWithFacts? kept known slot = some table) (v : ReplyFrame.Value Γ frame)
    (valid : FactsHold known v) :
    (slot.read v).1 = table (fun j => ((kept j).read v).1) := by
  cases tag : known slot with
  | none =>
    simp only [readWithFacts?, tag, Option.map_eq_some_iff] at found
    obtain ⟨j, located, rfl⟩ := found
    exact congrArg (fun s : ReplyFrame.Slot frame => (s.read v).1) (locate_eq kept slot j located).symm
  | some tagValue =>
    simp only [readWithFacts?, tag, Option.some.injEq] at found
    subst table
    exact valid slot tagValue tag

theorem reindexWithFacts_sound {X : Ty Empty} {frame : ReplyFrame X} {Γ : List (Ty Empty)} {n m : Nat}
    (e : Finite.Expr m) (slots : Fin m → ReplyFrame.Slot frame)
    (kept : Fin n → ReplyFrame.Slot frame) (known : CompactTerminal.Known frame) (table : Finite.Table n)
    (found : reindexWithFacts? kept known e slots = some table) (v : ReplyFrame.Value Γ frame)
    (valid : FactsHold known v) :
    e.eval (fun j => ((slots j).read v).1) = table (fun j => ((kept j).read v).1) := by
  induction e generalizing table with
  | literal bit =>
    simp only [reindexWithFacts?, Option.some.injEq] at found
    subst table
    rfl
  | read i =>
    exact readWithFacts_rows (slots i) kept known table found v valid
  | split low high hl hr =>
    cases knownTag : known (slots 0) with
    | some tag =>
      have actual := valid (slots 0) tag knownTag
      cases tag
      · simp only [reindexWithFacts?, knownTag] at found
        simpa [Finite.Expr.eval, actual] using! hl _ _ found
      · simp only [reindexWithFacts?, knownTag] at found
        simpa [Finite.Expr.eval, actual] using! hr _ _ found
    | none =>
      by_cases redundant : low = high
      · have reduced : reindexWithFacts? kept known low (fun j => slots j.succ) = some table := by
          simpa only [reindexWithFacts?, knownTag, redundant, ↓reduceIte] using found
        rw [← redundant]
        simpa [Finite.Expr.eval] using! hl _ _ reduced
      · simp only [reindexWithFacts?, knownTag, redundant, ↓reduceIte, bind,
          Option.bind_eq_some_iff, pure, Option.some.injEq] at found
        obtain ⟨j, located, l, left, r, right, rfl⟩ := found
        have same := congrArg (fun slot : ReplyFrame.Slot frame => (slot.read v).1)
          (locate_eq kept (slots 0) j located)
        simp only [Finite.Expr.eval, ← same]
        split
        · exact hr _ _ right
        · exact hl _ _ left

private theorem render_emits {L : List (Ty Empty)} {n : Nat} (emits before : List Bool)
    (p : Finite.Normal L n) :
    renderWith (emits.foldr Finite.Normal.emit p) before = renderWith p (before ++ emits) := by
  induction emits generalizing before with
  | nil => simp
  | cons b bs ih => simp [renderWith, ih, List.append_assoc]

theorem render_normal {L : List (Ty Empty)} {n : Nat} (p : Finite.Normal L n) (emits : List Bool) :
    (renderWith p emits).witnessed.normal = emits.foldr Finite.Normal.emit p := by
  induction p generalizing emits with
  | ret pos table =>
    simp only [renderWith, ReadTree.witnessed]
    induction emits with
    | nil =>
      simp only [List.foldr_nil, Finite.Tree.normal]
      congr
      exact funext (Finite.Expr.quote_eval _ _)
    | cons b bs h => simp [Finite.Tree.normal, h]
  | emit bit next ih =>
    simp only [renderWith, ih, List.foldr_append, List.foldr_cons, List.foldr_nil]
  | request label l r hl hr =>
    simp only [renderWith, ReadTree.witnessed]
    induction emits with
    | nil => simp [Finite.Tree.normal, hl, hr]
    | cons b bs h => simp [Finite.Tree.normal, h]
  | testRequest _ _ _ _ _ _ hfl hfr htl htr =>
    simp only [renderWith, ReadTree.witnessed]
    induction emits with
    | nil => simp [Finite.Tree.normal, hfl, hfr, htl, htr]
    | cons b bs h => simp [Finite.Tree.normal, h]

set_option backward.isDefEq.respectTransparency false in
theorem recoverTreeWithFacts_at {L : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X} {n m : Nat}
    (tree : ReadTree L m) (known : CompactTerminal.Known frame) (slots : Fin m → ReplyFrame.Slot frame)
    (kept : Fin n → ReplyFrame.Slot frame) (normal : Finite.Normal L n)
    (found : recoverTreeWithFacts tree known slots kept = some normal)
    {Γ : List (Ty Empty)} (v : ReplyFrame.Value Γ frame) (valid : FactsHold known v) :
    E Γ ((tree.selectedWith (fun j => (slots j).term)).elaborate.val.substVars
        (Tm.singleSubst v.elaborate.val))
      (((renderWith normal []).selectedWith (fun j => (kept j).term)).elaborate.val.substVars
        (Tm.singleSubst v.elaborate.val)) L := by
  induction tree generalizing n X Γ with
  | ret emits pos i =>
    simp only [recoverTreeWithFacts, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
    obtain ⟨table, lookup, rfl⟩ := found
    simp only [render_emits, List.nil_append, renderWith, ReadTree.selectedWith]
    apply CompactTerminal.selected_of_frame_row
    rw [Finite.Expr.quote_eval]
    exact readWithFacts_rows (slots i) kept known table lookup v valid
  | retExpr emits pos e =>
    simp only [recoverTreeWithFacts, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
    obtain ⟨table, recovered, rfl⟩ := found
    simp only [render_emits, List.nil_append, renderWith, ReadTree.selectedWith]
    apply CompactTerminal.selected_of_frame_row
    rw [Finite.Expr.quote_eval]
    exact reindexWithFacts_sound e slots kept known table recovered v valid
  | request emits label bound l r hl hr =>
    simp only [recoverTreeWithFacts, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
    obtain ⟨left, hleft, right, hright, rfl⟩ := found
    have le (b : Bool) := hl _ _ _ _ hleft (extendReply v b) (replyFacts_hold valid b)
    have re (b : Bool) := hr _ _ _ _ hright (extendReply v b) (replyFacts_hold valid b)
    rw [bindSlots_term, bindSlots_term] at le re
    simp only [render_emits, List.nil_append, renderWith, ReadTree.selectedWith]
    exact request_at emits label v le re
  | testRequest emits test low lowBound highBound fl fr tl tr hfl hfr htl htr =>
    cases n with
    | zero => simp [recoverTreeWithFacts] at found
    | succ n =>
      simp only [recoverTreeWithFacts, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at found
      obtain ⟨i, located, fl', h₀, fr', h₁, tl', h₂, tr', h₃, rfl⟩ := found
      let tested := slots test
      let child := ReplyFrame.Value.unit v (tested.read v).2
      have leftFact (chosen : (tested.read v).1 = false) (b : Bool) := guardFacts_hold valid tested false b chosen
      have rightFact (chosen : (tested.read v).1 = true) (b : Bool) := guardFacts_hold valid tested true b chosen
      have flEq chosen b := hfl _ _ _ _ h₀ (extendReply child b) (leftFact chosen b)
      have frEq chosen b := hfr _ _ _ _ h₁ (extendReply child b) (leftFact chosen b)
      have tlEq chosen b := htl _ _ _ _ h₂ (extendReply child b) (rightFact chosen b)
      have trEq chosen b := htr _ _ _ _ h₃ (extendReply child b) (rightFact chosen b)
      rw [guardSlots_term, guardSlots_term] at flEq frEq tlEq trEq
      simp only [render_emits, List.nil_append, renderWith, ReadTree.selectedWith]
      rw [locate_eq kept (slots test) i located]
      exact guard_at tested emits v
        (fun chosen => request_at [] low child (flEq chosen) (frEq chosen))
        (fun chosen => request_at [] (!low) child (tlEq chosen) (trEq chosen))

set_option backward.isDefEq.respectTransparency false in
private theorem recoverSplit_at {L : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X} {n m : Nat}
    (split : SelectedGuardSplit L m) (slots : Fin m → ReplyFrame.Slot frame)
    (kept : Fin (n + 1) → ReplyFrame.Slot frame) (normal : Finite.Normal L (n + 1))
    (found : recoverSplit split slots kept = some normal)
    {Γ : List (Ty Empty)} (v : ReplyFrame.Value Γ frame) :
    E Γ (atFrame (split.sourceWith (fun j => (slots j).term)) v)
      (atFrame ((renderWith normal []).selectedWith (fun j => (kept j).term)) v) L := by
  rcases split with ⟨test, emits, fl, tl⟩
  cases fl <;> cases tl <;> try (solve | simp [recoverSplit, bind] at found)
  rename_i prefixF low boundF fl fr prefixT high boundT tl tr
  cases prefixF <;> cases prefixT <;> try (solve | simp [recoverSplit, bind] at found)
  by_cases labels : high = !low
  · subst high
    simp only [recoverSplit, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, ite_true] at found
    obtain ⟨i, located, fl', h₀, fr', h₁, tl', h₂, tr', h₃, rfl⟩ := found
    let tested := slots test
    let child := ReplyFrame.Value.unit v (tested.read v).2
    have empty : FactsHold (fun _ => none) v := by intro _ _ impossible; cases impossible
    have leftFact (chosen : (tested.read v).1 = false) (b : Bool) := guardFacts_hold empty tested false b chosen
    have rightFact (chosen : (tested.read v).1 = true) (b : Bool) := guardFacts_hold empty tested true b chosen
    have flEq chosen b := recoverTreeWithFacts_at _ _ _ _ _ h₀ (extendReply child b) (leftFact chosen b)
    have frEq chosen b := recoverTreeWithFacts_at _ _ _ _ _ h₁ (extendReply child b) (leftFact chosen b)
    have tlEq chosen b := recoverTreeWithFacts_at _ _ _ _ _ h₂ (extendReply child b) (rightFact chosen b)
    have trEq chosen b := recoverTreeWithFacts_at _ _ _ _ _ h₃ (extendReply child b) (rightFact chosen b)
    rw [bindSlots_term, guardSlots_term] at flEq frEq tlEq trEq
    simp only [render_emits, List.nil_append, renderWith, SelectedGuardSplit.sourceWith, ReadTree.selectedWith]
    rw [locate_eq kept (slots test) i located]
    exact guard_at tested emits v
      (fun chosen => request_at [] low child (flEq chosen) (frEq chosen))
      (fun chosen => request_at [] (!low) child (tlEq chosen) (trEq chosen))
  · simp [recoverSplit, bind, labels] at found

theorem recoverSplit_sound {L : List (Ty Empty)} {X : Ty Empty} {frame : ReplyFrame X} {n m : Nat}
    (split : SelectedGuardSplit L m) (slots : Fin m → ReplyFrame.Slot frame)
    (kept : Fin (n + 1) → ReplyFrame.Slot frame) (normal : Finite.Normal L (n + 1))
    (found : recoverSplit split slots kept = some normal) :
    selectedEq (split.sourceWith (fun j => (slots j).term))
      ((renderWith normal []).selectedWith (fun j => (kept j).term)) :=
  frame_case_ext frame (split.sourceWith (fun j => (slots j).term)).elaborate.property.hasType
    ((renderWith normal []).selectedWith (fun j => (kept j).term)).elaborate.property.hasType
    (fun v => recoverSplit_at split slots kept normal found v)

private theorem reframed_slots_term {X : Ty Empty} {f f' : ReplyFrame X} {m : Nat} (same : f = f')
    (slots : Fin m → ReplyFrame.Slot f) :
    (fun i => ((same ▸ slots : Fin m → ReplyFrame.Slot f') i).term) = fun i => (slots i).term := by
  cases same
  rfl

theorem recovered_packed {L : List (Ty Empty)} {n : Nat} (p : SelectedAt (replyContext (n + 1)) L)
    (frameEq : p.frame = ReplyFrame.standard (n + 1)) (key : Finite.Normal L (n + 1))
    (found : recoverSplit p.split (frameEq ▸ p.slots) (ReplyFrame.standardSlots (n + 1)) = some key) :
    p.packedSource = (OrderedTables.target key).packed := by
  have replay := recoverSplit_sound p.split (frameEq ▸ p.slots) (ReplyFrame.standardSlots (n + 1)) key found
  rw [reframed_slots_term frameEq p.slots, standardSlots_term] at replay
  exact (Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2
    (replay.lsubstPost p.source.elaborate.property (OrderedTables.target key).property
      (fun _ _ hi => (packExits_valueFamily _ L hi).hasType))

theorem observations_eq {L : List (Ty Empty)} {n : Nat} {p : SelectedAt (replyContext n) L}
    (a : OrderedTables.Admission p) (env : Finite.Assignment n) :
    CanonicalLive.observations p env = a.key.outcomes env := by
  have map := CanonicalLive.readTree_map_outcomes (renderWith a.key []) env
  rw [render_normal, List.foldr_nil] at map
  exact (congrArg (fun arrow => ((CanonicalLive.payloadDenote.map arrow).of (replyInput n env)).outcomes)
    a.packed_eq).trans map

theorem key_eq_of_packed_eq {L : List (Ty Empty)} {n : Nat} {p q : SelectedAt (replyContext n) L}
    (l : OrderedTables.Admission p) (r : OrderedTables.Admission q) (eq : p.packedSource = q.packedSource) :
    l.key = r.key := by
  apply Finite.Normal.traceTree_inj
  intro env
  apply Reply.Normal.outcomesWith_injective _ (Reply.Exits.Exit.packed_injective L)
  have same : CanonicalLive.observations p env = CanonicalLive.observations q env := by
    simp only [CanonicalLive.observations, eq]
  exact (observations_eq l env).symm.trans (same.trans (observations_eq r env))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedTerminalTables
