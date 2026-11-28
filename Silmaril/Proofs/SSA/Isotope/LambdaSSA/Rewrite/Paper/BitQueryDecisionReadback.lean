module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Replay.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Thms

/-! # Exact scope and contextual replay for checked query decisions -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryDecisionReadback

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithCaseBind.BitQuery Paper.WithCaseBind.BitQuery.RequestTree
open Paper.WithCaseBind.BitQuery.RequestTree.Readback (Decision readDecision CaseOperandBeta CaseOperandBetaIn caseOperand requestDecEq)
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition
  (sameBody_eq)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr)

attribute [local instance] requestDecEq
local notation "U" => (Ty.unit : Ty Empty)

theorem readDecision_eq {n : Nat} {raw : Region signature.Instr} {d : Decision n}
    (h : readDecision n raw = some d) : raw = d.region := by
  unfold readDecision at h
  obtain ⟨⟨label, l, r⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨query, _, h⟩ := Option.bind_eq_some_iff.mp h
  dsimp only at h
  split at h
  · rename_i checked
    cases h
    exact sameBody_eq checked
  · cases h

private theorem case_left {Γ L : List (Ty Empty)} {i : Nat} {l r : Region signature.Instr}
    (hi : At Γ i Bit) (h : ValueBranches Γ (.case (.var i) l r) L) :
    ValueBranches (U :: Γ) l L := by
  cases h with
  | case ha hl hr =>
    cases ha with
    | var ha =>
      cases Option.some.inj (ha.symm.trans hi)
      exact hl

private theorem drop_unit {Γ L : List (Ty Empty)} {r : Region signature.Instr}
    (h : ValueBranches (U :: Γ) (r.renameVars Nat.succ) L) : ValueBranches Γ r L := by
  have drop : ∀ i A, At (U :: Γ) i A → Tm.BranchValue Γ (Tm.singleSubst (.unit : Tm signature.Instr) i) A := by
    intro i A hi
    cases i with
    | zero =>
      cases Option.some.inj hi
      exact .unit
    | succ i => exact .var hi
  simpa only [drop_weakening] using h.substVars drop

private theorem chosen_typed {n : Nat} (query : Expr n) {Γ L : List (Ty Empty)} (idx : Fin n → Nat)
    (slots : ∀ i, At Γ (idx i) Bit) {l r : Region signature.Instr}
    (h : ValueBranches Γ (choose query (fun i => .var (idx i)) l r) L) :
    ValueBranches Γ l L ∨ ValueBranches Γ r L := by
  induction query generalizing Γ l r with
  | literal b =>
    cases b
    · exact .inl h
    · exact .inr h
  | read i => exact .inl (drop_unit (case_left (slots i) h))
  | split low high ih _ =>
    have arm := case_left (slots 0) h
    rcases ih (fun i => (idx i.succ).succ) (fun i => slots i.succ) arm with chosen | chosen
    · exact .inl (drop_unit chosen)
    · exact .inr (drop_unit chosen)

private theorem request_scope {Γ L : List (Ty Empty)} {arg : Tm signature.Instr} {label : Bool}
    {l r : Region signature.Instr}
    (h : ValueBranches Γ (.case (.op (.ask label) arg) l r) L) :
    ValueBranches (Bit :: Γ) l L ∧ ValueBranches (Bit :: Γ) r L := by
  cases h with
  | case ha hl hr =>
    cases ha
    exact ⟨hl, hr⟩


theorem branches_typed {n : Nat} {Γ L : List (Ty Empty)} (d : Decision n)
    (slots : ∀ i : Fin n, At Γ i.val Bit) (hr : ValueBranches Γ d.region L) :
    ValueBranches (Bit :: Γ) d.left L ∧ ValueBranches (Bit :: Γ) d.right L := by
  rcases chosen_typed d.query Fin.val slots hr with h | h
  · exact request_scope h
  · exact request_scope h

private theorem choose_congr {n : Nat} (e : Expr n) {Γ L : List (Ty Empty)} {terms : Fin n → Tm signature.Instr}
    (ht : ∀ i, Tm.HasType Γ (terms i) Bit) {l r l' r' : Region signature.Instr}
    (hl : Paper.Eqv Γ l l' L) (hr : Paper.Eqv Γ r r' L) :
    Paper.Eqv Γ (choose e terms l r) (choose e terms l' r') L := by
  induction e generalizing Γ l r l' r' with
  | literal b => cases b; exact hl; exact hr
  | read i => exact .case (ht i) (hl.renameVars (Ren.wk Γ U)) (hr.renameVars (Ren.wk Γ U))
  | split lo hi il ir =>
    exact .case (ht 0)
      (il (fun j => (ht j.succ).rename (Ren.wk Γ U)) (hl.renameVars (Ren.wk Γ U)) (hr.renameVars (Ren.wk Γ U)))
      (ir (fun j => (ht j.succ).rename (Ren.wk Γ U)) (hl.renameVars (Ren.wk Γ U)) (hr.renameVars (Ren.wk Γ U)))

private theorem choose_rename {n : Nat} (e : Expr n) (terms : Fin n → Tm signature.Instr)
    (l r : Region signature.Instr) (ρ : Nat → Nat) :
    (choose e terms l r).renameLabels ρ =
      choose e terms (l.renameLabels ρ) (r.renameLabels ρ) := by
  induction e generalizing l r with
  | literal b => cases b <;> rfl
  | read i => simp only [choose, renameLabels, renameVars_renameLabels]
  | split lo hi il ir =>
    simp only [choose, renameLabels, il, ir, renameVars_renameLabels]

theorem replay {n : Nat} {Γ L : List (Ty Empty)} (d : Decision n)
    (slots : ∀ i : Fin n, At Γ i.val Bit) {l r : Region signature.Instr} (ρ : Nat → Nat)
    (hl : Paper.Eqv (Bit :: Γ) d.left (l.renameLabels ρ) L)
    (hr : Paper.Eqv (Bit :: Γ) d.right (r.renameLabels ρ) L) :
    Paper.Eqv Γ d.region ((⟨d.label, d.query, l, r⟩ : Decision n).region.renameLabels ρ) L := by
  change Paper.Eqv Γ
    (choose d.query (fun i => .var i) (requestRegion d.label false d.left d.right)
      (requestRegion d.label true d.left d.right))
    ((choose d.query (fun i => .var i) (requestRegion d.label false l r)
      (requestRegion d.label true l r)).renameLabels ρ) L
  rw [choose_rename]
  exact choose_congr d.query (fun i => .var (slots i))
    (.case (.op (constructorBit_value false .unit).hasType) hl hr)
    (.case (.op (constructorBit_value true .unit).hasType) hl hr)

private theorem choose_weak_focus (r : Region signature.Instr) (θ : Nat → Tm signature.Instr) :
    (r.renameVars Nat.succ).substVars (Tm.liftSubst θ) = (r.substVars θ).renameVars Nat.succ := by
  rw [substVars_renameVars, renameVars_substVars]
  rfl

theorem term_case_operand_extension_of
    {Seed : VCtx (Ty Empty) → Region signature.Instr → Region signature.Instr → LCtx (Ty Empty) → Prop}
    (beta : CaseOperandBetaIn (Paper.Extension.Eqv Seed)) {Γ L : List (Ty Empty)} {i : Nat}
    (hi : At Γ i Bit)
    (label : Bool) {l r : Region signature.Instr}
    (hl : ValueBranches (Bit :: Γ) l L) (hr : ValueBranches (Bit :: Γ) r L) :
    Paper.Extension.Eqv Seed Γ (.case (.op (.ask label) (caseOperand (.var i))) l r)
      (.case (.var i) ((requestRegion label false l r).renameVars Nat.succ)
        ((requestRegion label true l r).renameVars Nat.succ)) L := by
  let source := Region.case (.op (.ask label) (caseOperand (.var i))) l r
  let low := requestRegion label false l r
  let high := requestRegion label true l r
  let target := Region.case (.var i) (low.renameVars Nat.succ) (high.renameVars Nat.succ)
  have hsource : ValueBranches Γ source L :=
    .case (.op (.case (.var hi) (constructorBit_value false .unit).hasType
      (constructorBit_value true .unit).hasType)) hl hr
  have hrequest (b : Bool) : ValueBranches Γ (requestRegion label b l r) L :=
    .case (.op (constructorBit_value b .unit).hasType) hl hr
  have ht : ValueBranches Γ target L :=
    .case (.var hi) ((hrequest false).renameVars (Ren.wk Γ U)) ((hrequest true).renameVars (Ren.wk Γ U))
  have arms (b : Bool) : Paper.Extension.Eqv Seed (U :: Γ) (source.substVars (focus i b)) (target.substVars (focus i b)) L := by
    let θ := focus i b
    let ls := l.substVars (Tm.liftSubst θ)
    let rs := r.substVars (Tm.liftSubst θ)
    have source_eq : source.substVars θ =
        .case (.op (.ask label) (caseOperand (constructorBit b (.var 0)))) ls rs := by
      simp [source, θ, ls, rs, caseOperand, substVars, Tm.subst, focus, literal, constructorBit]
    have low_eq : low.substVars θ = requestRegion label false ls rs := rfl
    have high_eq : high.substVars θ = requestRegion label true ls rs := rfl
    have target_eq : target.substVars θ = .case (constructorBit b (.var 0))
        ((requestRegion label false ls rs).renameVars Nat.succ)
        ((requestRegion label true ls rs).renameVars Nat.succ) := by
      simp only [target, substVars, Tm.subst, choose_weak_focus, low_eq, high_eq]
      simp [θ, focus]
    rw [source_eq, target_eq]
    have hctx := hsource.substVars (θ := θ) (fun _ _ h => focus_typed hi b h)
    rw [source_eq] at hctx
    obtain ⟨hls, hrs⟩ := request_scope hctx
    refine (beta label b hls hrs).trans ?_
    have out (v : Bool) : ValueBranches (U :: Γ) (requestRegion label v ls rs) L :=
      .case (.op (constructorBit_value v .unit).hasType) hls hrs
    let left := (out false).renameVars (Ren.wk (U :: Γ) U)
    let right := (out true).renameVars (Ren.wk (U :: Γ) U)
    cases b
    · apply Paper.Extension.Eqv.symm
      refine (Paper.Extension.Eqv.paper (.cfgEta (.native (.base
        (.caseInl (.var rfl) left.hasType right.hasType))))).trans ?_
      have erase := SubstitutionEquiv.letValue (.var (i := 0) rfl) left.hasType
      rw [drop_weakening] at erase
      exact .paper (.cfgEta (.native erase))
    · apply Paper.Extension.Eqv.symm
      refine (Paper.Extension.Eqv.paper (.cfgEta (.native (.base
        (.caseInr (.var rfl) left.hasType right.hasType))))).trans ?_
      have erase := SubstitutionEquiv.letValue (.var (i := 0) rfl) right.hasType
      rw [drop_weakening] at erase
      exact .paper (.cfgEta (.native erase))
  exact (Paper.Extension.Eqv.paper (.cfgEta (.native (native_focus_bit hi hsource.hasType)))).symm.trans
    ((Paper.Extension.Eqv.case (.var hi) (arms false) (arms true)).trans
      (.paper (.cfgEta (.native (native_focus_bit hi ht.hasType)))))

theorem term_case_operand_of (beta : CaseOperandBeta) {Γ L : List (Ty Empty)} {i : Nat} (hi : At Γ i Bit)
    (label : Bool) {l r : Region signature.Instr}
    (hl : ValueBranches (Bit :: Γ) l L) (hr : ValueBranches (Bit :: Γ) r L) :
    Paper.Eqv Γ (.case (.op (.ask label) (caseOperand (.var i))) l r)
      (.case (.var i) ((requestRegion label false l r).renameVars Nat.succ)
        ((requestRegion label true l r).renameVars Nat.succ)) L := by
  have lifted : CaseOperandBetaIn (Paper.Extension.Eqv Paper.Eqv) := by
    intro _ _ tag b _ _ hleft hright
    exact .paper (beta tag b hleft hright)
  exact (term_case_operand_extension_of lifted hi label hl hr).toPaper (fun h => h)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryDecisionReadback
