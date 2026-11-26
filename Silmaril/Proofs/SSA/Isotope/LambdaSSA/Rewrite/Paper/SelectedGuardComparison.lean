module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.KnownGuard.RequestContext.Traversal.Comparison.Defs

/-! # Scope and exactness of the selected guard comparison -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedGuardComparison

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open Paper.WithCaseBind.OpenReplay
open Paper.WithCaseBind.OpenReplay.KnownGuardTraversal (requestRegion requestTerm retainPayload)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open CfgEta.TypeCategory (returnRegion)

local instance : HasTy signature.Instr (Ty Empty) := signature.hasTy

private def Acyclic {Φ : Type} : Region Φ → Prop
  | .br .. => True
  | .case _ l r => Acyclic l ∧ Acyclic r
  | .let₁ _ r | .let₂ _ r => Acyclic r
  | .cfg .. => False

private theorem acyclic_subst {Φ : Type} {r : Region Φ} (h : Acyclic r) (σ : Nat → Tm Φ) :
    Acyclic (r.substVars σ) := by
  induction r generalizing σ <;> simp_all [Acyclic, substVars]

private theorem acyclic_renameVars {Φ : Type} {r : Region Φ} (h : Acyclic r) (ρ : Nat → Nat) :
    Acyclic (r.renameVars ρ) := by
  induction r generalizing ρ <;> simp_all [Acyclic, renameVars]

private theorem acyclic_renameLabels {Φ : Type} {r : Region Φ} (h : Acyclic r) (ρ : Nat → Nat) :
    Acyclic (r.renameLabels ρ) := by
  induction r generalizing ρ <;> simp_all [Acyclic, renameLabels]

private theorem acyclic_lsubst {Φ : Type} {r : Region Φ} (h : Acyclic r)
    (σ : Nat → Region Φ) (hσ : ∀ i, Acyclic (σ i)) : Acyclic (r.lsubst σ) := by
  induction r generalizing σ with
  | br i _ => exact acyclic_subst (hσ i) _
  | case _ _ _ hl hr =>
    exact ⟨hl h.1 _ (fun i => acyclic_renameVars (hσ i) _), hr h.2 _ (fun i => acyclic_renameVars (hσ i) _)⟩
  | let₁ _ _ ih => exact ih h _ (fun i => acyclic_renameVars (hσ i) _)
  | let₂ _ _ ih => exact ih h _ (fun i => acyclic_renameVars (acyclic_renameVars (hσ i) _) _)
  | cfg => exact False.elim h

private theorem return_acyclic {Φ : Type} (t : Tm Φ) : Acyclic (returnRegion t) := by
  induction t <;> try trivial
  case let₁ _ _ ha hb => exact acyclic_lsubst ha _ (fun _ => hb)

private theorem program_acyclic {X D : Ty Empty} (p : Program signature.Instr X D) :
    Acyclic p.elaborate.val := by
  induction p with
  | returned t => exact return_acyclic t.elaborate.val
  | branchInput => trivial
  | let₂ _ _ _ _ ih => exact acyclic_subst ih _

private theorem packedBody_acyclic {Φ : Type} {r : Region Φ} (h : Acyclic r) :
    Acyclic (Paper.PackedBody.applyPacked r) :=
  acyclic_subst h _

private theorem selected_acyclic {X : Ty Empty} {L : List (Ty Empty)} (p : CaseTree signature.Instr X L) :
    Acyclic p.elaborate.val := by
  induction p with
  | exit _ _ body => exact acyclic_renameLabels (program_acyclic body) _
  | taggedExit _ _ tag _ => cases tag <;> trivial
  | case _ _ _ _ _ hl hr => exact ⟨packedBody_acyclic hl, packedBody_acyclic hr⟩

private theorem emits_acyclic {r : Region signature.Instr} (h : Acyclic r) (emits : List Bool) :
    Acyclic (prependEmits emits r) := by
  induction emits with
  | nil => exact h
  | cons _ _ ih => exact acyclic_renameVars ih _

private theorem traversal_acyclic {L : List (Ty Empty)} {tag : Bool} {X : Ty Empty} {n : Nat}
    {slots : Fin n → Term signature.Instr X Bit} {known : Term signature.Instr X Bit} {p : ReadTree L n}
    (c : KnownGuardTraversal L tag slots known p) (payload : Term signature.Instr X unit) :
    Acyclic (c.pruned payload) := by
  induction c with
  | @keep _ _ slots _ p => exact selected_acyclic (p.selectedWith slots)
  | request _ _ _ _ _ hl hr =>
    exact ⟨packedBody_acyclic (hl (retainPayload payload)), packedBody_acyclic (hr (retainPayload payload))⟩
  | guard _ _ _ _ _ _ _ _ _ hfl hfr htl htr =>
    let carried := retainPayload (A := Bit) (retainPayload (A := unit) payload)
    exact ⟨packedBody_acyclic ⟨packedBody_acyclic (hfl carried), packedBody_acyclic (hfr carried)⟩,
      packedBody_acyclic ⟨packedBody_acyclic (htl carried), packedBody_acyclic (htr carried)⟩⟩
  | @prune Y _ _ _ _ _ _ _ emits _ low _ _ _ l r hl hr =>
    let carried := retainPayload (A := Bit) (retainPayload (A := unit) payload)
    let live := requestRegion (requestTerm (X := product Y unit) [] (if tag then !low else low))
      (l.pruned carried) (r.pruned carried)
    have hLive : Acyclic live := ⟨packedBody_acyclic (hl carried), packedBody_acyclic (hr carried)⟩
    exact emits_acyclic (r := .let₁ payload.elaborate.val (Paper.PackedBody.applyPacked live))
      (packedBody_acyclic hLive) emits

private theorem read_available {Φ : Type} {r : Region Φ} (h : Acyclic r) :
    (AcyclicSyntax.read r).isSome := by
  induction r with
  | br => rfl
  | case _ l r hl hr =>
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hl h.1)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hr h.2)
    simp [AcyclicSyntax.read, ha, hb]
  | let₁ _ r ih =>
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (ih h)
    simp [AcyclicSyntax.read, ha]
  | let₂ _ r ih =>
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (ih h)
    simp [AcyclicSyntax.read, ha]
  | cfg => exact False.elim h

theorem selected_readable {X : Ty Empty} {L : List (Ty Empty)} (p : CaseTree signature.Instr X L) :
    (AcyclicSyntax.read p.elaborate.val).isSome :=
  read_available (selected_acyclic p)

theorem scoped_compare_accepted_iff {X : Ty Empty} {L : List (Ty Empty)} (left right : ScopedTarget X L)
    (readable : (AcyclicSyntax.read left.val).isSome) :
    (left.compare right).accepted = true ↔ left = right := by
  constructor
  · cases left.compare right with
    | unknown => simp [EqualityVerdict.accepted]
    | equal h => exact fun _ => h
  · rintro rfl
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp readable
    simp [ScopedTarget.compare, ha, EqualityVerdict.accepted]

theorem normalized_readable {X : Ty Empty} {L : List (Ty Empty)} (p : SelectedAt X L) :
    (AcyclicSyntax.read p.normalized.val).isSome := by
  apply read_available
  exact ⟨packedBody_acyclic (traversal_acyclic p.traversal.onFalse (.snd X unit)),
    packedBody_acyclic (traversal_acyclic p.traversal.onTrue (.snd X unit))⟩

theorem compare_accepted_iff {X : Ty Empty} {L : List (Ty Empty)} (left right : SelectedAt X L) :
    (left.compare right).accepted = true ↔ left.normalized = right.normalized := by
  have accepted : (left.compare right).accepted = (left.normalized.compare right.normalized).accepted := by
    unfold SelectedAt.compare
    cases left.normalized.compare right.normalized <;> rfl
  rw [accepted]
  exact scoped_compare_accepted_iff _ _ (normalized_readable left)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedGuardComparison
