module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Chain.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Example.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Substitution.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Join.Thms

/-! # Replay two moves along a cyclic state-forgetting square -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetChainExample

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory
open Paper.WithEntryLet
  (Site repairTargetMoves repairTargetAfterLetValue uniformity_of_target_moves ofRegion_comp_constructor)
open Paper.WithEntryLet.OperandExample hiding source target repaired corrected_square corrected_iterate
open Paper.WithEntryLet.ChainExample Paper.EntryLetObstruction
open Paper.Extension.Singleton (projection projectStep iterateChosen projectSquare_iff)
open SequencingObstruction (Instruction)

local notation "J" => projection Seed

set_option backward.isDefEq.respectTransparency false

private theorem weaken_labels {Γ : VCtx (Ty Empty)} {L K : LCtx (Ty Empty)}
    {r : Region Instruction} (hr : ValueBranches Γ r L) {ρ : Nat → Nat} (hρ : Ren L K ρ) :
    ValueBranches Γ (r.renameLabels ρ) K := by
  rw [renameLabels_eq_lsubst]
  exact hr.lsubst (fun _ _ hi => .br (hρ hi) (.var rfl))

theorem sequenceRequests_typed {p q : Region Instruction}
    (hp : ValueBranches [U] p [U]) (hq : ValueBranches [U] q [Bit]) :
    ValueBranches [U] (sequenceRequests p q) [Bit] := by
  have widen : Ren [U] [U, Bit] id := by
    intro i A hi
    cases i with
    | zero => exact hi
    | succ i => simp [At] at hi
  have he : ValueBranches [U] p [U, Bit] := by
    simpa only [renameLabels_id] using weaken_labels hp widen
  have hb := hq.renameVars ((Ren.wk [] U).lift U)
  exact .cfg (fun _ : Fin 1 => U) he (fun _ => weaken_labels hb (Ren.wk [Bit] U))

private theorem move_second_block :
    Site.here.move ((flatRecurringRequest.renameVars (lift Nat.succ)).renameLabels Nat.succ) =
      some ((movedRecurringRequest.renameVars (lift Nat.succ)).renameLabels Nat.succ) := by
  simp only [flatRecurringRequest, flatRequest, movedRecurringRequest, movedRequest, compLSubst,
    lsubst, renameVars, renameLabels, Site.move, Site.rewriteAt, Site.moveEntry]
  congr 2
  apply congrArg (Region.cfg (.br 0 (.var 0) : Region Instruction) 2)
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun j => j.elim0)) i

private theorem entry_move :
    (Site.entry .here).move twoFlatRequests = some firstRequestMoved := rfl

private theorem block_move (p : Region Instruction) :
    (Site.block 0 .here).move (sequenceRequests p flatRecurringRequest) =
      some (sequenceRequests p movedRecurringRequest) := by
  simp only [sequenceRequests, CfgEta.singleCfg, Site.move, Site.rewriteAt, Nat.zero_lt_succ, dite_true]
  change (Site.here.move _).map _ = _
  rw [move_second_block]
  simp only [Option.map_some, Option.some.injEq]
  congr 1
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  simp

private theorem only_request_root (site : Site) {a payload : Tm Instruction}
    {label n : Nat} {blocks : Fin n → Region Instruction} {r : Region Instruction}
    (branches : ∀ i, ∃ ℓ t, blocks i = .br ℓ t)
    (hm : site.move (.cfg (.let₁ a (.br label payload)) n blocks) = some r) :
    site = .here := by
  cases site with
  | here => rfl
  | entry s =>
    cases s with
    | unaryBody next => cases next <;> simp [Site.move, Site.rewriteAt, Site.moveEntry] at hm
    | _ => simp [Site.move, Site.rewriteAt, Site.moveEntry] at hm
  | block i next =>
    simp only [Site.move, Site.rewriteAt] at hm
    split at hm
    next hi =>
      obtain ⟨ℓ, t, hb⟩ := branches ⟨i, hi⟩
      rw [hb] at hm
      cases next <;> simp [Site.rewriteAt, Site.moveEntry] at hm
    next _ => contradiction
  | _ => simp [Site.move, Site.rewriteAt] at hm

private theorem one_move (site : Site) {r : Region Instruction}
    (hm : site.move twoFlatRequests = some r) :
    r = firstRequestMoved ∨ r = secondRequestMoved := by
  cases site with
  | entry next =>
    change (next.move flatRequest).map
      (fun e => sequenceRequests e flatRecurringRequest) = some r at hm
    obtain ⟨out, hout, rfl⟩ := Option.map_eq_some_iff.mp hm
    have same : next = .here := only_request_root next (fun i =>
      Fin.cases ⟨_, _, rfl⟩ (Fin.cases ⟨_, _, rfl⟩ (fun j => j.elim0)) i) hout
    subst next
    cases Option.some.inj hout
    exact .inl rfl
  | block idx next =>
    have hidx : idx < 1 := by
      by_contra h
      simp [twoFlatRequests, sequenceRequests, CfgEta.singleCfg, Site.move, Site.rewriteAt, h] at hm
    have hz : idx = 0 := by omega
    subst idx
    have hm' := hm
    simp only [twoFlatRequests, sequenceRequests, CfgEta.singleCfg, Site.move, Site.rewriteAt,
      Nat.zero_lt_succ, dite_true] at hm'
    obtain ⟨out, hout, _⟩ := Option.map_eq_some_iff.mp hm'
    have same : next = .here := by
      apply only_request_root next _ hout
      intro i
      refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i
      · exact ⟨_, _, rfl⟩
      · exact ⟨_, _, rfl⟩
    subst next
    change (Site.block 0 .here).move (sequenceRequests flatRequest flatRecurringRequest) = some r at hm
    rw [block_move] at hm
    exact .inr (Option.some.inj hm).symm
  | _ => simp [twoFlatRequests, sequenceRequests, CfgEta.singleCfg, flatRequest, Site.move, Site.rewriteAt, Site.moveEntry] at hm

local notation "substForget" => (Tm.singleSubst (Tm.unit : Tm Instruction) ∘ lift Nat.succ)

private theorem substForget_typed :
    ∀ ⦃i A⦄, At [U] i A → Tm.BranchValue [Bit] (substForget i) A := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .unit
  | succ i => simp [At] at hi

private theorem block_move_composite :
    (Site.block 0 .here).move (firstRequestMoved.substVars substForget) =
      some (bothRequestsMoved.substVars substForget) := by
  rw [Site.move_substVars]
  change ((Site.block 0 .here).move (sequenceRequests movedRequest flatRecurringRequest)).map _ = _
  rw [block_move]
  rfl

private theorem entry_move_composite :
    (Site.entry .here).move (twoFlatRequests.substVars substForget) =
      some (firstRequestMoved.substVars substForget) := by
  rw [Site.move_substVars, entry_move]
  rfl

theorem moves_composite :
    Site.moveAll sites (twoFlatRequests.substVars substForget) =
      some (bothRequestsMoved.substVars substForget) := by
  change ((Site.entry .here).move _ >>= fun p => (Site.block 0 .here).move p >>= some) = _
  rw [entry_move_composite]
  change ((Site.block 0 .here).move (firstRequestMoved.substVars substForget) >>= some) = _
  rw [block_move_composite]
  rfl

private theorem both_typed : ValueBranches [U] bothRequestsMoved [Bit] :=
  sequenceRequests_typed movedRequest_typed movedStep_typed

private theorem bothComposite : ValueBranches [Bit] (bothRequestsMoved.substVars substForget) [Bit] :=
  both_typed.substVars substForget_typed

private theorem both_eq :
    ofRegion both_typed = ofRegion movedRequest_typed ≫ ofRegion movedStep_typed := by
  let h := CfgEta.TypeCategory.seqValueBranches movedRequest_typed movedStep_typed
  rw [ofRegion_comp movedRequest_typed movedStep_typed h]
  exact (ofRegion_eq_iff both_typed h).2
    (Paper.linkedJoin movedRequest_typed (movedStep_typed.renameVars ((Ren.wk [] U).lift U)))

private theorem end_square :
    source ≫ coprod.map (𝟙 X) forget = ofRegion bothComposite ≫ (sumIso U U).hom := by
  have ex : forget ≫ ofRegion both_typed = ofRegion bothComposite :=
    ofRegion_comp_constructor (.unit (Γ := [Bit])) both_typed bothComposite
  rw [← ex, Category.assoc, both_eq, Category.assoc, movedTarget_eq, source,
    taggedSource_forget, Category.assoc]

theorem repaired :
    let hr := sequenceRequests_typed flatRequest_typed flatStep_typed
    ∃ g : X ⟶ X ⨿ X,
      projectStep Seed g = projectStep Seed (ofRegion hr ≫ (sumIso U U).hom) ∧
      source ≫ coprod.map (𝟙 X) forget = forget ≫ g :=
  repairTargetMoves sites (.unit (Γ := [Bit])) (sequenceRequests_typed flatRequest_typed flatStep_typed)
    source bothComposite moves_composite end_square

theorem unfinished_square_ne {r : Region Instruction}
    (hr : ValueBranches [U] r [Bit])
    (h : r = twoFlatRequests ∨ r = firstRequestMoved ∨ r = secondRequestMoved) :
    source ≫ coprod.map (𝟙 X) forget ≠ forget ≫ (ofRegion hr ≫ (sumIso U U).hom) := by
  have ht := hr.substVars substForget_typed
  have ex : forget ≫ ofRegion hr = ofRegion ht :=
    ofRegion_comp_constructor (.unit (Γ := [Bit])) hr ht
  intro eq
  rw [end_square, ← Category.assoc forget, ex] at eq
  exact unfinishedRequests_ne_bothMoved h ((ofRegion_eq_iff ht bothComposite).1
    ((cancel_mono (sumIso U U).hom).1 eq.symm))

theorem no_single_move_repairs (site : Site) {r : Region Instruction}
    (hr : ValueBranches [Bit] r [Bit])
    (hm : site.move (twoFlatRequests.substVars substForget) = some r) :
    source ≫ coprod.map (𝟙 X) forget ≠ ofRegion hr ≫ (sumIso U U).hom := by
  obtain ⟨q, hq, rfl, htyped, _⟩ := Site.move_pullback site
    (sequenceRequests_typed flatRequest_typed flatStep_typed) substForget hm
  rw [← ofRegion_comp_constructor (.unit (Γ := [Bit])) htyped hr, Category.assoc]
  obtain eq | eq := one_move site hq
  · exact unfinished_square_ne htyped (.inr (.inl eq))
  · exact unfinished_square_ne htyped (.inr (.inr eq))

theorem corrected_iterate :
    let hr := sequenceRequests_typed flatRequest_typed flatStep_typed
    iterateChosen Seed (projectStep Seed source) =
      (J).map forget ≫ iterateChosen Seed (projectStep Seed (ofRegion hr ≫ (sumIso U U).hom)) :=
  uniformity_of_target_moves sites (.unit (Γ := [Bit])) (sequenceRequests_typed flatRequest_typed flatStep_typed)
    source bothComposite moves_composite end_square

private theorem no_substituted_var_zero (a : Tm Instruction) :
    a.subst substForget ≠ .var 0 := by
  cases a with
  | var i =>
    cases i with
    | zero =>
      change (Tm.unit : Tm Instruction) ≠ .var 0
      simp
    | succ i =>
      change (Tm.var (i + 1) : Tm Instruction) ≠ .var 0
      simp
  | _ => simp [Tm.subst]

theorem mixed_expansion :
    Paper.Eqv [Bit] (firstRequestMoved.substVars substForget) expandedFirstMove [Bit] ∧
      (∀ q : Region Instruction, q.substVars substForget ≠ expandedFirstMove) ∧
      (Site.unaryBody (.block 0 .here)).move expandedFirstMove =
        some (.let₁ (.var 0) ((bothRequestsMoved.substVars substForget).renameVars Nat.succ)) := by
  refine ⟨?_, ?_, ?_⟩
  · have typed := (sequenceRequests_typed movedRequest_typed flatStep_typed).substVars substForget_typed
    have weakened := typed.renameVars (Ren.wk [Bit] Bit)
    have beta := SubstitutionEquiv.letValue (.var (i := 0) (rfl : At [Bit] 0 Bit)) weakened.hasType
    have cancels : Tm.singleSubst (Tm.var 0 : Tm Instruction) ∘ Nat.succ = Tm.var := rfl
    rw [substVars_renameVars, cancels, substVars_var] at beta
    exact .symm (.cfgEta (.native beta))
  · intro q
    cases q with
    | let₁ a body =>
      intro he
      exact no_substituted_var_zero a (Region.let₁.inj he).1
    | _ => simp [Region.substVars, expandedFirstMove]
  · change ((Site.block 0 .here).move
      ((firstRequestMoved.substVars substForget).renameVars Nat.succ)).map (Region.let₁ (.var 0)) = _
    rw [renameVars_eq_substVars, Site.move_substVars, block_move_composite]
    simp only [Option.map_some, renameVars_eq_substVars]

private theorem contract_weakened (r : Region Instruction) :
    (r.renameVars Nat.succ).substVars (Tm.singleSubst (.var 0)) = r := by
  rw [substVars_renameVars]
  exact substVars_var r

private theorem expandedBody_typed :
    ValueBranches [Bit, Bit] ((firstRequestMoved.substVars substForget).renameVars Nat.succ) [Bit] :=
  ((sequenceRequests_typed movedRequest_typed flatStep_typed).substVars substForget_typed).renameVars
    (Ren.wk [Bit] Bit)

theorem expandedBothMoves_typed : ValueBranches [Bit] expandedBothMoves [Bit] :=
  .let₁ (.var rfl) (bothComposite.renameVars (Ren.wk [Bit] Bit))

theorem mixed_endpoint :
    Paper.Eqv [Bit] expandedBothMoves (bothRequestsMoved.substVars substForget) [Bit] := by
  obtain ⟨q, hq, _, eq⟩ := Site.move_under_letValue (.block 0 .here)
    (.var (i := 0) (rfl : At [Bit] 0 Bit)) expandedBody_typed mixed_expansion.2.2
  rw [contract_weakened, block_move_composite] at hq
  cases Option.some.inj hq
  exact eq

theorem mixed_final_composite :
    source ≫ coprod.map (𝟙 X) forget = ofRegion expandedBothMoves_typed ≫ (sumIso U U).hom := by
  rw [(ofRegion_eq_iff expandedBothMoves_typed bothComposite).2 mixed_endpoint]
  exact end_square

private theorem mixed_prefix :
    Site.moveAll [.entry .here] (twoFlatRequests.substVars substForget) =
      some (((firstRequestMoved.substVars substForget).renameVars Nat.succ).substVars
        (Tm.singleSubst (.var 0))) := by
  rw [contract_weakened]
  change ((Site.entry .here).move (twoFlatRequests.substVars substForget) >>= some) = _
  rw [entry_move_composite]
  rfl

theorem mixed_repaired :
    let hr := sequenceRequests_typed flatRequest_typed flatStep_typed
    ∃ g : X ⟶ X ⨿ X,
      projectStep Seed g = projectStep Seed (ofRegion hr ≫ (sumIso U U).hom) ∧
      source ≫ coprod.map (𝟙 X) forget = forget ≫ g :=
  repairTargetAfterLetValue [.entry .here] (.block 0 .here)
    (.unit (Γ := [Bit])) (sequenceRequests_typed flatRequest_typed flatStep_typed)
    source (.var (i := 0) rfl) expandedBody_typed expandedBothMoves_typed
    mixed_prefix mixed_expansion.2.2 mixed_final_composite

theorem mixed_corrected_iterate :
    let hr := sequenceRequests_typed flatRequest_typed flatStep_typed
    iterateChosen Seed (projectStep Seed source) =
      (J).map forget ≫ iterateChosen Seed (projectStep Seed (ofRegion hr ≫ (sumIso U U).hom)) := by
  obtain ⟨g, hg, native⟩ := mixed_repaired
  dsimp only
  rw [← hg]
  exact Paper.Extension.Singleton.uniformity_of_constructor_square Seed ⟨.unit, .unit, rfl⟩ source g native

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetChainExample
