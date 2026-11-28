module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.NestedQuery
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SilentClassify

/-! # Mixed tables with nested request rows: completeness at every entry, and the regression -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate sumIso phaseFold classFold coprod_desc_ofRegion
  iterate_uniformity_ofBranchValue)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)

local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (seqValueBranches caseValueBranches)
open Paper.TypeCategory (ofRegion_id ofRegion_comp)
open Paper.Extension.Singleton (iterateSum iterateSum_map)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)

local notation "QLit" => Paper.Extension.Singleton.ofRegion (Step (τ := Ty Empty) (Φ := signature.Instr) false)
local notation "U" => (Ty.unit : Ty Empty)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking (Valid)

/-! ## Completeness -/

section Complete

variable {r r' : Region signature.Instr} {L L' : Bool → SLanding}

/-- Loops with tidy landings are equal exactly when they are valid in
every supported model. -/
theorem slanded_complete (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hl : SLanded r L) (hl' : SLanded r' L') (ht : ∀ q, (L q).Tidy) (ht' : ∀ q, (L' q).Tidy) :
    Eqv false [State] r r' [Bit] ↔ Valid h.hasType h'.hasType :=
  ⟨fun e => Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _,
    fun v => slanded_eqv h h' hl hl' (TableModel.slanded_point h h' hl hl' ht ht' v)⟩

end Complete

/-- Two mixed tables are equal at given original entries exactly when
they are valid in every supported model. -/
theorem mix_complete_all {K K' : Nat} (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
    (row' : Fin (K' + 1) → MixRow) (act' : Fin (K' + 1) → Bool → Bool → Act K') (i : Fin (K + 1))
    (i' : Fin (K' + 1)) :
    Eqv false [State] ((mixWritten row act).entered i) ((mixWritten row' act').entered i') [Bit] ↔
      Valid ((mixWritten row act).entered_typed i).hasType ((mixWritten row' act').entered_typed i').hasType := by
  obtain ⟨cyc, fuel, hc, hs⟩ := classification (mixSil row act)
  obtain ⟨cyc', fuel', hc', hs'⟩ := classification (mixSil row' act')
  obtain ⟨L, tidy, hl⟩ := mix_slanded row act (cyc := cyc) (fuel := fuel) ⟨hc, hs⟩ i
  obtain ⟨L', tidy', hl'⟩ := mix_slanded row' act' (cyc := cyc') (fuel := fuel') ⟨hc', hs'⟩ i'
  exact slanded_complete ((mixWritten row act).entered_typed i) ((mixWritten row' act').entered_typed i') hl hl'
    tidy tidy'

/-! ## Regression: a later request that is blind -/

theorem stash_classed (l₁ l₂ s n f : Bool) : Classed (stashRow l₁ l₂ s) (stashAct n f) veerCyc 0 := by
  refine ⟨fun y hy => ?_, fun a => ?_⟩
  · match y with
    | 0 => cases hy
    | 1 => cases f <;> exact ⟨_, _, rfl, rfl⟩
    | 2 => cases hy
    | 3 => cases f <;> exact ⟨_, _, rfl, rfl⟩
  · cases a with
    | ret b => exact True.intro
    | go y q =>
      match y with
      | 0 => exact rfl
      | 1 => exact rfl
      | 2 => exact rfl
      | 3 => exact rfl

theorem stash_nest (l₁ l₂ s n f : Bool) :
    nestTrees (stashRow l₁ l₂ s) (stashAct n f) veerCyc 0 =
      TreeTable.nest (K := 3) 4 (Router.ofSpin (stashLabel l₁ l₂) (stashSpun s n)).toTrees := by
  have progs : (nestTrees (stashRow l₁ l₂ s) (stashAct n f) veerCyc 0).prog =
      (TreeTable.nest (K := 3) 4 (Router.ofSpin (stashLabel l₁ l₂) (stashSpun s n)).toTrees).prog := by
    funext j
    match j with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
  have kids : (nestTrees (stashRow l₁ l₂ s) (stashAct n f) veerCyc 0).kids =
      (TreeTable.nest (K := 3) 4 (Router.ofSpin (stashLabel l₁ l₂) (stashSpun s n)).toTrees).kids := by
    funext j a b
    match j with
    | 0 =>
      cases s <;> cases n <;> cases a <;> cases b <;> first
        | rfl
        | (refine congrArg (Tree.ask _ _) (funext fun a' => funext fun b' => ?_)
           cases a' <;> cases b' <;> rfl)
    | 1 => rfl
    | 2 =>
      cases s <;> cases n <;> cases a <;> cases b <;> first
        | rfl
        | (refine congrArg (Tree.ask _ _) (funext fun a' => funext fun b' => ?_)
           cases a' <;> cases b' <;> rfl)
    | 3 => rfl
  exact (congrArg (fun k => TreeTable.mk (nestTrees (stashRow l₁ l₂ s) (stashAct n f) veerCyc 0).prog k) kids).trans
    (congrArg (fun p => TreeTable.mk p _) progs)

theorem stash_forward (l₁ l₂ s n : Bool) : (Router.ofSpin (stashLabel l₁ l₂) (stashSpun s n)).Forward 4 := by
  intro k hk a b
  match k, hk with
  | 0, _ => cases n <;> cases b <;> (show (_ : Nat) < _; decide)
  | 1, _ => cases n <;> cases b <;> (show (_ : Nat) < _; decide)
  | 2, _ => cases n <;> cases b <;> (show (_ : Nat) < _; decide)
  | 3, _ => cases n <;> cases b <;> (show (_ : Nat) < _; decide)
  | 4, hk => exact absurd hk (by decide)
  | 5, hk => exact absurd hk (by decide)
  | 6, hk => exact absurd hk (by decide)
  | 7, hk => exact absurd hk (by decide)

/-- The written table entered at the request row with each constant is
the explicit table of labelled rows and silent rows. -/
theorem stash_pointed (l₁ l₂ s n f : Bool) :
    SpinPointed ((mixWritten (stashRow l₁ l₂ s) (stashAct n f)).entered 0) (stashLabel l₁ l₂) (stashSpun s n)
      stashEntry := fun q => by
  have landed := nest_written_landed (stashRow l₁ l₂ s) (stashAct n f) (stash_classed l₁ l₂ s n f) 0 q
  have trees : ∀ i : Fin 4, Eqv false [State]
      ((nestTrees (stashRow l₁ l₂ s) (stashAct n f) veerCyc 0).entered i)
      ((Router.ofSpin (stashLabel l₁ l₂) (stashSpun s n)).entered (shiftN 4 i)) [Bit] := fun i => by
    rw [stash_nest]
    exact router_nest_eqv (K := 3) 4 _ (stash_forward l₁ l₂ s n) i
  cases q
  · exact Paper.Extension.Eqv.trans landed
      (const_congr ((nestTrees (stashRow l₁ l₂ s) (stashAct n f) veerCyc 0).entered_typed 0)
        ((Router.ofSpin (stashLabel l₁ l₂) (stashSpun s n)).entered_typed 4) (trees 0) false)
  · exact Paper.Extension.Eqv.trans landed
      (const_congr ((nestTrees (stashRow l₁ l₂ s) (stashAct n f) veerCyc 0).entered_typed 2)
        ((Router.ofSpin (stashLabel l₁ l₂) (stashSpun s n)).entered_typed 6) (trees 2) true)

theorem stash_tidy (l₁ l₂ s n : Bool) : Tidy (stashLabel l₁ l₂) (stashSpun s n) :=
    fun i l hi tag pl j q ha hj => by
  match i with
  | 0 => cases ha; rfl
  | 1 => cases ha; rfl
  | 2 => cases ha; rfl
  | 3 => cases ha; rfl
  | 4 =>
    cases tag
    · cases pl <;> cases ha <;> cases hj
    · cases ha
  | 5 => cases hi
  | 6 =>
    cases tag
    · cases pl <;> cases ha <;> cases hj
    · cases ha
  | 7 => cases hi

/-- The second request is blind: all of its replies lead to silent rows. -/
theorem stash_blind (l₁ l₂ s n : Bool) (c y tag pl : Bool) :
    ∃ j q, stashSpun s n (stashInner c y) tag pl = .go j q ∧ stashLabel l₁ l₂ j = none := by
  cases c <;> cases y <;> cases n <;> cases pl <;> exact ⟨_, _, rfl, rfl⟩

theorem stash_blind_rel {l₁ l₂ : Bool} (n n' b : Bool) :
    Act.Rel (fun j j' => j = j' ∨ (stashLabel l₁ l₂ j = none ∧ stashLabel l₁ l₂ j' = none))
      (Act.go (stashSpin (n != b)) false) (Act.go (stashSpin (n' != b)) false) := by
  cases n <;> cases n' <;> cases b <;> first | exact ⟨rfl, .inl rfl⟩ | exact ⟨rfl, .inr ⟨rfl, rfl⟩⟩

/-- Equivalent divergent continuations: whichever Bit the blind request
enters the silent cycle with, and whether the cycle negates the Bit. -/
theorem stash_eqv (l₁ l₂ s n f n' f' : Bool) :
    Eqv false [State] ((mixWritten (stashRow l₁ l₂ s) (stashAct n f)).entered 0)
      ((mixWritten (stashRow l₁ l₂ s) (stashAct n' f')).entered 0) [Bit] :=
  spin_pointed_eqv ((mixWritten (stashRow l₁ l₂ s) (stashAct n f)).entered_typed 0)
    ((mixWritten (stashRow l₁ l₂ s) (stashAct n' f')).entered_typed 0)
    (stash_pointed l₁ l₂ s n f) (stash_pointed l₁ l₂ s n' f')
    fun q => spin_router_congr (stashLabel l₁ l₂) _ _ (fun x l' hx a b => by
      match x with
      | 0 => exact stash_blind_rel n n' b
      | 1 => exact stash_blind_rel n n' b
      | 2 => exact stash_blind_rel n n' b
      | 3 => exact stash_blind_rel n n' b
      | 4 => cases a <;> cases b <;> cases s <;> first | exact rfl | exact ⟨rfl, .inl rfl⟩
      | 5 => cases hx
      | 6 => cases a <;> cases b <;> cases s <;> first | exact rfl | exact ⟨rfl, .inl rfl⟩
      | 7 => cases hx) (stashEntry q)

/-- The blind request queried with the stored first reply differs from
the blind request queried with the entry Bit. -/
theorem stash_ne_slot (l₁ l₂ n f n' f' : Bool) :
    ¬ Eqv false [State] ((mixWritten (stashRow l₁ l₂ false) (stashAct n f)).entered 0)
      ((mixWritten (stashRow l₁ l₂ true) (stashAct n' f')).entered 0) [Bit] := fun e => by
  obtain ⟨R, bis, r⟩ := TableModel.query_pointed_bisim (stash_tidy l₁ l₂ false n) (stash_tidy l₁ l₂ true n')
    ((mixWritten (stashRow l₁ l₂ false) (stashAct n f)).entered_typed 0)
    ((mixWritten (stashRow l₁ l₂ true) (stashAct n' f')).entered_typed 0)
    (stash_pointed l₁ l₂ false n f) (stash_pointed l₁ l₂ true n' f') e false
  exact Bool.false_ne_true (And.left (bis.act 4 4 r false true)).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
