module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Relay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.PartialFold.Feedback.Thms
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.MixedTables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonBlocks

/-! # The relay table collapses by the partial fold with feedback -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step partial_fold_feedback)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate phaseType phaseFold sumIso coprod_desc_ofRegion
  sumInl sumInr blockStep blockRoute)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open SingletonPhases (system)

local notation "S" => system (Φ := signature.Instr) State
local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false

/-- A returned Bit as a packed loop state. -/
noncomputable abbrev bitState : ofType (Φ := signature.Instr) Bit ⟶ ofType State :=
  ofRegion (r := .br 0 (.inl (.var 0))) (.br rfl (.inl (.var rfl)))

/-- Entering state `j` with a constructor value is that value followed by the entry. -/
theorem injOf_eq {X : Ty Empty} {a : Tm signature.Instr} (ha : Tm.BranchValue [X] a State) :
    ∀ (K : Nat) (j : Fin (K + 1)),
      ofRegion (r := .br 0 (injTm K j a)) (.br rfl (injTm_typed ha K j)) =
        ofRegion (r := .br 0 a) (.br rfl ha) ≫ injArr K j
  | 0, j => by
    have j0 : j = 0 := Fin.eq_zero j
    subst j0
    exact (Category.comp_id _).symm.trans
      (congrArg (ofRegion (r := .br 0 a) (.br rfl ha) ≫ ·) injArr_base.symm)
  | K + 1, j => by
    refine Fin.cases ?_ (fun j => ?_) j
    · exact (br_inl ha).trans (congrArg (ofRegion (r := .br 0 a) (.br rfl ha) ≫ ·) (injArr_zero K).symm)
    · exact (br_inr (injTm_typed ha K j)).trans
        ((congrArg (· ≫ (S).inr K) (injOf_eq ha K j)).trans
          ((Category.assoc _ _ _).trans
            (congrArg (ofRegion (r := .br 0 a) (.br rfl ha) ≫ ·) (injArr_succ K j).symm)))

theorem relayRoute_sum (K : Nat) (j₁ j₂ : Fin (K + 1)) :
    ofRegion (relayRoute_typed K j₁ j₂) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom =
      (sumIso (Φ := signature.Instr) Bit State).hom ≫
        coprod.desc (bitState ≫ injArr K j₁ ≫ coprod.inr) (injArr K j₂ ≫ coprod.inr) := by
  have arrow : ofRegion (relayRoute_typed K j₁ j₂) =
      (sumIso (Φ := signature.Instr) Bit State).hom ≫
        coprod.desc (ofRegion (stay_typed K j₁)) (ofRegion (goto_typed K j₂)) :=
    (coprod_desc_ofRegion (stay_typed K j₁) (goto_typed K j₂)).symm
  have stay : ofRegion (stay_typed K j₁) =
      (bitState ≫ injArr K j₁) ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
    (br_inr (injTm_typed (.inl (.var rfl)) K j₁)).trans
      (congrArg (· ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv))
        (injOf_eq (.inl (.var rfl)) K j₁))
  have goto : ofRegion (goto_typed K j₂) =
      injArr K j₂ ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
    br_inr (injTm_typed (.var rfl) K j₂)
  rw [arrow, stay, goto, Category.assoc]
  congr 1
  apply coprod.hom_ext <;> simp

theorem relayRow_arrow (K : Nat) (p : Program) (j₁ j₂ : Fin (K + 1)) :
    ofRegion (relayRow_typed K p j₁ j₂) = ofRegion (step_typed p) ≫ ofRegion (relayRoute_typed K j₁ j₂) :=
  (Paper.TypeCategory.ofRegion_comp (step_typed p) (relayRoute_typed K j₁ j₂) _).symm

theorem relayRow_sum (K : Nat) (p : Program) (j₁ j₂ : Fin (K + 1)) :
    ofRegion (relayRow_typed K p j₁ j₂) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom =
      stepP p ≫ coprod.desc (bitState ≫ injArr K j₁ ≫ coprod.inr) (injArr K j₂ ≫ coprod.inr) := by
  rw [relayRow_arrow, Category.assoc, relayRoute_sum, Category.assoc]

variable (K : Nat) (q p : Program) (j : Fin (K + 1))

/-- The relaying row: a return repeats into the untouched state, a repeat
enters the block at state `j`. -/
noncomputable abbrev relayState :
    ofType (Φ := signature.Instr) State ⟶ (ofType Bit ⨿ ofType State) ⨿ ofType (States K) :=
  stepP q ≫ coprod.desc (bitState ≫ coprod.inr ≫ coprod.inl) (injArr K j ≫ coprod.inr)

/-- The literal relay dispatcher is a joined step of the two blocks. -/
theorem relay_step :
    ofRegion (dispatch_typed (K + 1) (relayRows_typed K q p j)) ≫
        (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom =
      blockStep State (States K) (relayState K q j) (fanBlock K p) := by
  have zero : injArr (K + 1) 0 = sumInl (Φ := signature.Instr) State (States K) := injArr_zero K
  have succ (i : Fin (K + 1)) :
      injArr (K + 1) i.succ = injArr K i ≫ sumInr (Φ := signature.Instr) State (States K) :=
    injArr_succ K i
  apply SingletonPhases.sum_ext State (States K)
  · have d0 : injArr (K + 1) 0 ≫ ofRegion (dispatch_typed (K + 1) (relayRows_typed K q p j)) =
        ofRegion (relayRow_typed (K + 1) q 0 j.succ) :=
      inj_dispatch (K + 1) (relayRows_typed K q p j) 0
    have l0 := (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom) d0).trans
        (relayRow_sum (K + 1) q 0 j.succ))
    rw [zero, succ j] at l0
    refine l0.trans ?_
    refine Eq.trans ?_ ((SingletonBlocks.blockSystem State (States K)).inl_desc _ _).symm
    have m0 : coprod.desc (bitState ≫ sumInl State (States K) ≫ coprod.inr)
          ((injArr K j ≫ sumInr State (States K)) ≫ coprod.inr) =
        coprod.desc (bitState ≫ coprod.inr ≫ coprod.inl) (injArr K j ≫ coprod.inr) ≫
          blockRoute State (States K) Bit := by
      unfold blockRoute
      apply coprod.hom_ext <;> simp
    exact (congrArg (stepP q ≫ ·) m0).trans (Category.assoc _ _ _).symm
  · refine Eq.trans ?_ ((SingletonBlocks.blockSystem State (States K)).inr_desc _ _).symm
    apply inj_ext K
    intro i
    have di : injArr (K + 1) i.succ ≫ ofRegion (dispatch_typed (K + 1) (relayRows_typed K q p j)) =
        ofRegion (row_typed (K + 1) p 0) :=
      inj_dispatch (K + 1) (relayRows_typed K q p j) i.succ
    have li := (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom) di).trans
        (row_sum (K + 1) p 0))
    rw [succ i, zero, Category.assoc] at li
    have fold := inj_fold K i
    refine li.trans ?_
    unfold blockRoute
    simp only [fanBlock, stepP, Category.assoc, coprod.inl_desc, reassoc_of% fold]

theorem relay_row :
    relayState K q j ≫ coprod.map (𝟙 _) (phaseFold State K) = relayState 0 q 0 := by
  have fold := inj_fold K j
  have base : injArr 0 0 = 𝟙 (ofType (Φ := signature.Instr) State) := injArr_base
  have m : coprod.desc (bitState ≫ coprod.inr ≫ coprod.inl) (injArr K j ≫ coprod.inr) ≫
      coprod.map (𝟙 (ofType (Φ := signature.Instr) Bit ⨿ ofType State)) (phaseFold State K) =
      coprod.desc (bitState ≫ coprod.inr ≫ coprod.inl) (injArr 0 0 ≫ coprod.inr) := by
    apply coprod.hom_ext
    · simp
      rfl
    · simp [reassoc_of% fold, base]
      rfl
  exact (Category.assoc _ _ _).trans (congrArg (stepP q ≫ ·) m)

theorem dispatchLoop_arrow {K : Nat} {rows : Fin (K + 1) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [Silmaril.coprod Bit (States K)]) :
    ofRegion (dispatchLoop_typed h) =
      iterate (ofRegion (dispatch_typed K h) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) :=
  (iterate_exact (dispatch_typed K h)).symm

theorem dispatchEntered_arrow {K : Nat} {rows : Fin (K + 1) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [Silmaril.coprod Bit (States K)]) (i : Fin (K + 1)) :
    ofRegion (dispatchEntered_typed h i) = injArr K i ≫ ofRegion (dispatchLoop_typed h) :=
  (Paper.TypeCategory.ofRegion_comp (entry_typed K i) (dispatchLoop_typed h)
    (dispatchEntered_typed h i)).symm

/-- A relay table entered at any state equals the two-state relay table
entered at the state's class. -/
theorem relayFan_eqv (i : Fin (K + 2)) :
    Eqv false [State] (relayFan K q p j i) (relayFan 0 q p 0 (collapse i)) [Bit] := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (relayFan_typed K q p j i)
    (relayFan_typed 0 q p 0 (collapse i))).1
  change (π).map (ofRegion (dispatchEntered_typed (relayRows_typed K q p j) i)) =
    (π).map (ofRegion (dispatchEntered_typed (relayRows_typed 0 q p 0) (collapse i)))
  rw [dispatchEntered_arrow (relayRows_typed K q p j) i,
    dispatchEntered_arrow (relayRows_typed 0 q p 0) (collapse i),
    dispatchLoop_arrow (relayRows_typed K q p j), dispatchLoop_arrow (relayRows_typed 0 q p 0),
    relay_step, relay_step]
  obtain ⟨state, block, -⟩ := partial_fold_feedback false State State K (relayState K q j)
    (fanBlock K p) (relayState 0 q 0) (fanBlock 0 p) (relay_row K q j) (fan_block K p)
  refine Fin.cases ?_ (fun i => ?_) i
  · have left : injArr (K + 1) 0 = sumInl (Φ := signature.Instr) State (States K) := injArr_zero K
    have right : injArr 1 (collapse (0 : Fin (K + 2))) = sumInl (Φ := signature.Instr) State (States 0) :=
      injArr_zero 0
    rw [left, right]
    exact state
  · have left : injArr (K + 1) i.succ = injArr K i ≫ sumInr (Φ := signature.Instr) State (States K) :=
      injArr_succ K i
    have right : injArr 1 (collapse i.succ) = sumInr (Φ := signature.Instr) State (States 0) :=
      (injArr_succ 0 0).trans ((congrArg (· ≫ (S).inr 0) injArr_base).trans (Category.id_comp _))
    have fold := inj_fold K i
    have e : (π).map (injArr (K + 1) i.succ ≫
          iterate (blockStep State (phaseType State K) (relayState K q j) (fanBlock K p))) =
        (π).map (sumInr State State ≫ iterate (blockStep State State (relayState 0 q 0) (fanBlock 0 p))) := by
      rw [left, Category.assoc, Functor.map_comp, block, ← Functor.map_comp, reassoc_of% fold]
    rw [right]
    exact e

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
