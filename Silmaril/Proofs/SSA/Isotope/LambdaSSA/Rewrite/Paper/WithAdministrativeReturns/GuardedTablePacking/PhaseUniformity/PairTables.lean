module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Pair.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Composite.Thms
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RelayTables

/-! # A table with both classes duplicated collapses from one overall square -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step pair_fold)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate sumIso sumInl sumInr pairFold pairFold_inl
  pairFold_inr_inl pairFold_inr_inr)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open SingletonPhases (system)

local notation "S" => system (Φ := signature.Instr) State
local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false

/-- The sum of the two class folds on four interleaved states. -/
@[expose] noncomputable def foldPair : ofType (Φ := signature.Instr) (States 3) ⟶ ofType (States 1) :=
  pairFold State State 1

theorem fold_a0 : injArr 3 0 ≫ foldPair = injArr 1 0 :=
  (congrArg (· ≫ foldPair) (injArr_zero 2)).trans
    ((pairFold_inl (Φ := signature.Instr) State State 0).trans (injArr_zero 0).symm)

theorem inj_one : injArr 1 1 = sumInr (Φ := signature.Instr) State State :=
  (injArr_succ 0 0).trans ((congrArg (· ≫ (S).inr 0) injArr_base).trans (Category.id_comp _))

theorem fold_b0 : injArr 3 1 ≫ foldPair = injArr 1 1 := by
  have a : injArr 3 1 = sumInl (Φ := signature.Instr) State (States 1) ≫ sumInr State (States 2) :=
    (injArr_succ 2 0).trans (congrArg (· ≫ (S).inr 2) (injArr_zero 1))
  rw [a, inj_one, Category.assoc]
  exact pairFold_inr_inl (Φ := signature.Instr) State State 0

theorem fold_a1 : injArr 3 2 ≫ foldPair = injArr 1 0 := by
  have a : injArr 3 2 = injArr 1 0 ≫ sumInr (Φ := signature.Instr) State (States 1) ≫ sumInr State (States 2) :=
    (injArr_succ 2 1).trans ((congrArg (· ≫ (S).inr 2) (injArr_succ 1 0)).trans (Category.assoc _ _ _))
  rw [a, Category.assoc, Category.assoc]
  exact (congrArg (injArr 1 0 ≫ ·) (pairFold_inr_inr (Φ := signature.Instr) State State 0)).trans
    (Category.comp_id _)

theorem fold_b1 : injArr 3 3 ≫ foldPair = injArr 1 1 := by
  have a : injArr 3 3 = injArr 1 1 ≫ sumInr (Φ := signature.Instr) State (States 1) ≫ sumInr State (States 2) :=
    (injArr_succ 2 2).trans ((congrArg (· ≫ (S).inr 2) (injArr_succ 1 1)).trans (Category.assoc _ _ _))
  rw [a, Category.assoc, Category.assoc]
  exact (congrArg (injArr 1 1 ≫ ·) (pairFold_inr_inr (Φ := signature.Instr) State State 0)).trans
    (Category.comp_id _)

theorem fold_aState (d : Fin 2) : injArr 3 (aState d) ≫ foldPair = injArr 1 0 := by
  refine Fin.cases ?_ (fun d => ?_) d
  · exact fold_a0
  · exact fold_a1

theorem fold_bState (d : Fin 2) : injArr 3 (bState d) ≫ foldPair = injArr 1 1 := by
  refine Fin.cases ?_ (fun d => ?_) d
  · exact fold_b0
  · exact fold_b1

theorem fold_class (i : Fin 4) : injArr 3 i ≫ foldPair = injArr 1 (pairClass i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact fold_a0
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact fold_b0
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact fold_a1
      · have i0 : i = 0 := Fin.eq_zero i
        subst i0
        exact fold_b1

theorem relay_case (q : Program) (j₁ j₂ : Fin 4) (c₁ c₂ : Fin 2)
    (h₁ : injArr 3 j₁ ≫ foldPair = injArr 1 c₁) (h₂ : injArr 3 j₂ ≫ foldPair = injArr 1 c₂) :
    (ofRegion (relayRow_typed 3 q j₁ j₂) ≫ (sumIso (Φ := signature.Instr) Bit (States 3)).hom) ≫
        coprod.map (𝟙 _) foldPair =
      ofRegion (relayRow_typed 1 q c₁ c₂) ≫ (sumIso (Φ := signature.Instr) Bit (States 1)).hom := by
  have m : coprod.desc (bitState ≫ injArr 3 j₁ ≫ coprod.inr) (injArr 3 j₂ ≫ coprod.inr) ≫
      coprod.map (𝟙 (ofType (Φ := signature.Instr) Bit)) foldPair =
      coprod.desc (bitState ≫ injArr 1 c₁ ≫ coprod.inr) (injArr 1 c₂ ≫ coprod.inr) := by
    apply coprod.hom_ext
    · simp [reassoc_of% h₁]
    · simp [reassoc_of% h₂]
  exact (congrArg (· ≫ coprod.map (𝟙 _) foldPair) (relayRow_sum 3 q j₁ j₂)).trans
    ((Category.assoc _ _ _).trans ((congrArg (stepP q ≫ ·) m).trans (relayRow_sum 1 q c₁ c₂).symm))

theorem row_case (p : Program) (j : Fin 4) (c : Fin 2) (h : injArr 3 j ≫ foldPair = injArr 1 c) :
    (ofRegion (row_typed 3 p j) ≫ (sumIso (Φ := signature.Instr) Bit (States 3)).hom) ≫
        coprod.map (𝟙 _) foldPair =
      ofRegion (row_typed 1 p c) ≫ (sumIso (Φ := signature.Instr) Bit (States 1)).hom := by
  have m : coprod.map (𝟙 (ofType (Φ := signature.Instr) Bit)) (injArr 3 j) ≫ coprod.map (𝟙 _) foldPair =
      coprod.map (𝟙 _) (injArr 1 c) := by
    rw [coprod.map_map, Category.id_comp, h]
  exact (congrArg (· ≫ coprod.map (𝟙 _) foldPair) (row_sum 3 p j)).trans
    ((Category.assoc _ _ _).trans ((congrArg (stepP p ≫ ·) m).trans (row_sum 1 p c).symm))

theorem glue {C : Type*} [Category C] {a b c d e x y : C} (ι : a ⟶ b) (D : b ⟶ c) (s : c ⟶ d)
    (m : d ⟶ e) (f : b ⟶ x) (ι' : a ⟶ x) (D' : x ⟶ y) (s' : y ⟶ e) (ρ : a ⟶ c) (ρ' : a ⟶ y)
    (d₁ : ι ≫ D = ρ) (d₂ : ι' ≫ D' = ρ') (cls : ι ≫ f = ι') (sq : (ρ ≫ s) ≫ m = ρ' ≫ s') :
    ι ≫ (D ≫ s) ≫ m = ι ≫ f ≫ (D' ≫ s') := by
  subst d₁ cls d₂
  simpa only [Category.assoc] using sq

variable (q p : Program) (w : Wiring)

/-- The one overall square: the sum of the class folds is a simulation of
the four-state table onto the two-state relay table. -/
theorem pair_square :
    (ofRegion (dispatch_typed 3 (pairRows_typed q p w)) ≫ (sumIso (Φ := signature.Instr) Bit (States 3)).hom) ≫
        coprod.map (𝟙 _) foldPair =
      foldPair ≫ (ofRegion (dispatch_typed 1 (relayRows_typed 0 q p 0)) ≫
        (sumIso (Φ := signature.Instr) Bit (States 1)).hom) := by
  have a' : injArr 1 0 ≫ ofRegion (dispatch_typed 1 (relayRows_typed 0 q p 0)) =
      ofRegion (relayRow_typed 1 q 0 1) := inj_dispatch 1 (relayRows_typed 0 q p 0) 0
  have b' : injArr 1 1 ≫ ofRegion (dispatch_typed 1 (relayRows_typed 0 q p 0)) =
      ofRegion (row_typed 1 p 0) := inj_dispatch 1 (relayRows_typed 0 q p 0) 1
  apply inj_ext 3
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact glue _ _ _ _ _ _ _ _ _ _ (inj_dispatch 3 (pairRows_typed q p w) 0) a' fold_a0
      (relay_case q _ _ 0 1 (fold_aState _) (fold_bState _))
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact glue _ _ _ _ _ _ _ _ _ _ (inj_dispatch 3 (pairRows_typed q p w) 1) b' fold_b0
        (row_case p _ 0 (fold_aState _))
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact glue _ _ _ _ _ _ _ _ _ _ (inj_dispatch 3 (pairRows_typed q p w) 2) a' fold_a1
          (relay_case q _ _ 0 1 (fold_aState _) (fold_bState _))
      · have i0 : i = 0 := Fin.eq_zero i
        subst i0
        exact glue _ _ _ _ _ _ _ _ _ _ (inj_dispatch 3 (pairRows_typed q p w) 3) b' fold_b1
          (row_case p _ 0 (fold_aState _))

/-- The table with both classes duplicated, entered at any state, equals
the two-state relay table entered at the state's class. -/
theorem pairTable_eqv (i : Fin 4) :
    Eqv false [State] (pairTable q p w i) (relayFan 0 q p 0 (pairClass i)) [Bit] := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (pairTable_typed q p w i)
    (relayFan_typed 0 q p 0 (pairClass i))).1
  change (π).map (ofRegion (dispatchEntered_typed (pairRows_typed q p w) i)) =
    (π).map (ofRegion (dispatchEntered_typed (relayRows_typed 0 q p 0) (pairClass i)))
  rw [dispatchEntered_arrow (pairRows_typed q p w) i,
    dispatchEntered_arrow (relayRows_typed 0 q p 0) (pairClass i),
    dispatchLoop_arrow (pairRows_typed q p w), dispatchLoop_arrow (relayRows_typed 0 q p 0)]
  have loops := pair_fold false 1 State State _ _ (pair_square q p w)
  have cls := fold_class i
  calc
    _ = (π).map (injArr 3 i) ≫ (π).map (foldPair ≫ iterate _) :=
      ((π).map_comp _ _).trans (congrArg ((π).map (injArr 3 i) ≫ ·) loops)
    _ = (π).map ((injArr 3 i ≫ foldPair) ≫ iterate _) := by
      rw [← Functor.map_comp, Category.assoc]
    _ = _ := by rw [cls]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
