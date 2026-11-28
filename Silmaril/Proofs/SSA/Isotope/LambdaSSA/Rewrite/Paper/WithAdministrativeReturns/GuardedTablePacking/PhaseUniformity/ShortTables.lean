module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Short.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Composite.Padding.Thms
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.PairTables

/-! # The table with two and three duplicates collapses from one overall square -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step pair_fold_short)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate sumIso sumInl sumInr pairFold pairFold_inr_inl
  pairFold_inr_inr shortFold)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open SingletonPhases (system)

local notation "S" => system (Φ := signature.Instr) State
local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false

/-- The class fold on the five states. -/
@[expose] noncomputable def foldShort : ofType (Φ := signature.Instr) (States 4) ⟶ ofType (States 1) :=
  shortFold State State 1

theorem short_b0 : injArr 4 0 ≫ foldShort = injArr 1 1 := by
  have a : injArr 4 0 = sumInl (Φ := signature.Instr) State (States 3) := injArr_zero 3
  rw [a, inj_one]
  exact pairFold_inr_inl (Φ := signature.Instr) State State 1

theorem short_succ (i : Fin 4) : injArr 4 i.succ ≫ foldShort = injArr 1 (pairClass i) := by
  have a : injArr 4 i.succ = injArr 3 i ≫ sumInr (Φ := signature.Instr) State (States 3) := injArr_succ 3 i
  rw [a, Category.assoc]
  exact (congrArg (injArr 3 i ≫ ·) (pairFold_inr_inr (Φ := signature.Instr) State State 1)).trans
    (fold_class i)

theorem short_class (i : Fin 5) : injArr 4 i ≫ foldShort = injArr 1 (shortClass i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact short_b0
  · exact short_succ i

theorem short_aState (d : Fin 2) : injArr 4 (aShort d) ≫ foldShort = injArr 1 0 := by
  refine Fin.cases ?_ (fun d => ?_) d
  · exact short_succ 0
  · exact short_succ 2

theorem short_bState (d : Fin 3) : injArr 4 (bShort d) ≫ foldShort = injArr 1 1 := by
  refine Fin.cases ?_ (fun d => ?_) d
  · exact short_b0
  · refine Fin.cases ?_ (fun d => ?_) d
    · exact short_succ 1
    · exact short_succ 3

theorem relay_fold {K : Nat} (f : ofType (Φ := signature.Instr) (States K) ⟶ ofType (States 1))
    (q : Program) (j₁ j₂ : Fin (K + 1)) (c₁ c₂ : Fin 2)
    (h₁ : injArr K j₁ ≫ f = injArr 1 c₁) (h₂ : injArr K j₂ ≫ f = injArr 1 c₂) :
    (ofRegion (relayRow_typed K q j₁ j₂) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) f =
      ofRegion (relayRow_typed 1 q c₁ c₂) ≫ (sumIso (Φ := signature.Instr) Bit (States 1)).hom := by
  have m : coprod.desc (bitState ≫ injArr K j₁ ≫ coprod.inr) (injArr K j₂ ≫ coprod.inr) ≫
      coprod.map (𝟙 (ofType (Φ := signature.Instr) Bit)) f =
      coprod.desc (bitState ≫ injArr 1 c₁ ≫ coprod.inr) (injArr 1 c₂ ≫ coprod.inr) := by
    apply coprod.hom_ext
    · simp [reassoc_of% h₁]
    · simp [reassoc_of% h₂]
  exact (congrArg (· ≫ coprod.map (𝟙 _) f) (relayRow_sum K q j₁ j₂)).trans
    ((Category.assoc _ _ _).trans ((congrArg (stepP q ≫ ·) m).trans (relayRow_sum 1 q c₁ c₂).symm))

theorem row_fold {K : Nat} (f : ofType (Φ := signature.Instr) (States K) ⟶ ofType (States 1))
    (p : Program) (j : Fin (K + 1)) (c : Fin 2) (h : injArr K j ≫ f = injArr 1 c) :
    (ofRegion (row_typed K p j) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) f =
      ofRegion (row_typed 1 p c) ≫ (sumIso (Φ := signature.Instr) Bit (States 1)).hom := by
  have m : coprod.map (𝟙 (ofType (Φ := signature.Instr) Bit)) (injArr K j) ≫ coprod.map (𝟙 _) f =
      coprod.map (𝟙 _) (injArr 1 c) := by
    rw [coprod.map_map, Category.id_comp, h]
  exact (congrArg (· ≫ coprod.map (𝟙 _) f) (row_sum K p j)).trans
    ((Category.assoc _ _ _).trans ((congrArg (stepP p ≫ ·) m).trans (row_sum 1 p c).symm))

variable (q p : Program) (w : ShortWiring)

/-- The one overall square for the five-state table. -/
theorem short_square :
    (ofRegion (dispatch_typed 4 (shortRows_typed q p w)) ≫ (sumIso (Φ := signature.Instr) Bit (States 4)).hom) ≫
        coprod.map (𝟙 _) foldShort =
      foldShort ≫ (ofRegion (dispatch_typed 1 (relayRows_typed 0 q p 0)) ≫
        (sumIso (Φ := signature.Instr) Bit (States 1)).hom) := by
  have a' : injArr 1 0 ≫ ofRegion (dispatch_typed 1 (relayRows_typed 0 q p 0)) =
      ofRegion (relayRow_typed 1 q 0 1) := inj_dispatch 1 (relayRows_typed 0 q p 0) 0
  have b' : injArr 1 1 ≫ ofRegion (dispatch_typed 1 (relayRows_typed 0 q p 0)) =
      ofRegion (row_typed 1 p 0) := inj_dispatch 1 (relayRows_typed 0 q p 0) 1
  apply inj_ext 4
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · exact glue _ _ _ _ _ _ _ _ _ _ (inj_dispatch 4 (shortRows_typed q p w) 0) b' short_b0
      (row_fold foldShort p _ 0 (short_aState _))
  · refine Fin.cases ?_ (fun i => ?_) i
    · exact glue _ _ _ _ _ _ _ _ _ _ (inj_dispatch 4 (shortRows_typed q p w) 1) a' (short_succ 0)
        (relay_fold foldShort q _ _ 0 1 (short_aState _) (short_bState _))
    · refine Fin.cases ?_ (fun i => ?_) i
      · exact glue _ _ _ _ _ _ _ _ _ _ (inj_dispatch 4 (shortRows_typed q p w) 2) b' (short_succ 1)
          (row_fold foldShort p _ 0 (short_aState _))
      · refine Fin.cases ?_ (fun i => ?_) i
        · exact glue _ _ _ _ _ _ _ _ _ _ (inj_dispatch 4 (shortRows_typed q p w) 3) a' (short_succ 2)
            (relay_fold foldShort q _ _ 0 1 (short_aState _) (short_bState _))
        · have i0 : i = 0 := Fin.eq_zero i
          subst i0
          exact glue _ _ _ _ _ _ _ _ _ _ (inj_dispatch 4 (shortRows_typed q p w) 4) b' (short_succ 3)
            (row_fold foldShort p _ 0 (short_aState _))

/-- The table with two and three duplicates, entered at any state, equals
the two-state relay table entered at the state's class. -/
theorem shortTable_eqv (i : Fin 5) :
    Eqv false [State] (shortTable q p w i) (relayFan 0 q p 0 (shortClass i)) [Bit] := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (shortTable_typed q p w i)
    (relayFan_typed 0 q p 0 (shortClass i))).1
  change (π).map (ofRegion (dispatchEntered_typed (shortRows_typed q p w) i)) =
    (π).map (ofRegion (dispatchEntered_typed (relayRows_typed 0 q p 0) (shortClass i)))
  rw [dispatchEntered_arrow (shortRows_typed q p w) i,
    dispatchEntered_arrow (relayRows_typed 0 q p 0) (shortClass i),
    dispatchLoop_arrow (shortRows_typed q p w), dispatchLoop_arrow (relayRows_typed 0 q p 0)]
  have loops := pair_fold_short false State State 1 _ _ (short_square q p w)
  have cls := short_class i
  calc
    _ = (π).map (injArr 4 i) ≫ (π).map (foldShort ≫ iterate _) :=
      ((π).map_comp _ _).trans (congrArg ((π).map (injArr 4 i) ≫ ·) loops)
    _ = (π).map ((injArr 4 i ≫ foldShort) ≫ iterate _) := by
      rw [← Functor.map_comp, Category.assoc]
    _ = _ := by rw [cls]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
