module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Mixed.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.PartialFold

/-! # Fans collapse onto the two-state table by the partial fold -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate phaseType phaseFold sumIso coprod_desc_ofRegion)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open SingletonPhases (system inl_rep inr_rep)

local notation "S" => system (Φ := signature.Instr) State
local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false

/-- The step of a program at the chosen coproduct. -/
noncomputable abbrev stepP (p : Program) : ofType (Φ := signature.Instr) State ⟶ ofType Bit ⨿ ofType State :=
  ofRegion (step_typed p) ≫ (sumIso (Φ := signature.Instr) Bit State).hom

theorem route_sum (K : Nat) (j : Fin (K + 1)) :
    ofRegion (route_typed K j) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom =
      (sumIso (Φ := signature.Instr) Bit State).hom ≫ coprod.map (𝟙 _) (injArr K j) := by
  have arrow : ofRegion (route_typed K j) =
      (sumIso (Φ := signature.Instr) Bit State).hom ≫ coprod.desc (ofRegion (ret_typed K)) (ofRegion (goto_typed K j)) :=
    (coprod_desc_ofRegion (ret_typed K) (goto_typed K j)).symm
  have ret : ofRegion (ret_typed K) = coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv :=
    (inl_rep (Φ := signature.Instr) Bit (States K)).symm
  have goto : ofRegion (goto_typed K j) =
      injArr K j ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
    br_inr (injTm_typed (.var rfl) K j)
  rw [arrow, ret, goto, Category.assoc]
  congr 1
  apply coprod.hom_ext <;> simp

/-- A row at the chosen coproduct: the program step, then its successor state. -/
theorem row_sum (K : Nat) (p : Program) (j : Fin (K + 1)) :
    ofRegion (row_typed K p j) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom =
      stepP p ≫ coprod.map (𝟙 _) (injArr K j) := by
  rw [row_arrow, Category.assoc, route_sum, Category.assoc]

variable (K : Nat) (q p : Program) (j : Fin (K + 1))

noncomputable abbrev fanState : ofType (Φ := signature.Instr) State ⟶ ofType Bit ⨿ ofType (States K) :=
  stepP q ≫ coprod.map (𝟙 _) (injArr K j)

noncomputable abbrev fanBlock :
    ofType (Φ := signature.Instr) (States K) ⟶ (ofType Bit ⨿ ofType State) ⨿ ofType (States K) :=
  phaseFold State K ≫ stepP p ≫ coprod.inl

/-- The literal fan step is a state row joined with a block. -/
theorem fan_step :
    ofRegion (Table.fan K q p j).step_typed ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom =
      joined State K (fanState K q j) (fanBlock K p) := by
  have rows (i : Fin (K + 2)) :
      injArr (K + 1) i ≫ ofRegion (Table.fan K q p j).step_typed ≫
          (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom =
        stepP ((Table.fan K q p j).prog i) ≫ coprod.map (𝟙 _) (injArr (K + 1) ((Table.fan K q p j).next i)) := by
    rw [← Category.assoc, inj_dispatch (K + 1) (fun i => row_typed (K + 1) ((Table.fan K q p j).prog i)
      ((Table.fan K q p j).next i)) i]
    exact row_sum (K + 1) _ _
  apply (S).ext K
  · have r0 := rows 0
    rw [injArr_zero] at r0
    refine r0.trans ?_
    refine Eq.trans ?_ ((S).inl_desc K _ _).symm
    have m : coprod.map (𝟙 (ofType (Φ := signature.Instr) Bit)) (injArr K j ≫ (S).inr K) =
        coprod.map (𝟙 _) (injArr K j) ≫ coprod.map (𝟙 _) ((S).inr K) := by
      rw [coprod.map_map, Category.id_comp]
    change stepP q ≫ coprod.map (𝟙 _) (injArr (K + 1) j.succ) = _
    rw [injArr_succ, m]
    exact (Category.assoc _ _ _).symm
  · refine Eq.trans ?_ ((S).inr_desc K _ _).symm
    apply inj_ext K
    intro i
    have ri := rows i.succ
    rw [injArr_succ, Category.assoc] at ri
    have fold := inj_fold K i
    refine ri.trans ?_
    change stepP p ≫ coprod.map (𝟙 _) (injArr (K + 1) 0) = _
    rw [injArr_zero]
    simp only [fanBlock, stepP, Category.assoc, coprod.inl_desc, reassoc_of% fold]

theorem fan_entry : fanState K q j ≫ coprod.map (𝟙 _) (phaseFold State K) = fanState 0 q 0 := by
  have fold := inj_fold K j
  have base : injArr 0 0 = 𝟙 (ofType (Φ := signature.Instr) State) := injArr_base
  have m : coprod.map (𝟙 (ofType (Φ := signature.Instr) Bit)) (injArr K j) ≫
      coprod.map (𝟙 _) (phaseFold State K) = coprod.map (𝟙 _) (injArr 0 0) := by
    rw [coprod.map_map, Category.id_comp, fold, base]
  exact (Category.assoc _ _ _).trans (congrArg (stepP q ≫ ·) m)

theorem fan_block : fanBlock K p ≫ coprod.map (𝟙 _) (phaseFold State K) = phaseFold State K ≫ fanBlock 0 p := by
  have e : fanBlock 0 p = stepP p ≫ coprod.inl := Category.id_comp _
  rw [e]
  simp only [fanBlock, Category.assoc, coprod.inl_map, Category.id_comp]
  rfl

theorem fan_loop : ofRegion (Table.fan K q p j).loop_typed = iterate (joined State K (fanState K q j) (fanBlock K p)) := by
  rw [← fan_step]
  exact (iterate_exact (Table.fan K q p j).step_typed).symm

theorem entered_arrow {K : Nat} (t : Table K) (i : Fin (K + 1)) :
    ofRegion (t.entered_typed i) = injArr K i ≫ ofRegion t.loop_typed :=
  (Paper.TypeCategory.ofRegion_comp (entry_typed K i) t.loop_typed (t.entered_typed i)).symm

/-- A fan entered at any state equals the two-state table entered at the
state's class. -/
theorem fan_eqv (i : Fin (K + 2)) :
    Eqv false [State] ((Table.fan K q p j).entered i) ((Table.pingPong q p).entered (collapse i)) [Bit] := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N ((Table.fan K q p j).entered_typed i)
    ((Table.pingPong q p).entered_typed (collapse i))).1
  change (π).map (ofRegion _) = (π).map (ofRegion _)
  rw [entered_arrow, entered_arrow, fan_loop]
  have small : ofRegion (Table.pingPong q p).loop_typed =
      iterate (joined State 0 (fanState 0 q 0) (fanBlock 0 p)) := fan_loop 0 q p 0
  rw [small]
  refine Fin.cases ?_ (fun i => ?_) i
  · have left : injArr (K + 1) 0 = (S).inl K := injArr_zero K
    have right : injArr 1 (collapse (0 : Fin (K + 2))) = (S).inl 0 := injArr_zero 0
    rw [left, right]
    exact partial_state false State K _ _ _ _ (fan_entry K q j) (fan_block K p)
  · have left : injArr (K + 1) i.succ = injArr K i ≫ (S).inr K := injArr_succ K i
    have right : injArr 1 (collapse i.succ) = (S).inr 0 :=
      (injArr_succ 0 0).trans ((congrArg (· ≫ (S).inr 0) injArr_base).trans (Category.id_comp _))
    have fold := inj_fold K i
    rw [left, right, Category.assoc, Functor.map_comp,
      partial_block false State K _ _ _ _ (fan_entry K q j) (fan_block K p), ← Functor.map_comp,
      reassoc_of% fold]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
