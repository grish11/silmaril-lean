module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.FoldSimulation
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonPhases

/-! # The phase fold is a simulation of a single-program table onto its program -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion phaseType phaseFold sumIso coprod_desc_ofRegion ofRegion_id)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open SingletonPhases (system inl_rep inr_rep)

local notation "S" => system (Φ := signature.Instr) State

set_option backward.isDefEq.respectTransparency false

/-- Enter the state sum at state `j`. -/
noncomputable abbrev injArr (K : Nat) (j : Fin (K + 1)) : ofType (Φ := signature.Instr) State ⟶ ofType (States K) :=
  ofRegion (entry_typed K j)

theorem br_inl {X A B : Ty Empty} {t : Tm signature.Instr} (ht : Tm.BranchValue [X] t A) :
    ofRegion (r := .br 0 (.inl t)) (.br (L := [Silmaril.coprod A B]) rfl (.inl ht)) =
      ofRegion (r := .br 0 t) (.br rfl ht) ≫ (coprod.inl ≫ (sumIso A B).inv) := by
  rw [inl_rep]
  rfl

theorem br_inr {X A B : Ty Empty} {t : Tm signature.Instr} (ht : Tm.BranchValue [X] t B) :
    ofRegion (r := .br 0 (.inr t)) (.br (L := [Silmaril.coprod A B]) rfl (.inr ht)) =
      ofRegion (r := .br 0 t) (.br rfl ht) ≫ (coprod.inr ≫ (sumIso A B).inv) := by
  rw [inr_rep]
  rfl

theorem injArr_base : injArr 0 0 = 𝟙 (ofType (Φ := signature.Instr) State) := ofRegion_id State

theorem injArr_zero (K : Nat) : injArr (K + 1) 0 = (S).inl K :=
  (br_inl (.var rfl)).trans (congrArg (· ≫ (S).inl K) (ofRegion_id State) |>.trans (Category.id_comp _))

theorem injArr_succ (K : Nat) (j : Fin (K + 1)) : injArr (K + 1) j.succ = injArr K j ≫ (S).inr K :=
  br_inr (injTm_typed (.var rfl) K j)

theorem inj_fold : ∀ (K : Nat) (j : Fin (K + 1)), injArr K j ≫ phaseFold (Φ := signature.Instr) State K = 𝟙 _
  | 0, j => by
    have j0 : j = 0 := Fin.eq_zero j
    subst j0
    exact (congrArg (· ≫ phaseFold (Φ := signature.Instr) State 0) injArr_base).trans (Category.id_comp _)
  | K + 1, j => by
    refine Fin.cases ?_ (fun j => ?_) j
    · rw [injArr_zero]
      exact (S).inl_desc K _ _
    · rw [injArr_succ, Category.assoc]
      exact (congrArg (injArr K j ≫ ·) ((S).inr_desc K _ _)).trans (inj_fold K j)

theorem inj_ext : ∀ (K : Nat) {T : Paper.TypeCategory (τ := Ty Empty) signature.Instr} {f g : ofType (States K) ⟶ T},
    (∀ j, injArr K j ≫ f = injArr K j ≫ g) → f = g
  | 0, _, f, g, h => by
    have h0 := h 0
    rwa [injArr_base, Category.id_comp, Category.id_comp] at h0
  | K + 1, _, f, g, h => by
    apply (S).ext K
    · have h0 := h 0
      rwa [injArr_zero] at h0
    · apply inj_ext K
      intro j
      have hj := h j.succ
      rwa [injArr_succ, Category.assoc, Category.assoc] at hj

theorem inj_dispatch {D : Ty Empty} : ∀ (K : Nat) {rows : Fin (K + 1) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [D]) (i : Fin (K + 1)),
    injArr K i ≫ ofRegion (dispatch_typed K h) = ofRegion (h i)
  | 0, _, h, i => by
    have i0 : i = 0 := Fin.eq_zero i
    subst i0
    exact (congrArg (· ≫ ofRegion (h 0)) injArr_base).trans (Category.id_comp _)
  | K + 1, _, h, i => by
    have arrow : ofRegion (dispatch_typed (K + 1) h) =
        (sumIso (Φ := signature.Instr) State (States K)).hom ≫
          coprod.desc (ofRegion (h 0)) (ofRegion (dispatch_typed K (fun i => h i.succ))) :=
      (coprod_desc_ofRegion (h 0) (dispatch_typed K (fun i => h i.succ))).symm
    rw [arrow]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [injArr_zero]
      exact (S).inl_desc K _ _
    · rw [injArr_succ, Category.assoc]
      exact (congrArg (injArr K j ≫ ·) ((S).inr_desc K _ _)).trans (inj_dispatch K (fun i => h i.succ) j)

theorem row_arrow (K : Nat) (p : Program) (j : Fin (K + 1)) :
    ofRegion (row_typed K p j) = ofRegion (step_typed p) ≫ ofRegion (route_typed K j) :=
  (Paper.TypeCategory.ofRegion_comp (step_typed p) (route_typed K j) _).symm

/-- Routing followed by the fold forgets where the repeat goes. -/
theorem route_fold (K : Nat) (j : Fin (K + 1)) :
    ofRegion (route_typed K j) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom ≫
        coprod.map (𝟙 _) (phaseFold State K) =
      (sumIso (Φ := signature.Instr) Bit State).hom := by
  have arrow : ofRegion (route_typed K j) =
      (sumIso (Φ := signature.Instr) Bit State).hom ≫ coprod.desc (ofRegion (ret_typed K)) (ofRegion (goto_typed K j)) :=
    (coprod_desc_ofRegion (ret_typed K) (goto_typed K j)).symm
  have ret : ofRegion (ret_typed K) = coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv :=
    (inl_rep (Φ := signature.Instr) Bit (States K)).symm
  have goto : ofRegion (goto_typed K j) = injArr K j ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
    br_inr (injTm_typed (.var rfl) K j)
  have fold := inj_fold K j
  rw [arrow, ret, goto, Category.assoc]
  conv_rhs => rw [← Category.comp_id (sumIso (Φ := signature.Instr) Bit State).hom]
  congr 1
  apply coprod.hom_ext
  · simp
  · simp [reassoc_of% fold]

/-- The fold is a simulation of a single-program table onto its program,
as an equation of default Paper. -/
theorem single_square {K : Nat} (t : Table K) (p : Program) (single : t.Single p) :
    (ofRegion t.step_typed ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) (phaseFold State K) =
      phaseFold State K ≫ (ofRegion (step_typed p) ≫ (sumIso (Φ := signature.Instr) Bit State).hom) := by
  apply inj_ext K
  intro j
  have fold := inj_fold K j
  have rows : injArr K j ≫ ofRegion t.step_typed = ofRegion (row_typed K (t.prog j) (t.next j)) :=
    inj_dispatch K (fun i => row_typed K (t.prog i) (t.next i)) j
  rw [reassoc_of% fold, Category.assoc, reassoc_of% rows, row_arrow, Category.assoc, route_fold, single j]

theorem single_eqv {K : Nat} (t : Table K) (p : Program) (single : t.Single p) (i : Fin (K + 1)) :
    Eqv false [State] (t.entered i) (loopRegion p) [Bit] :=
  fold_simulation_entered false K t.step_typed (step_typed p) (single_square t p single)
    (entry_typed K i) (inj_fold K i)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
