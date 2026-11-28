module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Quotient.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.PairTables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Completion

/-! # A surjective class map between tables identifies their loops -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate sumIso sumInl sumInr phaseInj phaseInj_base phaseInj_zero
  phaseInj_succ classFold phaseInj_classFold)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open SingletonPhases (system)

local notation "S" => system (Φ := signature.Instr) State
local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false

/-- The constructor entry at state `i` is phase `i`. -/
theorem injArr_phase : ∀ (K : Nat) (i : Fin (K + 1)), injArr K i = phaseInj (Φ := signature.Instr) State K i
  | 0, i => by
    have i0 : i = 0 := Fin.eq_zero i
    subst i0
    exact injArr_base.trans (phaseInj_base (Φ := signature.Instr) State).symm
  | K + 1, i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (injArr_zero K).trans (phaseInj_zero (Φ := signature.Instr) State K).symm
    · exact (injArr_succ K j).trans
        ((congrArg (· ≫ sumInr (Φ := signature.Instr) State (States K)) (injArr_phase K j)).trans
          (phaseInj_succ (Φ := signature.Instr) State K j).symm)

variable {K K' : Nat}

theorem class_inj (cls : Fin (K + 1) → Fin (K' + 1)) (i : Fin (K + 1)) :
    injArr K i ≫ classFold (Φ := signature.Instr) State cls = injArr K' (cls i) := by
  rw [injArr_phase, injArr_phase]
  exact phaseInj_classFold (Φ := signature.Instr) State cls i

theorem row_class (f : ofType (Φ := signature.Instr) (States K) ⟶ ofType (States K'))
    (p : Program) (j : Fin (K + 1)) (c : Fin (K' + 1)) (h : injArr K j ≫ f = injArr K' c) :
    (ofRegion (row_typed K p j) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) f =
      ofRegion (row_typed K' p c) ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom := by
  have m : coprod.map (𝟙 (ofType (Φ := signature.Instr) Bit)) (injArr K j) ≫ coprod.map (𝟙 _) f =
      coprod.map (𝟙 _) (injArr K' c) := by
    rw [coprod.map_map, Category.id_comp, h]
  exact (congrArg (· ≫ coprod.map (𝟙 _) f) (row_sum K p j)).trans
    ((Category.assoc _ _ _).trans ((congrArg (stepP p ≫ ·) m).trans (row_sum K' p c).symm))

variable (t : Table K) (t' : Table K') (cls : Fin (K + 1) → Fin (K' + 1))
  (hprog : ∀ i, t.prog i = t'.prog (cls i)) (hnext : ∀ i, cls (t.next i) = t'.next (cls i))

include hprog hnext in
/-- The one overall square: the class map is a simulation of `t` onto `t'`. -/
theorem class_square :
    (ofRegion t.step_typed ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) (classFold State cls) =
      classFold State cls ≫ (ofRegion t'.step_typed ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom) := by
  apply inj_ext K
  intro i
  have rows : injArr K i ≫ ofRegion t.step_typed = ofRegion (row_typed K (t.prog i) (t.next i)) :=
    inj_dispatch K (fun i => row_typed K (t.prog i) (t.next i)) i
  have rows' : injArr K' (cls i) ≫ ofRegion t'.step_typed =
      ofRegion (row_typed K' (t'.prog (cls i)) (t'.next (cls i))) :=
    inj_dispatch K' (fun i => row_typed K' (t'.prog i) (t'.next i)) (cls i)
  have row := row_class (classFold State cls) (t'.prog (cls i)) (t.next i) (t'.next (cls i))
    ((class_inj cls (t.next i)).trans (congrArg (injArr K') (hnext i)))
  rw [hprog i] at rows
  exact glue _ _ _ _ _ _ _ _ _ _ rows rows' (class_inj cls i) row

theorem loop_arrow : ofRegion t.loop_typed =
    iterate (ofRegion t.step_typed ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) :=
  (iterate_exact t.step_typed).symm

/-- Onto at least two states. -/
theorem class_eqv {K m : Nat} (t : Table K) (t' : Table (m + 1)) (cls : Fin (K + 1) → Fin (m + 2))
    (surj : Function.Surjective cls) (hprog : ∀ i, t.prog i = t'.prog (cls i))
    (hnext : ∀ i, cls (t.next i) = t'.next (cls i)) (i : Fin (K + 1)) :
    Eqv false [State] (t.entered i) (t'.entered (cls i)) [Bit] := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (t.entered_typed i) (t'.entered_typed (cls i))).1
  change (π).map (ofRegion (t.entered_typed i)) = (π).map (ofRegion (t'.entered_typed (cls i)))
  rw [entered_arrow t i, entered_arrow t' (cls i), loop_arrow t, loop_arrow t']
  have loops := class_uniform false State cls surj _ _ (class_square t t' cls hprog hnext)
  have at_i := class_inj cls i
  calc
    _ = (π).map (injArr K i) ≫ (π).map (classFold State cls ≫ iterate _) :=
      ((π).map_comp _ _).trans (congrArg ((π).map (injArr K i) ≫ ·) loops)
    _ = (π).map ((injArr K i ≫ classFold State cls) ≫ iterate _) := by
      rw [← Functor.map_comp, Category.assoc]
    _ = _ := by rw [at_i]

/-- Any number of target states. With one, both tables run one program. -/
theorem quotient_eqv : ∀ {K K' : Nat} (t : Table K) (t' : Table K') (cls : Fin (K + 1) → Fin (K' + 1)),
    Function.Surjective cls → (∀ i, t.prog i = t'.prog (cls i)) →
    (∀ i, cls (t.next i) = t'.next (cls i)) → ∀ i : Fin (K + 1),
    Eqv false [State] (t.entered i) (t'.entered (cls i)) [Bit]
  | _, 0, t, t', cls, _, hprog, _, i =>
    (single_eqv t (t'.prog 0) (fun j => (hprog j).trans (congrArg t'.prog (Fin.eq_zero _))) i).trans
      (single_eqv t' (t'.prog 0) (fun j => congrArg t'.prog (Fin.eq_zero j)) (cls i)).symm
  | _, _ + 1, t, t', cls, surj, hprog, hnext, i => class_eqv t t' cls surj hprog hnext i

theorem unevenClass_surjective : Function.Surjective unevenClass := by
  intro c
  match c with
  | 0 => exact ⟨1, rfl⟩
  | 1 => exact ⟨3, rfl⟩
  | 2 => exact ⟨0, rfl⟩

theorem uneven_prog (qa qb qc : Program) (i : Fin 6) :
    (Table.uneven qa qb qc).prog i = (Table.cycle3 qa qb qc).prog (unevenClass i) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl

theorem uneven_next (qa qb qc : Program) (i : Fin 6) :
    unevenClass ((Table.uneven qa qb qc).next i) = (Table.cycle3 qa qb qc).next (unevenClass i) := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl

theorem uneven_eqv (qa qb qc : Program) (i : Fin 6) :
    Eqv false [State] ((Table.uneven qa qb qc).entered i)
      ((Table.cycle3 qa qb qc).entered (unevenClass i)) [Bit] :=
  class_eqv _ _ unevenClass unevenClass_surjective (uneven_prog qa qb qc) (uneven_next qa qb qc) i

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
