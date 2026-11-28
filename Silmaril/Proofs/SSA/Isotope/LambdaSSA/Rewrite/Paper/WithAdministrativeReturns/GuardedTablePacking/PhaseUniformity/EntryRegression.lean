module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.EntrySplit
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.EntryPoint

/-! # Split states: completeness at the original entries, and the regression -/

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

variable {K K' : Nat} {r r' : Region signature.Instr} {t : Bool → LTable K} {x : Bool → Fin (K + 1)}
  {t' : Bool → LTable K'} {x' : Bool → Fin (K' + 1)}

/-- Loops that are literal sources at each constant are equal exactly
when their sources are equal at each constant. -/
theorem pointed_iff_sources (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hp : Pointed r t x) (hp' : Pointed r' t' x') :
    Eqv false [State] r r' [Bit] ↔
      ∀ q, Eqv false [State] ((t q).entered (x q)) ((t' q).entered (x' q)) [Bit] :=
  ⟨fun e q => TableModel.pointed_sources h h' hp hp'
      (Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _) q,
    pointed_eqv h h' hp hp'⟩

/-- And exactly when they are valid in every supported model. -/
theorem pointed_complete (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hp : Pointed r t x) (hp' : Pointed r' t' x') :
    Eqv false [State] r r' [Bit] ↔ Valid h.hasType h'.hasType :=
  ⟨fun e => Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _,
    fun v => pointed_eqv h h' hp hp' (TableModel.pointed_sources h h' hp hp' v)⟩

end Complete

/-! ## Regression -/

theorem turn_source (l₁ l₂ : Bool) :
    entrySource (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct = turnSource false l₁ l₂ :=
  congrArg (LTable.mk fun _ => l₁) (funext fun j => funext fun a => funext fun b => by
    refine Fin.cases ?_ (fun j => ?_) j
    · cases a
      · exact congrArg (LTree.ask b l₂) (funext fun a' => funext fun b' => by cases a' <;> cases b' <;> rfl)
      · cases b <;> rfl
    · have j0 : j = 0 := Fin.eq_zero j
      subst j0
      cases a
      · exact congrArg (LTree.ask b l₂) (funext fun a' => funext fun b' => by cases a' <;> cases b' <;> rfl)
      · cases b <;> rfl)

theorem turn_nest (frozen l₁ l₂ : Bool) :
    (turnSource frozen l₁ l₂).toTable =
      TreeTable.nest (K := 1) 2
        (Router.ofLabels (turnExplicitLabel l₁ l₂) (turnExplicitAct frozen)).toTrees := by
  have progs : (turnSource frozen l₁ l₂).toTable.prog =
      (TreeTable.nest (K := 1) 2
        (Router.ofLabels (turnExplicitLabel l₁ l₂) (turnExplicitAct frozen)).toTrees).prog := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · have j0 : j = 0 := Fin.eq_zero j
      subst j0
      rfl
  have kids : (turnSource frozen l₁ l₂).toTable.kids =
      (TreeTable.nest (K := 1) 2
        (Router.ofLabels (turnExplicitLabel l₁ l₂) (turnExplicitAct frozen)).toTrees).kids := by
    funext j a b
    refine Fin.cases ?_ (fun j => ?_) j
    · cases frozen <;> cases a <;> cases b <;> first
        | rfl
        | (refine congrArg (Tree.ask _ _) (funext fun a' => funext fun b' => ?_)
           cases a' <;> cases b' <;> rfl)
    · have j0 : j = 0 := Fin.eq_zero j
      subst j0
      cases frozen <;> cases a <;> cases b <;> first
        | rfl
        | (refine congrArg (Tree.ask _ _) (funext fun a' => funext fun b' => ?_)
           cases a' <;> cases b' <;> rfl)
  exact (congrArg (fun k => TreeTable.mk (turnSource frozen l₁ l₂).toTable.prog k) kids).trans
    (congrArg (fun p => TreeTable.mk p _) progs)

theorem turn_forward (frozen l₁ l₂ : Bool) :
    (Router.ofLabels (turnExplicitLabel l₁ l₂) (turnExplicitAct frozen)).Forward 2 := by
  intro k hk a b
  match k, hk with
  | 0, _ => cases frozen <;> cases a <;> cases b <;> first | exact True.intro | (show (_ : Nat) < _; decide)
  | 1, _ => cases frozen <;> cases a <;> cases b <;> first | exact True.intro | (show (_ : Nat) < _; decide)
  | 2, hk => exact absurd hk (by decide)
  | 3, hk => exact absurd hk (by decide)

/-- The written split table equals the table with its second requests
as explicit states, at both copies. -/
theorem turn_eqv_explicit (frozen l₁ l₂ : Bool) (i : Fin 2) :
    Eqv false [State] ((turnSource frozen l₁ l₂).entered i)
      ((Router.ofLabels (turnExplicitLabel l₁ l₂) (turnExplicitAct frozen)).entered i.succ.succ) [Bit] := by
  show Eqv false [State] ((turnSource frozen l₁ l₂).toTable.entered i) _ [Bit]
  rw [turn_nest]
  exact router_nest_eqv (K := 1) 2 _ (turn_forward frozen l₁ l₂) i

theorem cap_turn_nest (l₁ l₂ : Bool) :
    (capSource (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).toTable =
      TreeTable.nest (K := 0) 2 (Router.ofLabels (selExplicitLabel l₁ l₂) capTurnAct).toTrees := by
  have progs : (capSource (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).toTable.prog =
      (TreeTable.nest (K := 0) 2 (Router.ofLabels (selExplicitLabel l₁ l₂) capTurnAct).toTrees).prog := by
    funext j
    have j0 : j = 0 := Fin.eq_zero j
    subst j0
    rfl
  have kids : (capSource (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).toTable.kids =
      (TreeTable.nest (K := 0) 2 (Router.ofLabels (selExplicitLabel l₁ l₂) capTurnAct).toTrees).kids := by
    funext j a b
    have j0 : j = 0 := Fin.eq_zero j
    subst j0
    cases a <;> cases b <;> first
      | rfl
      | (refine congrArg (Tree.ask _ _) (funext fun a' => funext fun b' => ?_)
         cases a' <;> cases b' <;> rfl)
  exact (congrArg (fun k => TreeTable.mk (capSource (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).toTable.prog k)
    kids).trans (congrArg (fun p => TreeTable.mk p _) progs)

theorem cap_turn_forward (l₁ l₂ : Bool) : (Router.ofLabels (selExplicitLabel l₁ l₂) capTurnAct).Forward 2 := by
  intro k hk a b
  match k, hk with
  | 0, _ => cases a <;> cases b <;> first | exact True.intro | (show (_ : Nat) < _; decide)
  | 1, _ => cases a <;> cases b <;> first | exact True.intro | (show (_ : Nat) < _; decide)
  | 2, hk => exact absurd hk (by decide)

theorem cap_turn_explicit (l₁ l₂ : Bool) :
    Eqv false [State] ((capSource (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).entered 0)
      ((Router.ofLabels (selExplicitLabel l₁ l₂) capTurnAct).entered 2) [Bit] := by
  show Eqv false [State] ((capSource (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).toTable.entered 0) _ [Bit]
  rw [cap_turn_nest]
  exact router_nest_eqv (K := 0) 2 _ (cap_turn_forward l₁ l₂) 0

/-- Keeping the entry state is not keeping the first reply's payload:
with a repeat that negates the Bit, the two tables differ at the entry. -/
theorem entry_ne_cap (l₁ l₂ : Bool) :
    ¬ Eqv false [State] ((entryRouter (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).entered 0)
      ((capRouter (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).entered 0) [Bit] := fun e => by
  have src := (pointed_iff_sources ((entryRouter (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).entered_typed 0)
    ((capRouter (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).entered_typed 0)
    (entry_pointed (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct 0)
    (pointed_of_eqv ((capRouter (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).entered_typed 0)
      (capSource (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct) 0 (cap_table_eqv _ _ _ 0))).1 e false
  rw [turn_source] at src
  obtain ⟨R, -, ha, r⟩ := (Router.labels_eqv_iff _ _ _ _ _ _).1
    (((turn_eqv_explicit false l₁ l₂ 0).symm.trans src).trans (cap_turn_explicit l₁ l₂))
  have s : R 0 1 := (ha 2 2 r false true).2
  exact Bool.false_ne_true (ha 0 1 s false false)

/-- After a repeat the kept Bit is the Bit the repeat carried, not the
first state: the table differs from the frozen split table. -/
theorem entry_ne_frozen (l₁ l₂ : Bool) :
    ¬ Eqv false [State] ((entryRouter (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).entered 0)
      (frozenCase l₁ l₂) [Bit] := fun e => by
  have src := (pointed_iff_sources ((entryRouter (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct).entered_typed 0)
    (frozenCase_typed l₁ l₂) (entry_pointed (fun _ : Fin 1 => l₁) (fun _ => l₂) turnAct 0)
    (case_pointed (fun _ => turnSource true l₁ l₂) turnCopy)).1 e false
  rw [turn_source] at src
  obtain ⟨R, -, ha, r⟩ := (Router.labels_eqv_iff _ _ _ _ _ _).1
    (((turn_eqv_explicit false l₁ l₂ 0).symm.trans src).trans (turn_eqv_explicit true l₁ l₂ 0))
  have s : R 3 2 := (ha 2 2 r true false).2
  have s' : R 1 0 := (ha 3 2 s false false).2
  exact Bool.false_ne_true (ha 1 0 s' false false).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
