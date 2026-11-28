module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.EnvTables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.EntryRegression
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.BitFragment.Recursive.Thms

/-! # Written rows with an environment: normal forms and the regression -/

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
open Silmaril.DeBruijn (lift)
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Code Normal)

/-! ## Written code with lets, by its normal form -/

theorem push_id {n : Nat} : Paper.WithAdministrativeReturns.BitFragment.Recursive.push (id : Fin n → Fin n) = id := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;> rfl

theorem envCode_region : ∀ {n : Nat} (c : Normal 2 n), (envCode c).region id = c.region
  | _, .ret _ _ => rfl
  | _, .ask l s left right => by
    show Region.case _ ((envCode left).region (Paper.WithAdministrativeReturns.BitFragment.Recursive.push id))
      ((envCode right).region (Paper.WithAdministrativeReturns.BitFragment.Recursive.push id)) = _
    rw [push_id, envCode_region left, envCode_region right]
    rfl

/-- The code of the normal form of a written program. -/
abbrev normalProgram (p : Program) : Program := envCode (p.normalize id)

/-- The packed written program is the packed code of its normal form, in
the quotient. This is the existing normalization of written code. -/
theorem normal_packed (p : Program) : QLit p.typed.packExits = QLit (normalProgram p).typed.packExits := by
  apply (Paper.Extension.Singleton.ofRegion_packExits_eq_iff (Seed := N) p.typed (normalProgram p).typed).2
  have e := Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.ofTablePacking false
    (Paper.WithAdministrativeReturns.WithGuardedTablePacking.ofAdministrativeReturns false
      (Paper.WithAdministrativeReturns.BitFragment.Recursive.Code.normalize_eqv p id))
  rw [← envCode_region] at e
  exact e

/-- So a row of written code is the row of its normal form. -/
theorem normal_row (K : Nat) (p : Program) (a : Bool → Bool → Act K) :
    QLit (routerRow_typed K p a) = QLit (routerRow_typed K (normalProgram p) a) := by
  have split : ∀ p : Program, QLit (routerRow_typed K p a) =
      (QLit unpack_typed ≫ QLit p.typed.packExits) ≫ QLit (routerRoute_typed K a) := fun p =>
    (q_comp (step_typed p) (routerRoute_typed K a)).trans
      (congrArg (· ≫ QLit (routerRoute_typed K a)) (q_comp unpack_typed p.typed.packExits))
  exact (split p).trans ((congrArg (fun f => (QLit unpack_typed ≫ f) ≫ QLit (routerRoute_typed K a))
    (normal_packed p)).trans (split (normalProgram p)).symm)

/-- A table of written code whose normal forms are rows of the fragment
equals the table of those rows at every entry. -/
theorem normal_table {K : Nat} (t : Router K) (row : Fin (K + 1) → EnvRow)
    (h : ∀ i, (t.prog i).normalize id = (row i).normal) (j : Fin (K + 1)) :
    Eqv false [State] (t.entered j) ((envRouter row t.act).entered j) [Bit] :=
  dispatch_rows_eqv t.rows_typed (envRouter row t.act).rows_typed
    (fun i => (normal_row K (t.prog i) (t.act i)).trans
      (congrArg (fun n : Normal 2 1 => QLit (routerRow_typed K (envCode n) (t.act i))) (h i))) j

/-- So it is the split table of literal request trees at each constant. -/
theorem normal_pointed {K : Nat} (t : Router K) (row : Fin (K + 1) → EnvRow)
    (h : ∀ i, (t.prog i).normalize id = (row i).normal) (j : Fin (K + 1)) :
    Pointed (t.entered j) (fun _ => envSource row t.act) (splitIdx j) := fun q =>
  (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q (t.entered_typed j))
    (constEntry_typed q ((envSource row t.act).entered_typed (splitIdx j q)))).1
    ((q_const q (t.entered_typed j)).trans
      ((congrArg (QLit (const_typed q) ≫ ·)
        ((Paper.Extension.Singleton.ofRegion_eq_iff N (t.entered_typed j)
          ((envRouter row t.act).entered_typed j)).2 (normal_table t row h j))).trans
        ((q_const q ((envRouter row t.act).entered_typed j)).symm.trans
          ((Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (env_pointed row t.act j q)))))

/-! ## Regression: which slot the final action reads -/

theorem slot_nest (frozen l₁ l₂ : Bool) (sL sR : Fin 3) (hf : frozen = false) :
    (envSource (fun _ : Fin 1 => slotRow l₁ l₂ sL sR) turnAct).toTable =
      TreeTable.nest (K := 1) 4 (Router.ofLabels (slotLabel l₁ l₂) (slotAct frozen sL sR)).toTrees := by
  subst hf
  have progs : (envSource (fun _ : Fin 1 => slotRow l₁ l₂ sL sR) turnAct).toTable.prog =
      (TreeTable.nest (K := 1) 4 (Router.ofLabels (slotLabel l₁ l₂) (slotAct false sL sR)).toTrees).prog := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · have j0 : j = 0 := Fin.eq_zero j
      subst j0
      rfl
  have kids : (envSource (fun _ : Fin 1 => slotRow l₁ l₂ sL sR) turnAct).toTable.kids =
      (TreeTable.nest (K := 1) 4 (Router.ofLabels (slotLabel l₁ l₂) (slotAct false sL sR)).toTrees).kids := by
    funext j a b
    refine Fin.cases ?_ (fun j => ?_) j
    · cases a <;> cases b <;> first
        | rfl
        | (refine congrArg (Tree.ask _ _) (funext fun a' => funext fun b' => ?_)
           cases a' <;> cases b' <;> rfl)
    · have j0 : j = 0 := Fin.eq_zero j
      subst j0
      cases a <;> cases b <;> first
        | rfl
        | (refine congrArg (Tree.ask _ _) (funext fun a' => funext fun b' => ?_)
           cases a' <;> cases b' <;> rfl)
  exact (congrArg (fun k => TreeTable.mk
    (envSource (fun _ : Fin 1 => slotRow l₁ l₂ sL sR) turnAct).toTable.prog k) kids).trans
    (congrArg (fun p => TreeTable.mk p _) progs)

theorem slot_forward (frozen l₁ l₂ : Bool) (sL sR : Fin 3) :
    (Router.ofLabels (slotLabel l₁ l₂) (slotAct frozen sL sR)).Forward 4 := by
  intro k hk a b
  match k, hk with
  | 0, _ => cases a <;> exact True.intro
  | 1, _ => cases a <;> exact True.intro
  | 2, _ => cases a <;> exact True.intro
  | 3, _ => cases a <;> exact True.intro
  | 4, hk => exact absurd hk (by decide)
  | 5, hk => exact absurd hk (by decide)

/-- The split table of the row equals the table with its second requests
as explicit states, at both copies. -/
theorem slot_eqv_explicit (l₁ l₂ : Bool) (sL sR : Fin 3) (i : Fin 2) :
    Eqv false [State] ((envSource (fun _ : Fin 1 => slotRow l₁ l₂ sL sR) turnAct).entered i)
      ((Router.ofLabels (slotLabel l₁ l₂) (slotAct false sL sR)).entered i.succ.succ.succ.succ) [Bit] := by
  show Eqv false [State] ((envSource (fun _ : Fin 1 => slotRow l₁ l₂ sL sR) turnAct).toTable.entered i) _ [Bit]
  rw [slot_nest false l₁ l₂ sL sR rfl]
  exact router_nest_eqv (K := 1) 4 _ (slot_forward false l₁ l₂ sL sR) i

theorem pick_inj : ∀ s s' : Fin 3, (∀ y' y c, pick s y' y c = pick s' y' y c) → s = s' := by
  decide +kernel

/-- Two such rows give equal loops exactly when their final actions read
the same slots. -/
theorem slot_eqv_iff (l₁ l₂ : Bool) (sL sR sL' sR' : Fin 3) :
    Eqv false [State] ((slotRouter l₁ l₂ sL sR).entered 0) ((slotRouter l₁ l₂ sL' sR').entered 0) [Bit] ↔
      sL = sL' ∧ sR = sR' := by
  constructor
  · intro e
    have src := (pointed_iff_sources ((slotRouter l₁ l₂ sL sR).entered_typed 0)
      ((slotRouter l₁ l₂ sL' sR').entered_typed 0)
      (env_pointed (fun _ : Fin 1 => slotRow l₁ l₂ sL sR) turnAct 0)
      (env_pointed (fun _ : Fin 1 => slotRow l₁ l₂ sL' sR') turnAct 0)).1 e
    have bis : ∀ q : Bool, ∃ R : Fin 6 → Fin 6 → Prop,
        (∀ x y, R x y → ∀ tag pl, Act.Rel R (slotAct false sL sR x tag pl) (slotAct false sL' sR' y tag pl)) ∧
        R (slotCopy q) (slotCopy q) := fun q => by
      obtain ⟨R, -, ha, r⟩ := (Router.labels_eqv_iff _ _ _ _ _ _).1
        (((slot_eqv_explicit l₁ l₂ sL sR (splitIdx (K := 0) 0 q)).symm.trans (src q)).trans
          (slot_eqv_explicit l₁ l₂ sL' sR' (splitIdx (K := 0) 0 q)))
      refine ⟨R, ha, ?_⟩
      cases q <;> exact r
    have rd : ∀ (x : Bool) (y' y c : Bool),
        pick (match x with | false => sL | true => sR) y' y c =
          pick (match x with | false => sL' | true => sR') y' y c := fun x y' y c => by
      obtain ⟨R, ha, r⟩ := bis c
      cases c <;> cases y <;> cases x
      all_goals first
        | exact ha _ _ (ha 4 4 r false false).2 false y'
        | exact ha _ _ (ha 4 4 r false false).2 true y'
        | exact ha _ _ (ha 4 4 r false true).2 false y'
        | exact ha _ _ (ha 4 4 r false true).2 true y'
        | exact ha _ _ (ha 5 5 r false false).2 false y'
        | exact ha _ _ (ha 5 5 r false false).2 true y'
        | exact ha _ _ (ha 5 5 r false true).2 false y'
        | exact ha _ _ (ha 5 5 r false true).2 true y'
    exact ⟨pick_inj sL sL' (rd false), pick_inj sR sR' (rd true)⟩
  · rintro ⟨rfl, rfl⟩
    exact Paper.Extension.Eqv.refl ((slotRouter l₁ l₂ sL sR).entered_typed 0).hasType

/-- After a repeat the entry slot holds the Bit the repeat carried: the
row that reads both its entry state and its first reply differs from the
frozen table, whose repeats stay in their copy. -/
theorem slot_ne_frozen (l₁ l₂ : Bool) :
    ¬ Eqv false [State] ((slotRouter l₁ l₂ 2 1).entered 0) (slotFrozen l₁ l₂ 2 1) [Bit] := fun e => by
  have src := (pointed_iff_sources ((slotRouter l₁ l₂ 2 1).entered_typed 0) (slotFrozen_typed l₁ l₂ 2 1)
    (env_pointed (fun _ : Fin 1 => slotRow l₁ l₂ 2 1) turnAct 0)
    (case_pointed (fun _ => leafTable (slotLabel l₁ l₂) (slotAct true 2 1)) slotCopy)).1 e false
  have right : Eqv false [State] ((leafTable (slotLabel l₁ l₂) (slotAct true 2 1)).entered 4)
      ((Router.ofLabels (slotLabel l₁ l₂) (slotAct true 2 1)).entered 4) [Bit] :=
    Paper.Extension.Eqv.refl ((Router.ofLabels (slotLabel l₁ l₂) (slotAct true 2 1)).entered_typed 4).hasType
  obtain ⟨R, -, ha, r⟩ := (Router.labels_eqv_iff _ _ _ _ _ _).1
    (((slot_eqv_explicit l₁ l₂ 2 1 0).symm.trans src).trans right)
  have s : R 5 4 := (ha 4 4 r true false).2
  have s' : R 2 0 := (ha 5 4 s false false).2
  exact Bool.false_ne_true (ha 2 0 s' false false).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
