module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SilentCycleTables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.SpinPrefix

/-! # Mixed tables of single requests as tables with silent rows -/

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

theorem pure_const_res {K M : Nat} (m : MixRow) {e : Fin 2} (hm : m = .pure e) (a₀ : Bool → Bool → Act K)
    (f : Act K → Act M) (g : Bool) :
    ofRegion (seqValueBranches (const_typed g) (routerRow_typed M m.program fun a b => f (m.act K a₀ a b))) =
      ofRegion (act_typed M (f (a₀ (exitBit e) g))) := by
  subst hm
  exact pure_const M e (fun _ b => f (a₀ (exitBit e) b)) g

theorem poll_label {m : MixRow} {l : Bool} (h : m.pollLabel = some l) : ∃ r, m = .ask r ∧ r.label = l := by
  cases m with
  | ask r => exact ⟨r, rfl, Option.some.inj h⟩
  | pure e => cases h

section Spun

variable {K : Nat} (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
  {cyc : Fin (K + (K + 1) + 1) → Bool} {fuel : Nat} (hcl : Classed row act cyc fuel)

include hcl in
theorem cyc_pure (y : Fin (K + (K + 1) + 1)) (hy : cyc y = true) : ∃ e, row (splitRow y) = .pure e := by
  obtain ⟨z, q, hz, -⟩ := hcl.cyclic y hy
  obtain ⟨e, hm, -⟩ := silent_some hz
  exact ⟨e, hm⟩

include hcl in
/-- A state of `cyc` in the resolved table repeats to its successor. -/
theorem res_hcyc (y : Fin (K + (K + 1) + 1)) (hy : cyc y = true) :
    ofRegion (seqValueBranches (const_typed (splitBit y))
        (((splitRouter (mixRouter row act)).resolved (cutSil (mixSil row act) cyc) fuel).rows_typed y)) =
      ofRegion (act_typed (K + (K + 1))
        (.go (silNext (mixSil row act) y) (splitBit (silNext (mixSil row act) y)))) ∧
      cyc (silNext (mixSil row act) y) = true := by
  obtain ⟨z, q, hz, cz⟩ := hcl.cyclic y hy
  have carried : splitBit z = q := mix_hcar row act y (.go z q) hz
  obtain ⟨e, hm, hA⟩ := silent_some hz
  have rowc := pure_const_res (row (splitRow y)) hm (act (splitRow y))
    (fun a => resolveN (cutSil (mixSil row act) cyc) fuel (redirect a)) (splitBit y)
  have cut : cutSil (mixSil row act) cyc z = none := by
    unfold cutSil
    rw [cz]
  rw [← hA, resolveN_none _ fuel q cut] at rowc
  rw [silNext_eq hz, carried]
  exact ⟨rowc, cz⟩

theorem res_hact (x : Fin (K + (K + 1) + 1)) (a b : Bool) :
    (((splitRouter (mixRouter row act)).resolved (cutSil (mixSil row act) cyc) fuel).act x a b).Carries splitBit :=
  resolve_carries (cutSil (mixSil row act) cyc) splitBit (cut_hcar row act) fuel _ (redirect_carries _)

include hcl in
theorem label_not_cyc (y : Fin (K + (K + 1) + 1)) {l : Bool} (hl : spunLabel row y = some l) : cyc y = false := by
  cases hy : cyc y with
  | false => rfl
  | true =>
    obtain ⟨e, hm⟩ := cyc_pure row act hcl y hy
    obtain ⟨r, hr, -⟩ := poll_label hl
    rw [hm] at hr
    cases hr

include hcl in
/-- A repeat to a silent row carries `false`. -/
theorem spun_tidy : Tidy (spunLabel row) (spunAct row act cyc fuel) := fun i l _ tag pl j q ha hj => by
  have settled := hcl.settled (redirect (act (splitRow i) tag pl))
  unfold spunAct at ha
  cases hr : resolveN (cutSil (mixSil row act) cyc) fuel (redirect (act (splitRow i) tag pl)) with
  | ret c =>
    rw [hr] at ha
    cases ha
  | go z q₀ =>
    rw [hr] at ha settled
    cases ha
    cases hz : cyc j with
    | true => rfl
    | false =>
      obtain ⟨r, hm⟩ := silent_none (cut_none settled hz)
      have lab : spunLabel row j = some r.label := by
        show (row (splitRow j)).pollLabel = _
        rw [hm]
        rfl
      rw [hj] at lab
      cases lab

include hcl in
/-- A mixed table of single requests, entered at a request row with each
constant, is its table of labelled rows and canonical silent rows. -/
theorem spun_pointed (hp : Polled row) (j : Fin (K + 1)) {r : EnvRow} (hj : row j = .ask r) :
    SpinPointed ((mixRouter row act).entered j) (spunLabel row) (spunAct row act cyc fuel) (splitIdx j) :=
  fun q => by
  have lab : spunLabel row (splitIdx j q) = some r.label := by
    show (row (splitRow (splitIdx j q))).pollLabel = _
    rw [splitRow_idx, hj]
    rfl
  have ncyc := label_not_cyc row act hcl (splitIdx j q) lab
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q ((mixRouter row act).entered_typed j))
    (constEntry_typed q ((spunRouter row act cyc fuel).entered_typed (splitIdx j q)))).1
  have fold : QLit ((splitRouter (mixRouter row act)).entered_typed (splitIdx j q)) =
      QLit ((mixRouter row act).entered_typed j) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (router_split_fold (mixRouter row act) j q)
  have res := silent_entered (splitRouter (mixRouter row act)) splitBit (cutSil (mixSil row act) cyc) fuel
    (cut_hsil row act) (cut_hcar row act) (mix_hact row act) (fun x a b => hcl.settled _) (splitIdx j q)
  have dull := dull_entry ((splitRouter (mixRouter row act)).resolved (cutSil (mixSil row act) cyc) fuel)
    splitBit cyc (silNext (mixSil row act)) (res_hact row act) (res_hcyc row act hcl) (splitIdx j q)
  have bit : dullBit cyc splitBit (splitIdx j q) = q := (dullBit_false ncyc).trans (splitBit_idx j q)
  rw [splitBit_idx, bit, res] at dull
  have spun := dulled_spin ((splitRouter (mixRouter row act)).resolved (cutSil (mixSil row act) cyc) fuel) cyc
    (silNext (mixSil row act)) (spunLabel row) (spunAct row act cyc fuel)
    (fun y l hl => by
      obtain ⟨r', hr, rfl⟩ := poll_label hl
      refine ⟨label_not_cyc row act hcl y hl, ?_⟩
      show (row (splitRow y)).program = _
      rw [hr, hp _ r' hr]
      rfl)
    (fun y l hl a b z q' hz => by
      have settled := hcl.settled (redirect ((row (splitRow y)).act K (act (splitRow y)) a b))
      have e : resolveN (cutSil (mixSil row act) cyc) fuel
          (redirect ((row (splitRow y)).act K (act (splitRow y)) a b)) = .go z q' := hz
      rw [e] at settled
      cases cz : cyc z with
      | true => exact .inr rfl
      | false =>
        obtain ⟨r', hm⟩ := silent_none (cut_none settled cz)
        refine .inl ⟨r'.label, ?_⟩
        show (row (splitRow z)).pollLabel = _
        rw [hm]
        rfl)
    (fun y hy => by
      obtain ⟨e, hm⟩ := cyc_pure row act hcl y hy
      refine ⟨?_, (res_hcyc row act hcl y hy).2⟩
      show (row (splitRow y)).pollLabel = _
      rw [hm]
      rfl)
    (fun y l hl a b => by
      obtain ⟨r', hr, -⟩ := poll_label hl
      show dullAct cyc (resolveN _ fuel (redirect (act (splitRow y) a b))) =
        dullAct cyc (resolveN _ fuel (redirect ((row (splitRow y)).act K (act (splitRow y)) a b)))
      rw [ask_act_eq hr])
    (splitIdx j q) lab
  exact (q_const q ((mixRouter row act).entered_typed j)).trans
    ((congrArg (QLit (const_typed q) ≫ ·) fold.symm).trans
      ((((π).map_comp _ _).symm.trans (congrArg (π).map dull)).trans
        (((π).map_comp _ _).trans ((congrArg (QLit (const_typed q) ≫ ·)
          ((Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 spun)).trans
            (q_const q ((spunRouter row act cyc fuel).entered_typed (splitIdx j q))).symm))))

end Spun

/-! ## Completeness -/

section Complete

variable {M M' : Nat} {label : Fin (M + 1) → Option Bool} {act : Fin (M + 1) → Bool → Bool → Act M}
  {label' : Fin (M' + 1) → Option Bool} {act' : Fin (M' + 1) → Bool → Bool → Act M'}
  {r r' : Region signature.Instr} {x : Bool → Fin (M + 1)} {x' : Bool → Fin (M' + 1)}

/-- Two loops whose tables agree at each constant are equal. -/
theorem spin_pointed_eqv (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hp : SpinPointed r label act x) (hp' : SpinPointed r' label' act' x')
    (e : ∀ q, Eqv false [State] ((Router.ofSpin label act).entered (x q))
      ((Router.ofSpin label' act').entered (x' q)) [Bit]) : Eqv false [State] r r' [Bit] := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N h h').1
  have point : ∀ q, QLit (constEntry_typed q h) = QLit (constEntry_typed q h') := fun q =>
    ((Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q h)
      (constEntry_typed q ((Router.ofSpin label act).entered_typed (x q)))).2 (hp q)).trans
      (((q_const q ((Router.ofSpin label act).entered_typed (x q))).trans
        ((congrArg (QLit (const_typed q) ≫ ·)
          ((Paper.Extension.Singleton.ofRegion_eq_iff N ((Router.ofSpin label act).entered_typed (x q))
            ((Router.ofSpin label' act').entered_typed (x' q))).2 (e q))).trans
          (q_const q ((Router.ofSpin label' act').entered_typed (x' q))).symm)).trans
        ((Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q h')
          (constEntry_typed q ((Router.ofSpin label' act').entered_typed (x' q)))).2 (hp' q)).symm)
  exact (congrArg (π).map (state_eta h)).trans
    ((q_case_congr (caseValueBranches (constEntry_typed false h) (constEntry_typed true h)) deadBit_typed
      (caseValueBranches (constEntry_typed false h') (constEntry_typed true h')) deadBit_typed
      (q_case_congr (constEntry_typed false h) (constEntry_typed true h) (constEntry_typed false h')
        (constEntry_typed true h') (point false) (point true)) rfl).trans
      (congrArg (π).map (state_eta h')).symm)

variable (ht : Tidy label act) (ht' : Tidy label' act') (hs : Sighted label act)

include ht ht' hs in
/-- Tidy tables with silent rows, the first of them sighted: the loops
are equal exactly when they are valid in every supported model. -/
theorem spin_pointed_complete (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hp : SpinPointed r label act x) (hp' : SpinPointed r' label' act' x') :
    Eqv false [State] r r' [Bit] ↔ Valid h.hasType h'.hasType :=
  ⟨fun e => Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _,
    fun v => spin_pointed_eqv h h' hp hp' fun q =>
      TableModel.spin_eqv_of_obs label act label' act' ht ht' hs (x q) (x' q) q
        (TableModel.spin_pointed_obs h h' hp hp' v q)⟩

include ht ht' hs in
/-- Equal loops have bisimilar tables at each constant. -/
theorem spin_pointed_bisim (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hp : SpinPointed r label act x) (hp' : SpinPointed r' label' act' x')
    (e : Eqv false [State] r r' [Bit]) (q : Bool) :
    ∃ R, Router.Bisimulation (Router.ofSpin label act) (Router.ofSpin label' act') R ∧ R (x q) (x' q) :=
  ⟨_, TableModel.spin_bisim label act label' act' ht ht' hs, q,
    TableModel.spin_pointed_obs h h' hp hp'
      (Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.valid_of_eqv false e _ _) q⟩

end Complete

theorem spin_pointed_congr {M : Nat} {r r' : Region signature.Instr} {label : Fin (M + 1) → Option Bool}
    {act : Fin (M + 1) → Bool → Bool → Act M} {x : Bool → Fin (M + 1)}
    (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (e : Eqv false [State] r r' [Bit]) (hp : SpinPointed r' label act x) : SpinPointed r label act x := fun q =>
  (Paper.Extension.Eqv.trans
    ((Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q h) (constEntry_typed q h')).1
      ((q_const q h).trans ((congrArg (QLit (const_typed q) ≫ ·)
        ((Paper.Extension.Singleton.ofRegion_eq_iff N h h').2 e)).trans (q_const q h').symm))) (hp q))

/-- Two presentations of the same table: the actions of labelled rows
agree up to which silent row a diverging reply repeats to. -/
theorem spin_router_congr {M : Nat} (label : Fin (M + 1) → Option Bool)
    (act act' : Fin (M + 1) → Bool → Bool → Act M)
    (h : ∀ x l, label x = some l → ∀ a b,
      Act.Rel (fun j j' => j = j' ∨ (label j = none ∧ label j' = none)) (act x a b) (act' x a b))
    (x : Fin (M + 1)) :
    Eqv false [State] ((Router.ofSpin label act).entered x) ((Router.ofSpin label act').entered x) [Bit] :=
  router_bisimulation_eqv (Router.ofSpin label act) (Router.ofSpin label act')
    (fun j j' => j = j' ∨ (label j = none ∧ label j' = none))
    ⟨fun j j' r => by
        show lsProg (label j) = lsProg (label j')
        rcases r with rfl | ⟨hj, hj'⟩
        · rfl
        · rw [hj, hj'],
      fun j j' r a b => by
        show Act.Rel _ (lsAct (label j) j (act j) a b) (lsAct (label j') j' (act' j') a b)
        rcases r with rfl | ⟨hj, hj'⟩
        · cases hl : label j with
          | none => exact ⟨rfl, .inl rfl⟩
          | some l => exact h j l hl a b
        · rw [hj, hj']
          exact ⟨rfl, .inr ⟨hj, hj'⟩⟩⟩ x x (.inl rfl)

/-! ## Regression: a visible reply that leads into a silent cycle -/

theorem veer_classed (l n f : Bool) : Classed (veerRow l) (veerAct n f) veerCyc 0 := by
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

theorem veer_ret_classed (l : Bool) : Classed (veerRow l) veerRet veerCyc 0 := by
  refine ⟨fun y hy => ?_, fun a => ?_⟩
  · match y with
    | 0 => cases hy
    | 1 => exact ⟨_, _, rfl, rfl⟩
    | 2 => cases hy
    | 3 => exact ⟨_, _, rfl, rfl⟩
  · cases a with
    | ret b => exact True.intro
    | go y q =>
      match y with
      | 0 => exact rfl
      | 1 => exact rfl
      | 2 => exact rfl
      | 3 => exact rfl

theorem veer_again_classed (l : Bool) : Classed (veerRow l) veerAgain veerCyc 0 := by
  refine ⟨fun y hy => ?_, fun a => ?_⟩
  · match y with
    | 0 => cases hy
    | 1 => exact ⟨_, _, rfl, rfl⟩
    | 2 => cases hy
    | 3 => exact ⟨_, _, rfl, rfl⟩
  · cases a with
    | ret b => exact True.intro
    | go y q =>
      match y with
      | 0 => exact rfl
      | 1 => exact rfl
      | 2 => exact rfl
      | 3 => exact rfl

theorem veer_polled (l : Bool) : Polled (veerRow l) := fun i r h => by
  match i with
  | 0 =>
    cases h
    rfl
  | 1 => cases h

/-- The right reply returns, so the request row is sighted. -/
theorem veer_sighted (l : Bool) (act : Fin 2 → Bool → Bool → Act 1) (cyc : Fin 4 → Bool)
    (h : ∀ g, act 0 true g = .ret g) : Sighted (spunLabel (veerRow l)) (spunAct (veerRow l) act cyc 0) :=
  fun i l' hi => by
    match i with
    | 0 =>
      refine ⟨true, false, ?_⟩
      show (dullAct cyc (redirect (act 0 true false))).Seen _
      rw [h]
      exact True.intro
    | 1 => cases hi
    | 2 =>
      refine ⟨true, false, ?_⟩
      show (dullAct cyc (redirect (act 0 true false))).Seen _
      rw [h]
      exact True.intro
    | 3 => cases hi

theorem veer_pointed (l : Bool) (act : Fin 2 → Bool → Bool → Act 1) (hcl : Classed (veerRow l) act veerCyc 0) :
    SpinPointed ((mixWritten (veerRow l) act).entered 0) (spunLabel (veerRow l))
      (spunAct (veerRow l) act veerCyc 0) (splitIdx 0) :=
  spin_pointed_congr ((mixWritten (veerRow l) act).entered_typed 0) ((mixRouter (veerRow l) act).entered_typed 0)
    (.paper ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (mix_written_arrow (veerRow l) act 0)))
    (spun_pointed (veerRow l) act hcl (veer_polled l) 0 rfl)

/-- Two presentations of the same divergent continuation: whichever Bit
the reply enters the cycle with, and whether the cycle negates the Bit. -/
theorem veer_eqv (l n f n' f' : Bool) :
    Eqv false [State] ((mixWritten (veerRow l) (veerAct n f)).entered 0)
      ((mixWritten (veerRow l) (veerAct n' f')).entered 0) [Bit] :=
  spin_pointed_eqv ((mixWritten (veerRow l) (veerAct n f)).entered_typed 0)
    ((mixWritten (veerRow l) (veerAct n' f')).entered_typed 0)
    (veer_pointed l _ (veer_classed l n f)) (veer_pointed l _ (veer_classed l n' f'))
    fun q => spin_router_congr (spunLabel (veerRow l)) _ _ (fun x l' hx a b => by
      match x with
      | 0 => cases n <;> cases n' <;> cases a <;> cases b <;> first | exact rfl | exact ⟨rfl, .inr ⟨rfl, rfl⟩⟩
      | 1 => cases hx
      | 2 => cases n <;> cases n' <;> cases a <;> cases b <;> first | exact rfl | exact ⟨rfl, .inr ⟨rfl, rfl⟩⟩
      | 3 => cases hx) (splitIdx 0 q)

/-- A reply that leads into the silent cycle is not a reply that returns. -/
theorem veer_ne_ret (l n f : Bool) :
    ¬ Eqv false [State] ((mixWritten (veerRow l) (veerAct n f)).entered 0)
      ((mixWritten (veerRow l) veerRet).entered 0) [Bit] := fun e => by
  obtain ⟨R, bis, r⟩ := spin_pointed_bisim
    (spun_tidy (veerRow l) (veerAct n f) (veer_classed l n f)) (spun_tidy (veerRow l) veerRet (veer_ret_classed l))
    (veer_sighted l (veerAct n f) veerCyc fun _ => rfl)
    ((mixWritten (veerRow l) (veerAct n f)).entered_typed 0) ((mixWritten (veerRow l) veerRet).entered_typed 0)
    (veer_pointed l _ (veer_classed l n f)) (veer_pointed l _ (veer_ret_classed l)) e false
  exact False.elim (bis.act _ _ r false false)

/-- Nor a reply after which the request is sent again. -/
theorem veer_ne_again (l n f : Bool) :
    ¬ Eqv false [State] ((mixWritten (veerRow l) (veerAct n f)).entered 0)
      ((mixWritten (veerRow l) veerAgain).entered 0) [Bit] := fun e => by
  obtain ⟨R, bis, r⟩ := spin_pointed_bisim
    (spun_tidy (veerRow l) (veerAct n f) (veer_classed l n f))
    (spun_tidy (veerRow l) veerAgain (veer_again_classed l))
    (veer_sighted l (veerAct n f) veerCyc fun _ => rfl)
    ((mixWritten (veerRow l) (veerAct n f)).entered_typed 0) ((mixWritten (veerRow l) veerAgain).entered_typed 0)
    (veer_pointed l _ (veer_classed l n f)) (veer_pointed l _ (veer_again_classed l)) e false
  have step := bis.act _ _ r false false
  have next : R (splitIdx 1 (n != false)) (splitIdx 0 false) := And.right step
  have progs := bis.prog _ _ next
  cases n <;> cases progs

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
