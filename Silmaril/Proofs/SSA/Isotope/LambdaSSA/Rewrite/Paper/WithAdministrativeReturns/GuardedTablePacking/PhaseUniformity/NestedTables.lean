module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.NestedRouter

/-! # Mixed tables with nested request rows, as request trees with silent rows -/

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
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Code Normal)

/-! ## Two matched tables that agree on their carried constants -/

theorem matched_const_congr {M : Nat} (c : Fin (M + 1) → Bool)
    {rows₁ rows₂ : Fin (M + 1) → Region signature.Instr}
    (h₁ : ∀ x, ValueBranches [State] (rows₁ x) [Silmaril.coprod Bit (States M)])
    (h₂ : ∀ x, ValueBranches [State] (rows₂ x) [Silmaril.coprod Bit (States M)])
    (m₁ : Matched c h₁) (m₂ : Matched c h₂)
    (rowc : ∀ i, QLit (seqValueBranches (const_typed (c i)) (h₁ i)) =
      QLit (seqValueBranches (const_typed (c i)) (h₂ i))) (x : Fin (M + 1)) :
    QLit (const_typed (c x)) ≫ QLit (dispatchEntered_typed h₁ x) =
      QLit (const_typed (c x)) ≫ QLit (dispatchEntered_typed h₂ x) := by
  have tables := (Paper.Extension.Singleton.ofRegion_eq_iff N
    (dispatchEntered_typed (resetRows_typed c h₁) x) (dispatchEntered_typed (resetRows_typed c h₂) x)).2
    (dispatch_rows_eqv (resetRows_typed c h₁) (resetRows_typed c h₂)
      (fun i => q_reset_congr (c i) (h₁ i) (h₂ i) (rowc i)) x)
  have a := congrArg (π).map (reset_entered c h₁ m₁ x)
  have b := congrArg (π).map (reset_entered c h₂ m₂ x)
  rw [(π).map_comp] at a b
  have reset : QLit (reset_typed (c x)) ≫ QLit (dispatchEntered_typed h₁ x) =
      QLit (reset_typed (c x)) ≫ QLit (dispatchEntered_typed h₂ x) := a.symm.trans (tables.trans b)
  have pre : ∀ f : (π).obj (ofType (Φ := signature.Instr) State) ⟶ (π).obj (ofType Bit),
      QLit (const_typed (c x)) ≫ f = QLit (const_typed (c x)) ≫ QLit (reset_typed (c x)) ≫ f := fun f =>
    ((congrArg (· ≫ f) (q_const_reset (c x))).symm.trans (Category.assoc _ _ _))
  exact (pre _).trans ((congrArg (QLit (const_typed (c x)) ≫ ·) reset).trans (pre _).symm)

/-! ## One split state -/

section Row

variable {M : Nat}

/-- A written request row entered with its Bit is its literal request
trees; a silent row is unchanged. -/
theorem live_row_const (m : MixRow) (y : Fin (M + 1)) (a : Bool → Bool → Act M) (c : Bool) :
    QLit (seqValueBranches (const_typed (m.liveBit c)) (routerRow_typed M m.liveProg (m.liveAct y a))) =
      QLit (seqValueBranches (const_typed (m.liveBit c))
        (genRow_typed m.treeProg fun x b => treeRegion_typed M (m.treeKids y a (m.liveBit c) x b))) := by
  cases m with
  | ask r => exact env_row_const M r a c
  | pure e => rfl

theorem liveAct_carries (cc : Fin (M + 1) → Bool) (m : MixRow) (y : Fin (M + 1)) (a : Bool → Bool → Act M)
    (ha : ∀ x b, (a x b).Carries cc) (hp : ∀ e, m = .pure e → cc y = false) (x b : Bool) :
    (m.liveAct y a x b).Carries cc := by
  cases m with
  | ask r => exact ha x b
  | pure e => exact hp e rfl

theorem live_tree_matched (cc : Fin (M + 1) → Bool) (m : MixRow) (y : Fin (M + 1)) (a : Bool → Bool → Act M)
    (c : Bool) (ha : ∀ x b, (a x b).Carries cc) (hp : ∀ e, m = .pure e → cc y = false) (x b : Bool) :
    (ofRegion (treeRegion_typed M (m.treeKids y a c x b)) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫
        coprod.map (𝟙 _) (resetArr cc) =
      ofRegion (treeRegion_typed M (m.treeKids y a c x b)) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom := by
  cases m with
  | ask r =>
    refine tree_matched cc (r.kids a c x b) ?_
    cases x
    · exact envTree_carries cc a ha r.left _
    · exact envTree_carries cc a ha r.right _
  | pure e => exact tree_matched cc (.leaf (.go y false)) (hp e rfl)

theorem envTree_tidy (spin : Fin (M + 1) → Prop) (a : Bool → Bool → Act M)
    (ha : ∀ x y, (Tree.leaf (a x y)).Tidy spin) : ∀ {n : Nat} (c : Normal 2 n) (env : Fin n → Bool),
    (envTree a c env).toTree.Tidy spin
  | _, .ret _ _, _ => ha _ _
  | _, .ask _ _ left right, env => fun x y => by
    cases x
    · exact envTree_tidy spin a ha left (consBit y env)
    · exact envTree_tidy spin a ha right (consBit y env)

end Row

/-! ## The split table of a mixed table -/

section Nest

variable {K : Nat} (row : Fin (K + 1) → MixRow) (act : Fin (K + 1) → Bool → Bool → Act K)
  {cyc : Fin (K + (K + 1) + 1) → Bool} {fuel : Nat} (hcl : Classed row act cyc fuel)

theorem settled_kind {y : Fin (K + (K + 1) + 1)} (h : cutSil (mixSil row act) cyc y = none) :
    (∃ r, row (splitRow y) = .ask r) ∨ cyc y = true := by
  cases hy : cyc y with
  | true => exact .inr rfl
  | false => exact .inl (silent_none (cut_none h hy))

theorem nestBit_pure {y : Fin (K + (K + 1) + 1)} {e : Fin 2} (h : row (splitRow y) = .pure e) :
    nestBit row y = false := by
  show (row (splitRow y)).liveBit (splitBit y) = false
  rw [h]
  rfl

theorem nestBit_ask {y : Fin (K + (K + 1) + 1)} {r : EnvRow} (h : row (splitRow y) = .ask r) :
    nestBit row y = splitBit y := by
  show (row (splitRow y)).liveBit (splitBit y) = _
  rw [h]
  rfl

include hcl in
/-- A dulled settled action carries the Bits of the split table. -/
theorem dull_nest_carries (a : Act (K + (K + 1))) (hs : a.Settled (cutSil (mixSil row act) cyc))
    (hc : a.Carries splitBit) : (dullAct cyc a).Carries (nestBit row) := by
  cases a with
  | ret b => exact True.intro
  | go z q =>
    have cz : splitBit z = q := hc
    show nestBit row z = (match cyc z with | true => false | false => q)
    cases hz : cyc z with
    | true =>
      obtain ⟨e, hm⟩ := cyc_pure row act hcl z hz
      exact nestBit_pure row hm
    | false =>
      obtain ⟨r, hm⟩ := silent_none (cut_none hs hz)
      exact (nestBit_ask row hm).trans cz

include hcl in
theorem spun_carries (y : Fin (K + (K + 1) + 1)) (a b : Bool) :
    (spunAct row act cyc fuel y a b).Carries (nestBit row) :=
  dull_nest_carries row act hcl _ (hcl.settled _)
    (resolve_carries (cutSil (mixSil row act) cyc) splitBit (cut_hcar row act) fuel _ (redirect_carries _))

include hcl in
theorem nest_router_matched : Matched (nestBit row) (nestRouter row act cyc fuel).rows_typed :=
  router_matched (nestBit row) (nestRouter row act cyc fuel) fun x a b =>
    liveAct_carries (nestBit row) (row (splitRow x)) x (spunAct row act cyc fuel x)
      (spun_carries row act hcl x) (fun _ h => nestBit_pure row h) a b

include hcl in
theorem nest_trees_matched : Matched (nestBit row) (nestTrees row act cyc fuel).rows_typed :=
  fun x => gen_post (coprod.map (𝟙 _) (resetArr (nestBit row))) (by simp) ((nestTrees row act cyc fuel).prog x)
    (fun a b => treeRegion_typed _ ((nestTrees row act cyc fuel).kids x a b))
    (fun a b => treeRegion_typed _ ((nestTrees row act cyc fuel).kids x a b))
    (fun a b => live_tree_matched (nestBit row) (row (splitRow x)) x (spunAct row act cyc fuel x) (nestBit row x)
      (spun_carries row act hcl x) (fun _ h => nestBit_pure row h) a b)

include hcl in
/-- The table of written request rows and silent rows, entered with the
Bit of a split state, is the table of request trees and silent rows. -/
theorem nest_trees (y : Fin (K + (K + 1) + 1)) :
    QLit (const_typed (nestBit row y)) ≫ QLit ((nestRouter row act cyc fuel).entered_typed y) =
      QLit (const_typed (nestBit row y)) ≫ QLit ((nestTrees row act cyc fuel).entered_typed y) :=
  matched_const_congr (nestBit row) (nestRouter row act cyc fuel).rows_typed
    (nestTrees row act cyc fuel).rows_typed (nest_router_matched row act hcl) (nest_trees_matched row act hcl)
    (fun i => live_row_const (row (splitRow i)) i (spunAct row act cyc fuel i) (splitBit i)) y

include hcl in
/-- The dulled resolved table is the table of written request rows and
silent rows, at request rows and at the states of `cyc`. -/
theorem nest_bisim (y : Fin (K + (K + 1) + 1)) (hy : (∃ r, row (splitRow y) = .ask r) ∨ cyc y = true) :
    Eqv false [State]
      ((dulled ((splitRouter (mixRouter row act)).resolved (cutSil (mixSil row act) cyc) fuel) cyc
        (silNext (mixSil row act))).entered y)
      ((nestRouter row act cyc fuel).entered y) [Bit] :=
  dulled_live _ (nestRouter row act cyc fuel) cyc (silNext (mixSil row act))
    (fun y => ∃ r, row (splitRow y) = .ask r)
    (fun y ⟨r, hr⟩ => by
      refine ⟨?_, ?_, fun a b => ?_⟩
      · cases hc : cyc y with
        | false => rfl
        | true =>
          obtain ⟨e, hm⟩ := cyc_pure row act hcl y hc
          rw [hm] at hr
          cases hr
      · show (row (splitRow y)).liveProg = (row (splitRow y)).program
        rw [hr]
        rfl
      · show (row (splitRow y)).liveAct y (spunAct row act cyc fuel y) a b =
          dullAct cyc (resolveN _ fuel (redirect ((row (splitRow y)).act K (act (splitRow y)) a b)))
        rw [hr]
        rfl)
    (fun y _ a b z q hz => by
      have settled := hcl.settled (redirect ((row (splitRow y)).act K (act (splitRow y)) a b))
      have e : resolveN (cutSil (mixSil row act) cyc) fuel
          (redirect ((row (splitRow y)).act K (act (splitRow y)) a b)) = .go z q := hz
      rw [e] at settled
      exact settled_kind row act settled)
    (fun y hc => by
      obtain ⟨e, hm⟩ := cyc_pure row act hcl y hc
      refine ⟨?_, fun a b => ?_, (res_hcyc row act hcl y hc).2⟩
      · show (row (splitRow y)).liveProg = _
        rw [hm]
        rfl
      · show (row (splitRow y)).liveAct y (spunAct row act cyc fuel y) a b = _
        rw [hm]
        rfl) y hy

include hcl in
/-- A resolved action continued in the resolved table is its landing: a
returned Bit, or the table of request trees and silent rows. -/
theorem nest_landing_arrow (a : Act (K + (K + 1))) (hs : a.Settled (cutSil (mixSil row act) cyc))
    (hc : a.Carries splitBit) :
    (π).map (Act.arrow ((splitRouter (mixRouter row act)).resolved (cutSil (mixSil row act) cyc) fuel) a) =
      QLit (TLanding.region_typed (a.treeLanding (nestTrees row act cyc fuel) (nestBit row))) := by
  cases a with
  | ret b => rw [arrow_ret]
  | go y q =>
    have cy : splitBit y = q := hc
    subst cy
    have kind := settled_kind row act hs
    have bit : dullBit cyc splitBit y = nestBit row y := by
      rcases kind with ⟨r, hr⟩ | hcy
      · have nc : cyc y = false := by
          cases hc' : cyc y with
          | false => rfl
          | true =>
            obtain ⟨e, hm⟩ := cyc_pure row act hcl y hc'
            rw [hm] at hr
            cases hr
        exact (dullBit_false nc).trans (nestBit_ask row hr).symm
      · obtain ⟨e, hm⟩ := cyc_pure row act hcl y hcy
        exact (dullBit_true hcy).trans (nestBit_pure row hm).symm
    have dull := dull_entry ((splitRouter (mixRouter row act)).resolved (cutSil (mixSil row act) cyc) fuel)
      splitBit cyc (silNext (mixSil row act)) (res_hact row act) (res_hcyc row act hcl) y
    rw [bit] at dull
    have bis := (Paper.Extension.Singleton.ofRegion_eq_iff N
      ((dulled ((splitRouter (mixRouter row act)).resolved (cutSil (mixSil row act) cyc) fuel) cyc
        (silNext (mixSil row act))).entered_typed y)
      ((nestRouter row act cyc fuel).entered_typed y)).2 (nest_bisim row act hcl y kind)
    rw [arrow_go]
    exact (congrArg (π).map dull).trans (((π).map_comp _ _).trans
      ((congrArg (QLit (const_typed (nestBit row y)) ≫ ·) bis).trans
        ((nest_trees row act hcl y).trans
          (q_const (nestBit row y) ((nestTrees row act cyc fuel).entered_typed y)).symm)))

include hcl in
/-- A mixed table entered with each constant is its landing. -/
theorem nest_landed (j : Fin (K + 1)) :
    TLanded ((mixRouter row act).entered j) (nestLanding row act cyc fuel j) := fun q => by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q ((mixRouter row act).entered_typed j))
    (TLanding.region_typed (nestLanding row act cyc fuel j q))).1
  have fold : QLit ((splitRouter (mixRouter row act)).entered_typed (splitIdx j q)) =
      QLit ((mixRouter row act).entered_typed j) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (router_split_fold (mixRouter row act) j q)
  have entry := silent_entry (splitRouter (mixRouter row act)) splitBit (cutSil (mixSil row act) cyc) fuel
    (cut_hsil row act) (cut_hcar row act) (mix_hact row act) (fun x a b => hcl.settled _) (splitIdx j q)
    (hcl.settled _)
  rw [splitBit_idx] at entry
  have carries := resolve_carries (cutSil (mixSil row act) cyc) splitBit (cut_hcar row act) fuel
    (.go (splitIdx j q) q) (splitBit_idx j q)
  exact (q_const q ((mixRouter row act).entered_typed j)).trans
    ((congrArg (QLit (const_typed q) ≫ ·) fold.symm).trans
      ((((π).map_comp _ _).symm.trans (congrArg (π).map entry)).trans
        (nest_landing_arrow row act hcl _ (hcl.settled _) carries)))

include hcl in
theorem nest_written_landed (j : Fin (K + 1)) :
    TLanded ((mixWritten row act).entered j) (nestLanding row act cyc fuel j) := fun q =>
  (const_congr ((mixWritten row act).entered_typed j) ((mixRouter row act).entered_typed j)
    (.paper ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp (mix_written_arrow row act j))) q).trans
    (nest_landed row act hcl j q)

include hcl in
/-- The table of request trees and silent rows is one of labelled rows
with tidy trees and silent rows. -/
theorem nestTrees_spun : (nestTrees row act cyc fuel).Spun := fun j => by
  cases hm : row (splitRow j) with
  | ask r =>
    refine .inl ⟨⟨r.label, ?_⟩, fun x b => ⟨?_, ?_⟩⟩
    · show (row (splitRow j)).treeProg = _
      rw [hm]
      rfl
    · show ((row (splitRow j)).treeKids j (spunAct row act cyc fuel j) (nestBit row j) x b).All IsLabel
      rw [hm]
      exact ltree_all _
    · show ((row (splitRow j)).treeKids j (spunAct row act cyc fuel j) (nestBit row j) x b).Tidy _
      rw [hm]
      have leaf : ∀ x' y', (Tree.leaf (spunAct row act cyc fuel j x' y')).Tidy
          fun z => (nestTrees row act cyc fuel).prog z = .ret 0 0 := fun x' y' => by
        have settled := hcl.settled (redirect (act (splitRow j) x' y'))
        show (Tree.leaf (dullAct cyc (resolveN _ fuel (redirect (act (splitRow j) x' y'))))).Tidy _
        cases ha : resolveN (cutSil (mixSil row act) cyc) fuel (redirect (act (splitRow j) x' y')) with
        | ret c => exact True.intro
        | go z q =>
          rw [ha] at settled
          show (nestTrees row act cyc fuel).prog z = .ret 0 0 →
            (match cyc z with | true => false | false => q) = false
          intro hz
          cases hc : cyc z with
          | true => rfl
          | false =>
            obtain ⟨r', hr'⟩ := silent_none (cut_none settled hc)
            have pz : (row (splitRow z)).treeProg = .ret 0 0 := hz
            rw [hr'] at pz
            exact absurd pz (label_ne_ret ⟨r'.label, rfl⟩)
      cases x
      · exact envTree_tidy _ _ leaf r.left _
      · exact envTree_tidy _ _ leaf r.right _
  | pure e =>
    refine .inr ⟨?_, fun x b => ?_⟩
    · show (row (splitRow j)).treeProg = _
      rw [hm]
      rfl
    · show (row (splitRow j)).treeKids j (spunAct row act cyc fuel j) (nestBit row j) x b = _
      rw [hm]
      rfl

include hcl in
/-- Every entry of a classified mixed table lands in a returned Bit or in
a tidy table of labelled rows and canonical silent rows. -/
theorem mix_slanded (j : Fin (K + 1)) :
    ∃ L : Bool → SLanding, (∀ q, (L q).Tidy) ∧ SLanded ((mixWritten row act).entered j) L := by
  have each : ∀ q, ∃ S : SLanding, S.Tidy ∧
      Eqv false [U] (constEntry q ((mixWritten row act).entered j)) S.region [Bit] := fun q => by
    obtain ⟨S, tidy, e⟩ := tlanding_lift (nestTrees row act cyc fuel) (nestTrees_spun row act hcl) (nestBit row)
      (resolveN (cutSil (mixSil row act) cyc) fuel (.go (splitIdx j q) q))
    exact ⟨S, tidy, (nest_written_landed row act hcl j q).trans e⟩
  choose L tidy hl using each
  exact ⟨L, tidy, hl⟩

end Nest

/-! ## Loops with landings -/

section Landings

variable {r r' : Region signature.Instr} {L L' : Bool → SLanding}

/-- A loop is the case on its state of its two landings. -/
theorem slanded_case (h : ValueBranches [State] r [Bit]) (hl : SLanded r L) :
    Eqv false [State] r (caseEntry (L false).region (L true).region) [Bit] := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N h
    (caseEntry_typed (SLanding.region_typed (L false)) (SLanding.region_typed (L true)))).1
  have point : ∀ q, QLit (constEntry_typed q h) = QLit (SLanding.region_typed (L q)) := fun q =>
    (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (hl q)
  exact (congrArg (π).map (state_eta h)).trans
    (q_case_congr (caseValueBranches (constEntry_typed false h) (constEntry_typed true h)) deadBit_typed
      (caseValueBranches (SLanding.region_typed (L false)) (SLanding.region_typed (L true))) deadBit_typed
      (q_case_congr (constEntry_typed false h) (constEntry_typed true h) (SLanding.region_typed (L false))
        (SLanding.region_typed (L true)) (point false) (point true)) rfl)

/-- Two loops whose landings are equal at each constant are equal. -/
theorem slanded_eqv (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hl : SLanded r L) (hl' : SLanded r' L')
    (e : ∀ q, Eqv false [U] (L q).region (L' q).region [Bit]) : Eqv false [State] r r' [Bit] := by
  refine (slanded_case h hl).trans (Paper.Extension.Eqv.trans ?_ (slanded_case h' hl').symm)
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N
    (caseEntry_typed (SLanding.region_typed (L false)) (SLanding.region_typed (L true)))
    (caseEntry_typed (SLanding.region_typed (L' false)) (SLanding.region_typed (L' true)))).1
  have point : ∀ q, QLit (SLanding.region_typed (L q)) = QLit (SLanding.region_typed (L' q)) := fun q =>
    (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (e q)
  exact q_case_congr (caseValueBranches (SLanding.region_typed (L false)) (SLanding.region_typed (L true)))
    deadBit_typed (caseValueBranches (SLanding.region_typed (L' false)) (SLanding.region_typed (L' true)))
    deadBit_typed (q_case_congr _ _ _ _ (point false) (point true)) rfl

end Landings

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
