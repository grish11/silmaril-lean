module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Silent.Diverge.Nested.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.QueryTables

/-! # From request trees with silent rows to a tidy router table -/

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
open Paper.TypeCategory (iterate_fixpoint)

/-! ## Outlining keeps silent rows and tidiness -/

theorem label_ne_ret {p : Program} (h : IsLabel p) : p ≠ .ret 0 0 := by
  obtain ⟨l, rfl⟩ := h
  intro e
  cases e

section Shift

variable {K : Nat}

theorem shift_tidy (spin : Fin (K + 1) → Prop) (spin' : Fin (K + 2) → Prop)
    (hs : ∀ z, spin' z.succ → spin z) : ∀ s : Tree K, s.Tidy spin → s.shift.Tidy spin'
  | .leaf (.ret _), _ => True.intro
  | .leaf (.go z _), h => fun hz => h (hs z hz)
  | .ask _ _ kids, h => fun x y => shift_tidy spin spin' hs (kids x y) (h x y)

variable (t : TreeTable K) (i : Fin (K + 1)) (x y q : Bool) (p : Program) (ks : Bool → Bool → Tree K)

/-- Moving an inner request into a new state keeps the table one of
labelled rows with tidy trees and silent rows. -/
theorem outline_spun (h : t.kids i x y = .ask q p ks) (hs : t.Spun) : (t.outlineAt i x y q p ks).Spun := by
  have hi : IsLabel (t.prog i) ∧ ∀ x' y', (t.kids i x' y').All IsLabel ∧
      (t.kids i x' y').Tidy fun z => t.prog z = .ret 0 0 := by
    rcases hs i with l | ⟨-, sp⟩
    · exact l
    · rw [sp x y] at h
      cases h
  have hk := hi.2 x y
  rw [h] at hk
  have hp : IsLabel p := hk.1.1
  have back : ∀ z : Fin (K + 1), (t.outlineAt i x y q p ks).prog z.succ = .ret 0 0 → t.prog z = .ret 0 0 :=
    fun z hz => hz
  refine Fin.cases ?_ (fun j => ?_)
  · refine .inl ⟨hp, fun x' y' => ⟨shift_all IsLabel _ (hk.1.2 x' y'), ?_⟩⟩
    exact shift_tidy _ _ back _ (hk.2 x' y')
  · rcases hs j with ⟨lj, tj⟩ | ⟨sj, kj⟩
    · refine .inl ⟨lj, fun x' y' => ?_⟩
      show (if j = i ∧ x' = x ∧ y' = y then Tree.leaf (.go 0 q) else (t.kids j x' y').shift).All IsLabel ∧
        (if j = i ∧ x' = x ∧ y' = y then Tree.leaf (.go 0 q) else (t.kids j x' y').shift).Tidy _
      by_cases c : j = i ∧ x' = x ∧ y' = y
      · rw [ifPos c]
        exact ⟨True.intro, fun (h0 : p = .ret 0 0) => absurd h0 (label_ne_ret hp)⟩
      · rw [ifNeg c]
        exact ⟨shift_all IsLabel _ (tj x' y').1, shift_tidy _ _ back _ (tj x' y').2⟩
    · refine .inr ⟨sj, fun x' y' => ?_⟩
      show (if j = i ∧ x' = x ∧ y' = y then Tree.leaf (.go 0 q) else (t.kids j x' y').shift) = _
      have c : ¬ (j = i ∧ x' = x ∧ y' = y) := fun c => by
        have e := c.1
        subst e
        rw [kj x y] at h
        cases h
      rw [ifNeg c, kj x' y']
      rfl

end Shift

/-! ## The router table of a table without inner requests -/

theorem flat_spin {K : Nat} (t : TreeTable K) (hno : ¬ ∃ i x y q p ks, t.kids i x y = Tree.ask q p ks)
    (hs : t.Spun) :
    ∃ label : Fin (K + 1) → Option Bool, t.flatten = Router.ofSpin label t.flatten.act ∧
      Tidy label t.flatten.act := by
  have each : ∀ j, ∃ o : Option Bool, t.prog j = lsProg o ∧
      (o = none → ∀ x y, t.kids j x y = .leaf (.go j false)) := fun j => by
    rcases hs j with ⟨⟨l, hl⟩, -⟩ | ⟨sj, kj⟩
    · exact ⟨some l, hl, fun e => by cases e⟩
    · exact ⟨none, sj, fun _ => kj⟩
  choose label hprog hnone using each
  have acts : ∀ j, lsAct (label j) j (t.flatten.act j) = t.flatten.act j := fun j => by
    cases hj : label j with
    | some l => rfl
    | none =>
      funext a b
      show Act.go j false = (t.kids j a b).leafAct
      rw [hnone j hj a b]
      rfl
  refine ⟨label, ?_, fun i l hi tag pl j q ha hj => ?_⟩
  · exact (congrArg (fun p => Router.mk p t.flatten.act) (funext hprog)).trans
      (congrArg (Router.mk fun j => lsProg (label j)) (funext acts).symm)
  · have pj : t.prog j = .ret 0 0 := by
      rw [hprog j, hj]
      rfl
    have pi : IsLabel (t.prog i) := ⟨l, by rw [hprog i, hi]; rfl⟩
    rcases hs i with ⟨-, ti⟩ | ⟨si, -⟩
    · have tidy := (ti tag pl).2
      cases hk : t.kids i tag pl with
      | leaf a =>
        have e : a = .go j q := by
          have : (t.kids i tag pl).leafAct = .go j q := ha
          rw [hk] at this
          exact this
        subst e
        rw [hk] at tidy
        exact tidy pj
      | ask q' p' ks' => exact absurd ⟨i, tag, pl, q', p', ks', hk⟩ hno
    · exact absurd si (label_ne_ret pi)

/-- Every table of labelled request trees and silent rows has a tidy
router table of labelled rows and silent rows with the same entered
loops, in default Paper. -/
theorem spun_router (n : Nat) : ∀ {K : Nat} (t : TreeTable K), t.asks ≤ n → t.Spun →
    ∃ (M : Nat) (label : Fin (M + 1) → Option Bool) (act : Fin (M + 1) → Bool → Bool → Act M)
      (e : Fin (K + 1) → Fin (M + 1)), Tidy label act ∧
      ∀ j, ofRegion (t.entered_typed j) = ofRegion ((Router.ofSpin label act).entered_typed (e j)) := by
  have base : ∀ {K : Nat} (t : TreeTable K), (¬ ∃ i x y q p ks, t.kids i x y = Tree.ask q p ks) → t.Spun →
      ∃ (M : Nat) (label : Fin (M + 1) → Option Bool) (act : Fin (M + 1) → Bool → Bool → Act M)
        (e : Fin (K + 1) → Fin (M + 1)), Tidy label act ∧
        ∀ j, ofRegion (t.entered_typed j) = ofRegion ((Router.ofSpin label act).entered_typed (e j)) :=
    fun {K} t hno hs => by
      obtain ⟨label, eq, tidy⟩ := flat_spin t hno hs
      exact ⟨K, label, t.flatten.act, id, tidy, fun j =>
        (arrow_of_eq (flat_eq t hno) j).trans (router_arrow_of_eq eq j)⟩
  induction n with
  | zero =>
    intro K t hn hs
    by_cases hask : ∃ i x y q p ks, t.kids i x y = Tree.ask q p ks
    · obtain ⟨i, x, y, q, p, ks, h⟩ := hask
      have dec := outline_asks t i x y q p ks h
      omega
    · exact base t hask hs
  | succ n ih =>
    intro K t hn hs
    by_cases hask : ∃ i x y q p ks, t.kids i x y = Tree.ask q p ks
    · obtain ⟨i, x, y, q, p, ks, h⟩ := hask
      have dec := outline_asks t i x y q p ks h
      obtain ⟨M, label, act, e, tidy, ha⟩ := ih (t.outlineAt i x y q p ks) (by omega)
        (outline_spun t i x y q p ks h hs)
      exact ⟨M, label, act, fun j => e j.succ, tidy, fun j => (outline_arrow t i x y q p ks h j).trans (ha j.succ)⟩
    · exact base t hask hs

/-! ## A silent row does not read its Bit -/

section SpinBit

variable {M : Nat} (label : Fin (M + 1) → Option Bool) (act : Fin (M + 1) → Bool → Bool → Act M)

theorem spin_row_const (x : Fin (M + 1)) (hn : label x = none) (q : Bool) :
    ofRegion (const_typed q) ≫ ofRegion ((Router.ofSpin label act).rows_typed x) =
      ofRegion (act_typed M (.go x false)) := by
  have key : ∀ o : Option Bool, o = none →
      ∀ h : ValueBranches [State] (routerRow M (lsProg o) (lsAct o x (act x))) [Silmaril.coprod Bit (States M)],
        ofRegion (const_typed q) ≫ ofRegion h = ofRegion (act_typed M (.go x false)) := fun o ho h => by
    subst ho
    exact (ofRegion_comp (const_typed q) h (seqValueBranches (const_typed q) h)).trans
      (pure_const M 0 (fun _ _ => .go x false) q)
  exact key (label x) hn ((Router.ofSpin label act).rows_typed x)

/-- Entering a silent row does not depend on the Bit, in default Paper. -/
theorem spin_entry_bit (x : Fin (M + 1)) (hn : label x = none) (q : Bool) :
    ofRegion (const_typed q) ≫ ofRegion ((Router.ofSpin label act).entered_typed x) =
      ofRegion (const_typed false) ≫ ofRegion ((Router.ofSpin label act).entered_typed x) := by
  have e : ∀ q, ofRegion (const_typed q) ≫ ofRegion ((Router.ofSpin label act).entered_typed x) =
      (ofRegion (act_typed M (.go x false)) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫
        coprod.desc (𝟙 _) (Paper.TypeCategory.iterate (stepArr (Router.ofSpin label act))) := fun q => by
    have fix := iterate_fixpoint (stepArr (Router.ofSpin label act))
    have step : injArr M x ≫ stepArr (Router.ofSpin label act) =
        ofRegion ((Router.ofSpin label act).rows_typed x) ≫
          (sumIso (Φ := signature.Instr) Bit (States M)).hom := by
      rw [stepArr_eq, ← Category.assoc, inj_dispatch M (Router.ofSpin label act).rows_typed x]
    show _ ≫ ofRegion (dispatchEntered_typed (Router.ofSpin label act).rows_typed x) = _
    rw [dispatchEntered_arrow (Router.ofSpin label act).rows_typed x, loop_iterate]
    calc
      _ = ofRegion (const_typed q) ≫ injArr M x ≫ stepArr (Router.ofSpin label act) ≫
            coprod.desc (𝟙 _) (Paper.TypeCategory.iterate (stepArr (Router.ofSpin label act))) :=
        congrArg (fun f => ofRegion (const_typed q) ≫ injArr M x ≫ f) fix
      _ = (ofRegion (const_typed q) ≫ ofRegion ((Router.ofSpin label act).rows_typed x)) ≫
            (sumIso (Φ := signature.Instr) Bit (States M)).hom ≫
              coprod.desc (𝟙 _) (Paper.TypeCategory.iterate (stepArr (Router.ofSpin label act))) := by
        rw [← Category.assoc (injArr M x), step]
        simp only [Category.assoc]
      _ = _ := by
        rw [spin_row_const label act x hn q, Category.assoc]
  exact (e q).trans (e false).symm

end SpinBit

/-! ## Entering with a constant -/

theorem const_congr {D : Ty Empty} {r r' : Region signature.Instr} (h : ValueBranches [State] r [D])
    (h' : ValueBranches [State] r' [D]) (e : Eqv false [State] r r' [D]) (q : Bool) :
    Eqv false [U] (constEntry q r) (constEntry q r') [D] :=
  (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q h) (constEntry_typed q h')).1
    ((q_const q h).trans ((congrArg (QLit (const_typed q) ≫ ·)
      ((Paper.Extension.Singleton.ofRegion_eq_iff N h h').2 e)).trans (q_const q h').symm))

theorem const_arrow_congr {D : Ty Empty} {r r' : Region signature.Instr} (h : ValueBranches [State] r [D])
    (h' : ValueBranches [State] r' [D]) (e : ofRegion h = ofRegion h') (q : Bool) :
    ofRegion (constEntry_typed q h) = ofRegion (constEntry_typed q h') :=
  (ofRegion_comp (const_typed q) h (constEntry_typed q h)).symm.trans
    ((congrArg (ofRegion (const_typed q) ≫ ·) e).trans (ofRegion_comp (const_typed q) h' (constEntry_typed q h')))

theorem spin_entry_bit_eqv {M : Nat} (label : Fin (M + 1) → Option Bool)
    (act : Fin (M + 1) → Bool → Bool → Act M) (x : Fin (M + 1)) (hn : label x = none) (q : Bool) :
    Eqv false [U] (constEntry q ((Router.ofSpin label act).entered x))
      (constEntry false ((Router.ofSpin label act).entered x)) [Bit] :=
  .paper ((Paper.TypeCategory.ofRegion_eq_iff (constEntry_typed q ((Router.ofSpin label act).entered_typed x))
    (constEntry_typed false ((Router.ofSpin label act).entered_typed x))).mp
    ((ofRegion_comp (const_typed q) ((Router.ofSpin label act).entered_typed x) _).symm.trans
      ((spin_entry_bit label act x hn q).trans
        (ofRegion_comp (const_typed false) ((Router.ofSpin label act).entered_typed x) _))))

/-- A landing in request trees with silent rows is a landing in a tidy
router table. -/
theorem tlanding_lift {M : Nat} (t : TreeTable M) (hs : t.Spun) (c : Fin (M + 1) → Bool) (a : Act M) :
    ∃ S : SLanding, S.Tidy ∧ Eqv false [U] (a.treeLanding t c).region S.region [Bit] := by
  cases a with
  | ret b => exact ⟨.ret b, True.intro, Paper.Extension.Eqv.refl (TLanding.region_typed (M := M) (.ret b)).hasType⟩
  | go y q =>
    obtain ⟨M', label, act, e, tidy, ha⟩ := spun_router t.asks t (Nat.le_refl _) hs
    exact ⟨.at label act (e y) (c y), tidy, .paper ((Paper.TypeCategory.ofRegion_eq_iff
      (constEntry_typed (c y) (t.entered_typed y))
      (constEntry_typed (c y) ((Router.ofSpin label act).entered_typed (e y)))).mp
      (const_arrow_congr (t.entered_typed y) ((Router.ofSpin label act).entered_typed (e y)) (ha y) (c y)))⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
