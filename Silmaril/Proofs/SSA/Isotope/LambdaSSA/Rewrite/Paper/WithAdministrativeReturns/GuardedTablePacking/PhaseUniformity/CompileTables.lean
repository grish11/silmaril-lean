module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Nest.Compile.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.NestTables

/-! # Every tree table has a router table with the same entered loops -/

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

theorem ifPos {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ifNeg {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

variable {K : Nat}

/-! ## Renaming -/

theorem inline_shift (p₀ : Program) (k₀ : Bool → Bool → Tree K) : ∀ s : Tree K, s.shift.inline p₀ k₀ = s
  | .leaf (.ret _) => rfl
  | .leaf (.go _ _) => rfl
  | .ask q p kids => congrArg (Tree.ask q p) (funext fun x => funext fun y => inline_shift p₀ k₀ (kids x y))

theorem shift_above : ∀ s : Tree K, s.shift.Above 0
  | .leaf (.ret _) => True.intro
  | .leaf (.go j _) => Nat.succ_pos j.val
  | .ask _ _ kids => fun x y => shift_above (kids x y)

theorem size_shift : ∀ s : Tree K, s.shift.size = s.size
  | .leaf _ => rfl
  | .ask _ _ kids => by
    show 1 + (_ + _ + (_ + _)) = 1 + (_ + _ + (_ + _))
    rw [size_shift (kids false false), size_shift (kids false true), size_shift (kids true false),
      size_shift (kids true true)]

theorem shift_all (Q : Program → Prop) : ∀ s : Tree K, s.All Q → s.shift.All Q
  | .leaf _, _ => True.intro
  | .ask _ _ kids, h => ⟨h.1, fun x y => shift_all Q (kids x y) (h.2 x y)⟩

/-! ## Counting -/

theorem finSum_lower : ∀ (n : Nat) (g g' : Fin n → Nat) (i : Fin n) (c : Nat),
    (∀ j, j ≠ i → g' j = g j) → g' i + c = g i → finSum n g' + c = finSum n g
  | 0, _, _, i, _, _, _ => i.elim0
  | n + 1, g, g', i, c, hne, hi => by
    revert hne hi
    refine Fin.cases ?_ (fun i' => ?_) i
    · intro hne hi
      have tail : (fun j : Fin n => g' j.succ) = fun j => g j.succ :=
        funext fun j => hne j.succ (Fin.succ_ne_zero j)
      show g' 0 + finSum n (fun j => g' j.succ) + c = g 0 + finSum n fun j => g j.succ
      rw [tail]
      omega
    · intro hne hi
      have head : g' 0 = g 0 := hne 0 (Fin.succ_ne_zero i').symm
      have ih := finSum_lower n (fun j => g j.succ) (fun j => g' j.succ) i' c
        (fun j hj => hne j.succ fun e => hj (Fin.succ_inj.mp e)) hi
      show g' 0 + finSum n (fun j => g' j.succ) + c = g 0 + finSum n fun j => g j.succ
      omega

section Step

variable (t : TreeTable K) (i : Fin (K + 1)) (x y q : Bool) (p : Program) (ks : Bool → Bool → Tree K)

/-- One step removes exactly one inner request. -/
theorem outline_asks (h : t.kids i x y = .ask q p ks) : (t.outlineAt i x y q p ks).asks + 1 = t.asks := by
  have hsize : (t.kids i x y).size = 1 + ((ks false false).size + (ks false true).size +
      ((ks true false).size + (ks true true).size)) := by
    rw [h]
    rfl
  have front : (t.outlineAt i x y q p ks).rowAsks 0 = (ks false false).size + (ks false true).size +
      ((ks true false).size + (ks true true).size) := by
    show (ks false false).shift.size + (ks false true).shift.size +
      ((ks true false).shift.size + (ks true true).shift.size) = _
    rw [size_shift, size_shift, size_shift, size_shift]
  have sz : ∀ (j : Fin (K + 1)) (x' y' : Bool), ((t.outlineAt i x y q p ks).kids j.succ x' y').size =
      if j = i ∧ x' = x ∧ y' = y then 0 else (t.kids j x' y').size := by
    intro j x' y'
    show (if j = i ∧ x' = x ∧ y' = y then Tree.leaf (.go 0 q) else (t.kids j x' y').shift).size = _
    by_cases c : j = i ∧ x' = x ∧ y' = y
    · rw [ifPos c, ifPos c]
      rfl
    · rw [ifNeg c, ifNeg c]
      exact size_shift _
  have other : ∀ j, j ≠ i → (t.outlineAt i x y q p ks).rowAsks j.succ = t.rowAsks j := by
    intro j hj
    show ((t.outlineAt i x y q p ks).kids j.succ false false).size + _ + (_ + _) = _
    rw [sz, sz, sz, sz, ifNeg fun c => hj c.1, ifNeg fun c => hj c.1, ifNeg fun c => hj c.1,
      ifNeg fun c => hj c.1]
    rfl
  have here : (t.outlineAt i x y q p ks).rowAsks i.succ + (t.kids i x y).size = t.rowAsks i := by
    show ((t.outlineAt i x y q p ks).kids i.succ false false).size + _ + (_ + _) + _ =
      (t.kids i false false).size + (t.kids i false true).size +
        ((t.kids i true false).size + (t.kids i true true).size)
    rw [sz, sz, sz, sz]
    cases x <;> cases y <;> simp <;> omega
  have tail := finSum_lower (K + 1) t.rowAsks (fun j => (t.outlineAt i x y q p ks).rowAsks j.succ) i
    (t.kids i x y).size other here
  show (t.outlineAt i x y q p ks).rowAsks 0 +
    finSum (K + 1) (fun j => (t.outlineAt i x y q p ks).rowAsks j.succ) + 1 = finSum (K + 1) t.rowAsks
  omega

/-- Writing the new state back inside recovers the table. -/
theorem outline_inline (h : t.kids i x y = .ask q p ks) : (t.outlineAt i x y q p ks).inlineFront = t := by
  have fk : (t.outlineAt i x y q p ks).frontKids = ks :=
    funext fun a => funext fun b => inline_shift _ _ (ks a b)
  have kids : (t.outlineAt i x y q p ks).inlineFront.kids = t.kids := by
    funext j x' y'
    show (if j = i ∧ x' = x ∧ y' = y then Tree.leaf (.go 0 q) else (t.kids j x' y').shift).inline p
      (t.outlineAt i x y q p ks).frontKids = _
    rw [fk]
    by_cases c : j = i ∧ x' = x ∧ y' = y
    · rw [ifPos c]
      obtain ⟨rfl, rfl, rfl⟩ := c
      exact h.symm
    · rw [ifNeg c]
      exact inline_shift _ _ _
  exact congrArg (TreeTable.mk t.prog) kids

theorem arrow_of_eq {t t' : TreeTable K} (e : t = t') (j : Fin (K + 1)) :
    ofRegion (t.entered_typed j) = ofRegion (t'.entered_typed j) := by
  subst e
  rfl

/-- One step does not change the entered loops, in default Paper. -/
theorem outline_arrow (h : t.kids i x y = .ask q p ks) (j : Fin (K + 1)) :
    ofRegion (t.entered_typed j) = ofRegion ((t.outlineAt i x y q p ks).entered_typed j.succ) :=
  (arrow_of_eq (outline_inline t i x y q p ks h).symm j).trans
    (inlineFront_arrow (t.outlineAt i x y q p ks) (fun a b => shift_above (ks a b)) j)

theorem outline_all (Q : Program → Prop) (h : t.kids i x y = .ask q p ks) (hall : t.All Q) :
    (t.outlineAt i x y q p ks).All Q := by
  have hk : (Tree.ask q p ks).All Q := h ▸ hall.2 i x y
  refine ⟨fun j => ?_, fun j x' y' => ?_⟩
  · refine Fin.cases ?_ (fun j' => ?_) j
    · exact hk.1
    · exact hall.1 j'
  · refine Fin.cases ?_ (fun j' => ?_) j
    · exact shift_all Q _ (hk.2 x' y')
    · show (if j' = i ∧ x' = x ∧ y' = y then Tree.leaf (.go 0 q) else (t.kids j' x' y').shift).All Q
      by_cases c : j' = i ∧ x' = x ∧ y' = y
      · rw [ifPos c]
        exact True.intro
      · rw [ifNeg c]
        exact shift_all Q _ (hall.2 j' x' y')

end Step

theorem flat_eq (t : TreeTable K) (hno : ¬ ∃ i x y q p ks, t.kids i x y = Tree.ask q p ks) :
    t = t.flatten.toTrees := by
  have kids : t.kids = fun j x y => Tree.leaf (t.kids j x y).leafAct := by
    funext j x y
    cases hk : t.kids j x y with
    | leaf a => rfl
    | ask q p ks => exact absurd ⟨j, x, y, q, p, ks, hk⟩ hno
  exact congrArg (TreeTable.mk t.prog) kids

/-- Every tree table has a router table with the same entered loops, in
default Paper. The old states are sent to states of the router table, and
every program of the router table is a program of the tree table. -/
theorem exists_router (Q : Program → Prop) (n : Nat) : ∀ {K : Nat} (t : TreeTable K), t.asks ≤ n → t.All Q →
    ∃ (M : Nat) (R : Router M) (e : Fin (K + 1) → Fin (M + 1)), (∀ m, Q (R.prog m)) ∧
      ∀ j, ofRegion (t.entered_typed j) = ofRegion (R.entered_typed (e j)) := by
  induction n with
  | zero =>
    intro K t hn hall
    by_cases hask : ∃ i x y q p ks, t.kids i x y = Tree.ask q p ks
    · obtain ⟨i, x, y, q, p, ks, h⟩ := hask
      have dec := outline_asks t i x y q p ks h
      omega
    · exact ⟨K, t.flatten, id, hall.1, fun j => arrow_of_eq (flat_eq t hask) j⟩
  | succ n ih =>
    intro K t hn hall
    by_cases hask : ∃ i x y q p ks, t.kids i x y = Tree.ask q p ks
    · obtain ⟨i, x, y, q, p, ks, h⟩ := hask
      have dec := outline_asks t i x y q p ks h
      obtain ⟨M, R, e, hq, ha⟩ := ih (t.outlineAt i x y q p ks) (by omega) (outline_all t i x y q p ks Q h hall)
      exact ⟨M, R, fun j => e j.succ, hq, fun j => (outline_arrow t i x y q p ks h j).trans (ha j.succ)⟩
    · exact ⟨K, t.flatten, id, hall.1, fun j => arrow_of_eq (flat_eq t hask) j⟩

/-! ## Tables of labelled requests -/

theorem ltree_all : ∀ s : LTree K, s.toTree.All IsLabel
  | .leaf _ => True.intro
  | .ask _ l kids => ⟨⟨l, rfl⟩, fun x y => ltree_all (kids x y)⟩

theorem ltable_all (t : LTable K) : t.toTable.All IsLabel :=
  ⟨fun j => ⟨t.label j, rfl⟩, fun j x y => ltree_all (t.kids j x y)⟩

theorem router_arrow_of_eq {M : Nat} {R R' : Router M} (e : R = R') (m : Fin (M + 1)) :
    ofRegion (R.entered_typed m) = ofRegion (R'.entered_typed m) := by
  subst e
  rfl

/-- Every table of labelled request trees has a router table of labelled
requests with the same entered loops. -/
theorem ltable_router (t : LTable K) :
    ∃ (M : Nat) (label : Fin (M + 1) → Bool) (act : Fin (M + 1) → Bool → Bool → Act M)
      (e : Fin (K + 1) → Fin (M + 1)),
      ∀ j, ofRegion (t.entered_typed j) = ofRegion ((Router.ofLabels label act).entered_typed (e j)) := by
  obtain ⟨M, R, e, hq, ha⟩ := exists_router IsLabel t.toTable.asks t.toTable (Nat.le_refl _) (ltable_all t)
  choose label hl using hq
  have hR : R = Router.ofLabels label R.act := congrArg (fun p => Router.mk p R.act) (funext hl)
  exact ⟨M, label, R.act, e, fun j => (ha j).trans (router_arrow_of_eq hR (e j))⟩

/-! ## The written source and its explicit table -/

theorem source_nest (a o d : Bool) :
    (sourceTable a o d).toTable =
      TreeTable.nest (K := 1) 1 (Router.ofLabels (explicitLabel a o d) explicitAct).toTrees := by
  have fk : (Router.ofLabels (explicitLabel a o d) explicitAct).toTrees.frontKids =
      fun x' y' => (contKids x' y').toTree := by
    funext x' y'
    cases x' <;> rfl
  have progs : (sourceTable a o d).toTable.prog =
      (TreeTable.nest (K := 1) 1 (Router.ofLabels (explicitLabel a o d) explicitAct).toTrees).prog := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · have j0 : j = 0 := Fin.eq_zero j
      subst j0
      rfl
  have kids : (sourceTable a o d).toTable.kids =
      (TreeTable.nest (K := 1) 1 (Router.ofLabels (explicitLabel a o d) explicitAct).toTrees).kids := by
    funext j x y
    show _ = (Tree.leaf (explicitAct j.succ x y)).inline (labelPoll (explicitLabel a o d 0)).program
      (Router.ofLabels (explicitLabel a o d) explicitAct).toTrees.frontKids
    rw [fk]
    refine Fin.cases ?_ (fun j => ?_) j
    · cases x <;> cases y <;> rfl
    · have j0 : j = 0 := Fin.eq_zero j
      subst j0
      cases x <;> cases y <;> rfl
  exact (congrArg (fun k => TreeTable.mk (sourceTable a o d).toTable.prog k) kids).trans
    (congrArg (fun p => TreeTable.mk p _) progs)

theorem explicit_forward (a o d : Bool) : (Router.ofLabels (explicitLabel a o d) explicitAct).Forward 1 := by
  intro k hk x y
  match k, hk with
  | 0, _ => cases x <;> first | exact True.intro | (show (_ : Nat) < _; decide)
  | 1, hk => exact absurd hk (by decide)
  | 2, hk => exact absurd hk (by decide)

theorem ltable_eqv_router (t : LTable K) :
    ∃ (M : Nat) (label : Fin (M + 1) → Bool) (act : Fin (M + 1) → Bool → Bool → Act M)
      (e : Fin (K + 1) → Fin (M + 1)),
      ∀ j, Eqv false [State] (t.entered j) ((Router.ofLabels label act).entered (e j)) [Bit] := by
  obtain ⟨M, label, act, e, ha⟩ := ltable_router t
  exact ⟨M, label, act, e, fun j =>
    (Paper.Extension.Singleton.ofRegion_eq_iff N (t.entered_typed j)
      ((Router.ofLabels label act).entered_typed (e j))).1 (congrArg (π).map (ha j))⟩

/-- The written source equals the table with the second request as an
explicit state, at both entries. -/
theorem source_eqv_explicit (a o d : Bool) (i : Fin 2) :
    Eqv false [State] ((sourceTable a o d).entered i)
      ((Router.ofLabels (explicitLabel a o d) explicitAct).entered i.succ) [Bit] := by
  show Eqv false [State] ((sourceTable a o d).toTable.entered i) _ [Bit]
  rw [source_nest]
  exact router_nest_eqv (K := 1) 1 _ (explicit_forward a o d) i

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
