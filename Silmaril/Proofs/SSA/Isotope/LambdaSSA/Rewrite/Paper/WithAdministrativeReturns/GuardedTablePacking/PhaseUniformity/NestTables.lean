module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Nest.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.DeepTables
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RouterPrefix

/-! # Nested request trees equal their router tables -/

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
open Paper.TypeCategory (sumDesc sumInl sumInr sumInl_sumDesc sumInr_sumDesc sumDesc_comp iterate_outline)
open Paper.WithCaseBind.BitQuery.RequestTree (event Word)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (bit)

/-! ## Rows with regions at the four results -/

section Post

variable {K K' : Nat}
  (φ : ofType (Φ := signature.Instr) Bit ⨿ ofType (States K) ⟶ ofType Bit ⨿ ofType (States K'))
  (hφ : coprod.inl ≫ φ = coprod.inl)

include hφ in
theorem dead_post_of :
    (ofRegion (dead_typed K) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ φ =
      ofRegion (dead_typed K') ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom := by
  have e : ofRegion (dead_typed K) =
      ofRegion (r := .br 0 (.inl .unit)) (.br (L := [Bit]) rfl (.inl (A := Ty.unit) (B := Ty.unit) .unit)) ≫
        (coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
    br_inl (X := Silmaril.empty) (.inl .unit)
  have e' : ofRegion (dead_typed K') =
      ofRegion (r := .br 0 (.inl .unit)) (.br (L := [Bit]) rfl (.inl (A := Ty.unit) (B := Ty.unit) .unit)) ≫
        (coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States K')).inv) :=
    br_inl (X := Silmaril.empty) (.inl .unit)
  rw [e, e']
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hφ]

include hφ in
theorem gen_post (p : Program) {r r' : Bool → Bool → Region signature.Instr}
    (h : ∀ x y, ValueBranches [Ty.unit] (r x y) [Silmaril.coprod Bit (States K)])
    (h' : ∀ x y, ValueBranches [Ty.unit] (r' x y) [Silmaril.coprod Bit (States K')])
    (leaf : ∀ x y, (ofRegion (h x y) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ φ =
      ofRegion (h' x y) ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom) :
    (ofRegion (genRow_typed p h) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ φ =
      ofRegion (genRow_typed p h') ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom :=
  seq_post φ p _ _
    (case_post φ _ _ _ _ (case_post φ _ _ _ _ (leaf false false) (leaf false true))
      (case_post φ _ _ _ _ (case_post φ _ _ _ _ (leaf true false) (leaf true true)) (dead_post_of φ hφ)))

end Post

/-! ## Trees -/

variable {K : Nat}

/-- A tree row as an arrow. -/
noncomputable abbrev rowArr (K : Nat) (p : Program) (k : Bool → Bool → Tree K) :
    ofType (Φ := signature.Instr) State ⟶ ofType Bit ⨿ ofType (States K) :=
  ofRegion (genRow_typed p fun x y => treeRegion_typed K (k x y)) ≫
    (sumIso (Φ := signature.Instr) Bit (States K)).hom

theorem ask_arrow (K : Nat) (q : Bool) (p : Program) (kids : Bool → Bool → Tree K) :
    ofRegion (treeRegion_typed K (.ask q p kids)) =
      ofRegion (const_typed q) ≫ ofRegion (genRow_typed p fun x y => treeRegion_typed K (kids x y)) :=
  (Paper.TypeCategory.ofRegion_comp (const_typed q)
    (genRow_typed p fun x y => treeRegion_typed K (kids x y)) _).symm

theorem ask_sum (K : Nat) (q : Bool) (p : Program) (kids : Bool → Bool → Tree K) :
    ofRegion (treeRegion_typed K (.ask q p kids)) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom =
      ofRegion (const_typed q) ≫ rowArr K p kids :=
  (congrArg (· ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) (ask_arrow K q p kids)).trans
    (Category.assoc _ _ _)

theorem go_zero_post (r₀ : ofType (Φ := signature.Instr) State ⟶ ofType Bit ⨿ ofType (States K)) (q : Bool) :
    (ofRegion (act_typed (K + 1) (.go 0 q)) ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom) ≫
        coprod.desc coprod.inl (sumDesc r₀ coprod.inr) = ofRegion (const_typed q) ≫ r₀ := by
  have e : ofRegion (act_typed (K + 1) (.go 0 q)) =
      (ofRegion (const_typed q) ≫ injArr (K + 1) 0) ≫
        (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).inv) :=
    (br_inr (injTm_typed (.inl (bitTm_typed q)) (K + 1) 0)).trans
      (congrArg (· ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).inv))
        (injOf_eq (.inl (bitTm_typed q)) (K + 1) 0))
  rw [e]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, coprod.inr_desc]
  rw [zero_inline]

/-- Running the row of state zero in place of the jumps to it turns a
tree into its inlined tree. -/
theorem tree_post (p₀ : Program) (k₀ : Bool → Bool → Tree K) : ∀ t : Tree (K + 1),
    (ofRegion (treeRegion_typed (K + 1) t) ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom) ≫
        coprod.desc coprod.inl (sumDesc (rowArr K p₀ k₀) coprod.inr) =
      ofRegion (treeRegion_typed K (t.inline p₀ k₀)) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom
  | .leaf (.ret c) => act_post (rowArr K p₀ k₀) (.ret c)
  | .leaf (.go j q) => by
    refine Fin.cases ?_ (fun j' => ?_) j
    · exact (go_zero_post (rowArr K p₀ k₀) q).trans (ask_sum K q p₀ k₀).symm
    · exact act_post (rowArr K p₀ k₀) (.go j' q)
  | .ask q p kids => by
    have ih := gen_post (K := K + 1) (K' := K) (coprod.desc coprod.inl (sumDesc (rowArr K p₀ k₀) coprod.inr))
      (coprod.inl_desc _ _) p
      (fun x y => treeRegion_typed (K + 1) (kids x y))
      (fun x y => treeRegion_typed K ((kids x y).inline p₀ k₀))
      (fun x y => tree_post p₀ k₀ (kids x y))
    exact (congrArg (· ≫ coprod.desc coprod.inl (sumDesc (rowArr K p₀ k₀) coprod.inr))
        (ask_sum (K + 1) q p kids)).trans
      ((Category.assoc _ _ _).trans ((congrArg (ofRegion (const_typed q) ≫ ·) ih).trans
        (ask_sum K q p fun x y => (kids x y).inline p₀ k₀).symm))

/-- A tree that does not jump to state zero is its renamed tree, landing
in the other states. -/
theorem tree_lower (p₀ : Program) (k₀ : Bool → Bool → Tree K) : ∀ t : Tree (K + 1), t.Above 0 →
    (ofRegion (treeRegion_typed K (t.inline p₀ k₀)) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫
        coprod.map (𝟙 _) (sumInr State (States K)) =
      ofRegion (treeRegion_typed (K + 1) t) ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom
  | .leaf (.ret c), _ =>
    act_nat (sumInr (Φ := signature.Instr) State (States K)) Fin.succ (fun i => (injArr_succ K i).symm) (.ret c)
  | .leaf (.go j q), ab => by
    revert ab
    refine Fin.cases ?_ (fun j' => ?_) j
    · intro ab
      exact absurd ab (Nat.lt_irrefl 0)
    · intro _
      exact act_nat (sumInr (Φ := signature.Instr) State (States K)) Fin.succ
        (fun i => (injArr_succ K i).symm) (.go j' q)
  | .ask q p kids, ab => by
    have ih := gen_post (coprod.map (𝟙 (ofType (Φ := signature.Instr) Bit)) (sumInr State (States K)))
      ((coprod.inl_map _ _).trans (Category.id_comp _)) p
      (fun x y => treeRegion_typed K ((kids x y).inline p₀ k₀))
      (fun x y => treeRegion_typed (K + 1) (kids x y))
      (fun x y => tree_lower p₀ k₀ (kids x y) (ab x y))
    exact (congrArg (· ≫ coprod.map (𝟙 _) (sumInr State (States K)))
        (ask_sum K q p fun x y => (kids x y).inline p₀ k₀)).trans
      ((Category.assoc _ _ _).trans ((congrArg (ofRegion (const_typed q) ≫ ·) ih).trans
        (ask_sum (K + 1) q p kids).symm))

theorem above_inline (p₀ : Program) (k₀ : Bool → Bool → Tree K) (m : Nat) : ∀ t : Tree (K + 1),
    t.Above (m + 1) → (t.inline p₀ k₀).Above m
  | .leaf (.ret _), _ => True.intro
  | .leaf (.go j q), ab => by
    revert ab
    refine Fin.cases ?_ (fun j' => ?_) j
    · intro ab
      exact absurd ab (Nat.not_lt_zero _)
    · intro ab
      exact Nat.lt_of_succ_lt_succ ab
  | .ask _ _ kids, ab => fun x y => above_inline p₀ k₀ m (kids x y) (ab x y)

/-! ## Tables -/

/-- Writing state zero inside the rows that jump to it does not change the
entered loops, when its own row does not jump to it. -/
theorem inlineFront_arrow (t : TreeTable (K + 1)) (fwd : ∀ x y, (t.kids 0 x y).Above 0) (i : Fin (K + 1)) :
    ofRegion (t.inlineFront.entered_typed i) = ofRegion (t.entered_typed i.succ) :=
  dispatch_outline t.inlineFront.rows_typed t.rows_typed (rowArr K (t.prog 0) t.frontKids)
    (gen_post (coprod.map (𝟙 (ofType (Φ := signature.Instr) Bit)) (sumInr State (States K)))
      ((coprod.inl_map _ _).trans (Category.id_comp _)) (t.prog 0)
      (fun x y => treeRegion_typed K (t.frontKids x y)) (fun x y => treeRegion_typed (K + 1) (t.kids 0 x y))
      (fun x y => tree_lower (t.prog 0) (fun _ _ => .leaf (.ret false)) (t.kids 0 x y) (fwd x y))).symm
    (fun i => gen_post (K := K + 1) (K' := K) _ (coprod.inl_desc _ _) (t.prog i.succ)
      (fun x y => treeRegion_typed (K + 1) (t.kids i.succ x y))
      (fun x y => treeRegion_typed K ((t.kids i.succ x y).inline (t.prog 0) t.frontKids))
      (fun x y => tree_post (t.prog 0) t.frontKids (t.kids i.succ x y))) i

/-- The table with its first `n` states written inside the rows that jump
to them has the same entered loops, in default Paper, when those `n` rows
only jump forward. -/
theorem nest_arrow : ∀ (n : Nat) (t : TreeTable (K + n)),
    (∀ k : Fin (K + n + 1), k.val < n → ∀ x y, (t.kids k x y).Above k.val) → ∀ i : Fin (K + 1),
    ofRegion ((TreeTable.nest n t).entered_typed i) = ofRegion (t.entered_typed (shiftN n i))
  | 0, _, _, _ => rfl
  | n + 1, t, fwd, i =>
    (nest_arrow n t.inlineFront
      (fun k hk x y => above_inline _ _ k.val (t.kids k.succ x y) (fwd k.succ (Nat.succ_lt_succ hk) x y)) i).trans
      (inlineFront_arrow t (fun x y => fwd 0 (Nat.succ_pos n) x y) (shiftN n i))

theorem router_nest_arrow (n : Nat) (t : Router (K + n)) (fwd : t.Forward n) (i : Fin (K + 1)) :
    ofRegion ((TreeTable.nest n t.toTrees).entered_typed i) = ofRegion (t.entered_typed (shiftN n i)) :=
  nest_arrow n t.toTrees fwd i

theorem router_nest_eqv (n : Nat) (t : Router (K + n)) (fwd : t.Forward n) (i : Fin (K + 1)) :
    Eqv false [State] ((TreeTable.nest n t.toTrees).entered i) (t.entered (shiftN n i)) [Bit] :=
  (Paper.Extension.Singleton.ofRegion_eq_iff N ((TreeTable.nest n t.toTrees).entered_typed i)
    (t.entered_typed (shiftN n i))).1 (congrArg (π).map (router_nest_arrow n t fwd i))

/-! ## Regression tables -/

theorem chained_forward (a b c o : Bool) (n : Nat) (hn : n ≤ 3) :
    (Router.ofLabels (chainedLabel a b c o) chainedAct).Forward n := by
  intro k hk x y
  match k, hk with
  | 0, _ => cases x <;> cases y <;> first | exact True.intro | (show (_ : Nat) < _; decide)
  | 1, _ => cases x <;> cases y <;> (show (_ : Nat) < _; decide)
  | 2, _ => cases x <;> cases y <;> first | exact True.intro | (show (_ : Nat) < _; decide)
  | 3, hk => exact absurd (Nat.lt_of_lt_of_le hk hn) (by decide)

theorem spiral_forward (a b o : Bool) : (Router.ofLabels (spiralLabel a b o) spiralAct).Forward 2 := by
  intro k hk x y
  match k, hk with
  | 0, _ => show (_ : Nat) < _; decide
  | 1, _ => show (_ : Nat) < _; decide
  | 2, hk => exact absurd hk (by decide)

/-- After two completed exchanges of the spiral the request of `B` is
pending. -/
theorem spiral_prefix (a b o g : Bool) :
    (Except.error b, FreeMonoid.of (event o g (false, false)) *
      (FreeMonoid.of (event a false (false, false)) * 1)) ∈
      (Router.ofLabels (spiralLabel a b o) spiralAct).prefixObservations 2 g :=
  (TableModel.prefix_unfold (spiralLabel a b o) spiralAct 2 g _ _).2 (.inr ⟨false, false, _, rfl,
    show (_, _) ∈ (Router.ofLabels (spiralLabel a b o) spiralAct).prefixObservations 0 false from
      (TableModel.prefix_unfold (spiralLabel a b o) spiralAct 0 false _ _).2 (.inr ⟨false, false, 1, rfl,
        show (_, _) ∈ (Router.ofLabels (spiralLabel a b o) spiralAct).prefixObservations 1 false from
          TableModel.prefix_pending (spiralLabel a b o) spiralAct 1 false⟩)⟩)

theorem spiral_prefix_not (a o g : Bool) {b b' : Bool} (ne : b ≠ b') :
    (Except.error b, FreeMonoid.of (event o g (false, false)) *
      (FreeMonoid.of (event a false (false, false)) * 1)) ∉
      (Router.ofLabels (spiralLabel a b' o) spiralAct).prefixObservations 2 g := by
  intro h
  rcases (TableModel.prefix_unfold (spiralLabel a b' o) spiralAct 2 g _ _).1 h with
    ⟨-, e⟩ | ⟨tag, pl, v, e, hc⟩
  · exact TableModel.one_ne_cons e.symm
  · obtain ⟨ev, rfl⟩ := TableModel.word_cons e
    obtain ⟨-, -, rfl, rfl⟩ := TableModel.event_inj ev
    have h1 : (Except.error b, FreeMonoid.of (event a false (false, false)) * (1 : Word)) ∈
        (Router.ofLabels (spiralLabel a b' o) spiralAct).prefixObservations 0 false := hc
    rcases (TableModel.prefix_unfold (spiralLabel a b' o) spiralAct 0 false _ _).1 h1 with
      ⟨-, e⟩ | ⟨tag, pl, v, e, hc⟩
    · exact TableModel.one_ne_cons e.symm
    · obtain ⟨ev, rfl⟩ := TableModel.word_cons e
      obtain ⟨-, -, rfl, rfl⟩ := TableModel.event_inj ev
      have h2 : (Except.error b, (1 : Word)) ∈
          (Router.ofLabels (spiralLabel a b' o) spiralAct).prefixObservations 1 false := hc
      exact ne (Except.error.inj (TableModel.prefix_one (spiralLabel a b' o) spiralAct 1 false h2))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
