module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Deep.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Outline.Thms
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.RouterReflection

/-! # A deep table equals its expansion -/

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

/-! ## Squares with an arbitrary map on the results -/

section Post

variable {K K' : Nat}
  (φ : ofType (Φ := signature.Instr) Bit ⨿ ofType (States K) ⟶ ofType Bit ⨿ ofType (States K'))

theorem case_post {A B : Ty Empty} {r s r' s' : Region signature.Instr}
    (ha : ValueBranches [A] r [Silmaril.coprod Bit (States K)])
    (hb : ValueBranches [B] s [Silmaril.coprod Bit (States K)])
    (ha' : ValueBranches [A] r' [Silmaril.coprod Bit (States K')])
    (hb' : ValueBranches [B] s' [Silmaril.coprod Bit (States K')])
    (na : (ofRegion ha ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ φ =
      ofRegion ha' ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom)
    (nb : (ofRegion hb ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ φ =
      ofRegion hb' ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom) :
    (ofRegion (caseValueBranches ha hb) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ φ =
      ofRegion (caseValueBranches ha' hb') ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom := by
  rw [← coprod_desc_ofRegion ha hb, ← coprod_desc_ofRegion ha' hb']
  simp only [Category.assoc]
  congr 1
  apply coprod.hom_ext
  · rw [coprod.inl_desc_assoc, coprod.inl_desc_assoc]
    exact (Category.assoc _ _ _).symm.trans na
  · rw [coprod.inr_desc_assoc, coprod.inr_desc_assoc]
    exact (Category.assoc _ _ _).symm.trans nb

theorem seq_post (p : Program) {r r' : Region signature.Instr}
    (hr : ValueBranches [Silmaril.coprod Bit State] r [Silmaril.coprod Bit (States K)])
    (hr' : ValueBranches [Silmaril.coprod Bit State] r' [Silmaril.coprod Bit (States K')])
    (n : (ofRegion hr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ φ =
      ofRegion hr' ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom) :
    (ofRegion (seqValueBranches (step_typed p) hr) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ φ =
      ofRegion (seqValueBranches (step_typed p) hr') ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom := by
  rw [← Paper.TypeCategory.ofRegion_comp (step_typed p) hr (seqValueBranches (step_typed p) hr),
    ← Paper.TypeCategory.ofRegion_comp (step_typed p) hr' (seqValueBranches (step_typed p) hr')]
  simp only [Category.assoc]
  exact congrArg (ofRegion (step_typed p) ≫ ·) ((Category.assoc _ _ _).symm.trans n)

end Post

/-! ## Outlining a front state of a dispatcher -/

/-- If the row of state zero is `r₀` landing in the other states, and
running `r₀` in place of the jumps to state zero turns the other rows
into the rows of a smaller dispatcher, the entered loops agree in default
Paper. -/
theorem dispatch_outline {K : Nat} {rows : Fin (K + 1) → Region signature.Instr}
    {rows' : Fin (K + 2) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [Silmaril.coprod Bit (States K)])
    (h' : ∀ i, ValueBranches [State] (rows' i) [Silmaril.coprod Bit (States (K + 1))])
    (r₀ : ofType (Φ := signature.Instr) State ⟶ ofType Bit ⨿ ofType (States K))
    (front : ofRegion (h' 0) ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom =
      r₀ ≫ coprod.map (𝟙 _) (sumInr State (States K)))
    (row : ∀ i, (ofRegion (h' i.succ) ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom) ≫
        coprod.desc coprod.inl (sumDesc r₀ coprod.inr) =
      ofRegion (h i) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) (i : Fin (K + 1)) :
    ofRegion (dispatchEntered_typed h i) = ofRegion (dispatchEntered_typed h' i.succ) := by
  have eJ : ofRegion (dispatch_typed K h) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom =
      (ofRegion (dispatch_typed K fun i => h' i.succ) ≫
        (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom) ≫
          coprod.desc coprod.inl (sumDesc r₀ coprod.inr) := by
    apply inj_ext K
    intro j
    have a := inj_dispatch K h j
    have b := inj_dispatch K (fun i => h' i.succ) j
    rw [← Category.assoc, a, ← row j, ← b]
    simp only [Category.assoc]
  have eG : ofRegion (dispatch_typed (K + 1) h') ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom =
      sumDesc (r₀ ≫ coprod.map (𝟙 _) (sumInr State (States K)))
        (ofRegion (dispatch_typed K fun i => h' i.succ) ≫
          (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom) := by
    have e : ofRegion (dispatch_typed (K + 1) h') =
        (sumIso (Φ := signature.Instr) State (States K)).hom ≫
          coprod.desc (ofRegion (h' 0)) (ofRegion (dispatch_typed K fun i => h' i.succ)) :=
      (coprod_desc_ofRegion (h' 0) (dispatch_typed K fun i => h' i.succ)).symm
    rw [e, ← front]
    exact sumDesc_comp _ _ _
  rw [dispatchEntered_arrow h i, dispatchEntered_arrow h' i.succ, dispatchLoop_arrow h, dispatchLoop_arrow h',
    eJ, eG, iterate_outline]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ Paper.TypeCategory.iterate _) (injArr_succ K i).symm)

/-! ## Deep rows -/

variable {K : Nat}

/-- The continuation row as an arrow. -/
noncomputable abbrev contArr (K : Nat) (pc : Program) (ac : Bool → Bool → Act K) :
    ofType (Φ := signature.Instr) State ⟶ ofType Bit ⨿ ofType (States K) :=
  ofRegion (routerRow_typed K pc ac) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom

theorem succ_inline (r₀ : ofType (Φ := signature.Instr) State ⟶ ofType Bit ⨿ ofType (States K))
    (j : Fin (K + 1)) : injArr (K + 1) j.succ ≫ sumDesc r₀ coprod.inr = injArr K j ≫ coprod.inr := by
  have e : injArr (K + 1) j.succ = injArr K j ≫ sumInr (Φ := signature.Instr) State (States K) :=
    injArr_succ K j
  rw [e, Category.assoc, sumInr_sumDesc]

theorem zero_inline (r₀ : ofType (Φ := signature.Instr) State ⟶ ofType Bit ⨿ ofType (States K)) :
    injArr (K + 1) 0 ≫ sumDesc r₀ coprod.inr = r₀ := by
  have e : injArr (K + 1) 0 = sumInl (Φ := signature.Instr) State (States K) := injArr_zero K
  rw [e, sumInl_sumDesc]

theorem act_post (r₀ : ofType (Φ := signature.Instr) State ⟶ ofType Bit ⨿ ofType (States K)) (a : Act K) :
    (ofRegion (act_typed (K + 1) (a.map Fin.succ)) ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom) ≫
        coprod.desc coprod.inl (sumDesc r₀ coprod.inr) =
      ofRegion (act_typed K a) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom := by
  cases a with
  | ret c =>
    have e : ofRegion (act_typed (K + 1) ((Act.ret c : Act K).map Fin.succ)) =
        ofRegion (r := .br 0 (bitTm c)) (.br rfl (bitTm_typed c)) ≫
          (coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).inv) :=
      br_inl (bitTm_typed c)
    have e' : ofRegion (act_typed K (.ret c)) =
        ofRegion (r := .br 0 (bitTm c)) (.br rfl (bitTm_typed c)) ≫
          (coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
      br_inl (bitTm_typed c)
    rw [e, e']
    simp
  | go j q =>
    have e : ofRegion (act_typed (K + 1) ((Act.go j q : Act K).map Fin.succ)) =
        (ofRegion (r := .br 0 (.inl (bitTm q))) (.br (L := [State]) rfl (.inl (bitTm_typed q))) ≫
            injArr (K + 1) j.succ) ≫
          (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).inv) :=
      (br_inr (injTm_typed (.inl (bitTm_typed q)) (K + 1) j.succ)).trans
        (congrArg (· ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).inv))
          (injOf_eq (.inl (bitTm_typed q)) (K + 1) j.succ))
    have e' : ofRegion (act_typed K (.go j q)) =
        (ofRegion (r := .br 0 (.inl (bitTm q))) (.br (L := [State]) rfl (.inl (bitTm_typed q))) ≫ injArr K j) ≫
          (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
      (br_inr (injTm_typed (.inl (bitTm_typed q)) K j)).trans
        (congrArg (· ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv))
          (injOf_eq (.inl (bitTm_typed q)) K j))
    rw [e, e']
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, coprod.inr_desc]
    rw [succ_inline]

theorem ask_post (pc : Program) (ac : Bool → Bool → Act K) (q : Bool) :
    (ofRegion (act_typed (K + 1) (.go 0 q)) ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom) ≫
        coprod.desc coprod.inl (sumDesc (contArr K pc ac) coprod.inr) =
      ofRegion (inline_typed K pc ac q) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom := by
  have e : ofRegion (act_typed (K + 1) (.go 0 q)) =
      (ofRegion (const_typed q) ≫ injArr (K + 1) 0) ≫
        (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).inv) :=
    (br_inr (injTm_typed (.inl (bitTm_typed q)) (K + 1) 0)).trans
      (congrArg (· ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).inv))
        (injOf_eq (.inl (bitTm_typed q)) (K + 1) 0))
  have e' : ofRegion (inline_typed K pc ac q) =
      ofRegion (const_typed q) ≫ ofRegion (routerRow_typed K pc ac) :=
    (Paper.TypeCategory.ofRegion_comp (const_typed q) (routerRow_typed K pc ac) _).symm
  rw [e, e']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, coprod.inr_desc]
  rw [zero_inline]

theorem dead_post (r₀ : ofType (Φ := signature.Instr) State ⟶ ofType Bit ⨿ ofType (States K)) :
    (ofRegion (dead_typed (K + 1)) ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom) ≫
        coprod.desc coprod.inl (sumDesc r₀ coprod.inr) =
      ofRegion (dead_typed K) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom := by
  have e : ofRegion (dead_typed (K + 1)) =
      ofRegion (r := .br 0 (.inl .unit)) (.br (L := [Bit]) rfl (.inl (A := Ty.unit) (B := Ty.unit) .unit)) ≫
        (coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).inv) :=
    br_inl (X := Silmaril.empty) (.inl .unit)
  have e' : ofRegion (dead_typed K) =
      ofRegion (r := .br 0 (.inl .unit)) (.br (L := [Bit]) rfl (.inl (A := Ty.unit) (B := Ty.unit) .unit)) ≫
        (coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States K)).inv) :=
    br_inl (X := Silmaril.empty) (.inl .unit)
  rw [e, e']
  simp

theorem leaf_post (pc : Program) (ac : Bool → Bool → Act K) (x : Leaf K) :
    (ofRegion (act_typed (K + 1) x.expand) ≫ (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom) ≫
        coprod.desc coprod.inl (sumDesc (contArr K pc ac) coprod.inr) =
      ofRegion (leaf_typed K pc ac x) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom := by
  cases x with
  | act a => exact act_post (contArr K pc ac) a
  | ask q => exact ask_post pc ac q

/-- Running the continuation in place of the jumps to the new state turns
an expanded row into the deep row. -/
theorem deepRow_post (p pc : Program) (ac : Bool → Bool → Act K) (b : Bool → Bool → Leaf K) :
    (ofRegion (routerRow_typed (K + 1) p fun x y => (b x y).expand) ≫
        (sumIso (Φ := signature.Instr) Bit (States (K + 1))).hom) ≫
        coprod.desc coprod.inl (sumDesc (contArr K pc ac) coprod.inr) =
      ofRegion (deepRow_typed K p pc ac b) ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom :=
  seq_post _ p _ _
    (case_post _ _ _ _ _ (case_post _ _ _ _ _ (leaf_post pc ac _) (leaf_post pc ac _))
      (case_post _ _ _ _ _ (case_post _ _ _ _ _ (leaf_post pc ac _) (leaf_post pc ac _))
        (dead_post (contArr K pc ac))))

/-- A deep table and its expansion have the same entered loops, as arrows
of default Paper. -/
theorem deep_expand_arrow (t : Deep K) (i : Fin (K + 1)) :
    ofRegion (t.entered_typed i) = ofRegion (t.expand.entered_typed i.succ) :=
  dispatch_outline t.rows_typed t.expand.rows_typed (contArr K t.cont t.contAct)
    (routerRow_nat (sumInr (Φ := signature.Instr) State (States K)) Fin.succ
      (fun i => (injArr_succ K i).symm) t.cont t.cont rfl t.contAct (t.expand.act 0) (fun _ _ => rfl)).symm
    (fun i => deepRow_post (t.prog i) t.cont t.contAct (t.leaf i)) i

theorem deep_expand_eqv (t : Deep K) (i : Fin (K + 1)) :
    Eqv false [State] (t.entered i) (t.expand.entered i.succ) [Bit] :=
  (Paper.Extension.Singleton.ofRegion_eq_iff N (t.entered_typed i) (t.expand.entered_typed i.succ)).1
    (congrArg (π).map (deep_expand_arrow t i))

theorem expand_ofLabels (label : Fin (K + 1) → Bool) (leaf : Fin (K + 1) → Bool → Bool → Leaf K) (lc : Bool)
    (ac : Bool → Bool → Act K) :
    (Deep.ofLabels label leaf lc ac).expand = Router.ofLabels (deepLabel label lc) (deepAct leaf ac) := by
  have progs : (Deep.ofLabels label leaf lc ac).expand.prog =
      fun x => (labelPoll (deepLabel label lc x)).program := by
    funext x
    refine Fin.cases ?_ (fun i => ?_) x <;> rfl
  exact congrArg (fun p => Router.mk p (deepAct leaf ac)) progs

theorem deep_labels_eqv (label : Fin (K + 1) → Bool) (leaf : Fin (K + 1) → Bool → Bool → Leaf K) (lc : Bool)
    (ac : Bool → Bool → Act K) (i : Fin (K + 1)) :
    Eqv false [State] ((Deep.ofLabels label leaf lc ac).entered i)
      ((Router.ofLabels (deepLabel label lc) (deepAct leaf ac)).entered i.succ) [Bit] := by
  have e := deep_expand_eqv (Deep.ofLabels label leaf lc ac) i
  rw [expand_ofLabels] at e
  exact e

/-! ## The two-request row against explicit rows -/

abbrev duoSplit (x : Fin 2) (y : Fin 3) : Prop := (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2)

theorem duoSplit_label (a c : Bool) (x : Fin 2) (y : Fin 3) (r : duoSplit x y) :
    deepLabel (fun _ => a) c x = splitLabel a c y := by
  rcases r with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem duoSplit_act (x : Fin 2) (y : Fin 3) (r : duoSplit x y) (tag pl : Bool) :
    Act.Rel duoSplit (deepAct duoLeaf duoCont x tag pl) (splitAct y tag pl) := by
  rcases r with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases tag <;> cases pl <;> decide

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
