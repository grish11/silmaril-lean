module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.CaptureTables
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Composite.Entry.Defs

/-! # Split states: resetting the query, the split table, and its recombination -/

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
open Paper.TypeCategory (iterate_roll)

/-! ## Resetting the query of every row, in default Paper -/

section Reset

variable {M : Nat} (c : Fin (M + 1) → Bool)

theorem inj_reset (x : Fin (M + 1)) :
    injArr M x ≫ resetArr c = ofRegion (reset_typed (c x)) ≫ injArr M x :=
  (inj_dispatch M (resetRows_typed c (entry_typed M)) x).trans
    (ofRegion_comp (reset_typed (c x)) (entry_typed M x) _).symm

variable {rows : Fin (M + 1) → Region signature.Instr}
  (h : ∀ x, ValueBranches [State] (rows x) [Silmaril.coprod Bit (States M)])

theorem reset_dispatch :
    resetArr c ≫ ofRegion (dispatch_typed M h) = ofRegion (dispatch_typed M (resetRows_typed c h)) := by
  apply inj_ext M
  intro x
  rw [← Category.assoc, inj_reset, Category.assoc, inj_dispatch M h x,
    inj_dispatch M (resetRows_typed c h) x]
  exact ofRegion_comp (reset_typed (c x)) (h x) _

/-- The loop of the reset rows is the reset followed by the loop, when
every repeat already carries the Bit of its target. -/
theorem reset_loop (m : Matched c h) :
    ofRegion (dispatchLoop_typed (resetRows_typed c h)) =
      resetArr c ≫ ofRegion (dispatchLoop_typed h) := by
  have fix : (ofRegion (dispatch_typed M h) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫
      coprod.map (𝟙 _) (resetArr c) =
      ofRegion (dispatch_typed M h) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom := by
    apply inj_ext M
    intro x
    simp only [← Category.assoc]
    rw [inj_dispatch M h x]
    exact m x
  have roll := iterate_roll (resetArr c)
    (ofRegion (dispatch_typed M h) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom)
  rw [fix, ← Category.assoc, reset_dispatch c h] at roll
  rw [dispatchLoop_arrow (resetRows_typed c h), dispatchLoop_arrow h]
  exact roll

/-- So the reset rows entered at a state are the reset followed by the
rows entered at that state. -/
theorem reset_entered (m : Matched c h) (x : Fin (M + 1)) :
    ofRegion (dispatchEntered_typed (resetRows_typed c h) x) =
      ofRegion (reset_typed (c x)) ≫ ofRegion (dispatchEntered_typed h x) := by
  rw [dispatchEntered_arrow (resetRows_typed c h) x, dispatchEntered_arrow h x, reset_loop c h m,
    ← Category.assoc, inj_reset, Category.assoc]

end Reset

/-! ## The reset on a constant, and on a region -/

/-- A Bit constant followed by a case on it takes the arm of the constant,
in default Paper. -/
theorem bit_case {D : Ty Empty} (q : Bool) {r₀ r₁ : Region signature.Instr} (h₀ : ValueBranches [U] r₀ [D])
    (h₁ : ValueBranches [U] r₁ [D]) :
    ofRegion (seqValueBranches (bit_typed q) (caseValueBranches h₀ h₁)) =
      ofRegion (match q with | false => h₀ | true => h₁ :
        ValueBranches [U] (match q with | false => r₀ | true => r₁) [D]) := by
  cases q
  · exact (case_inl_arrow (X := U) (B := U) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl) h₀ h₁).trans
      ((ofRegion_comp unitId h₀ (seqValueBranches unitId h₀)).symm.trans
        (by rw [ofRegion_id, Category.id_comp]))
  · exact (case_inr_arrow (X := U) (A := U) (t := (.var 0 : Tm signature.Instr)) (.var (i := 0) rfl) h₀ h₁).trans
      ((ofRegion_comp unitId h₁ (seqValueBranches unitId h₁)).symm.trans
        (by rw [ofRegion_id, Category.id_comp]))

/-- A constant state followed by a case on the state takes the arm of
its Bit, in default Paper. -/
theorem const_case {D : Ty Empty} (q : Bool) {r₀ r₁ d : Region signature.Instr} (h₀ : ValueBranches [U] r₀ [D])
    (h₁ : ValueBranches [U] r₁ [D]) (hd : ValueBranches [Silmaril.empty] d [D]) :
    ofRegion (seqValueBranches (const_typed q) (caseValueBranches (caseValueBranches h₀ h₁) hd)) =
      ofRegion (match q with | false => h₀ | true => h₁ :
        ValueBranches [U] (match q with | false => r₀ | true => r₁) [D]) :=
  (case_inl_arrow (X := U) (B := Silmaril.empty) (t := bitTm q) (bitTm_typed q)
    (caseValueBranches h₀ h₁) hd).trans (bit_case q h₀ h₁)

theorem const_reset (q : Bool) :
    ofRegion (const_typed q) ≫ ofRegion (reset_typed q) = ofRegion (const_typed q) := by
  have a := ofRegion_comp (const_typed q) (reset_typed q) (seqValueBranches (const_typed q) (reset_typed q))
  have b := const_case q (const_typed q) (const_typed q) emptyState_typed
  cases q <;> exact a.trans b

/-- Regions out of the empty type are equal, in default Paper. -/
theorem empty_ext {D : Ty Empty} {r s : Region signature.Instr} (hr : ValueBranches [Silmaril.empty] r [D])
    (hs : ValueBranches [Silmaril.empty] s [D]) : ofRegion hr = ofRegion hs :=
  (Paper.TypeCategory.ofRegion_eq_iff _ _).mpr
    (.cfgEta (.native (.initial (a := .var 0) (.var rfl) hr.hasType hs.hasType)))

/-- Two regions that agree on a constant state agree after the reset to it. -/
theorem q_reset_congr {D : Ty Empty} (q : Bool) {k k' : Region signature.Instr}
    (h : ValueBranches [State] k [D]) (h' : ValueBranches [State] k' [D])
    (e : QLit (seqValueBranches (const_typed q) h) = QLit (seqValueBranches (const_typed q) h')) :
    QLit (seqValueBranches (reset_typed q) h) = QLit (seqValueBranches (reset_typed q) h') := by
  have split : ∀ {k : Region signature.Instr} (h : ValueBranches [State] k [D]),
      QLit (seqValueBranches (reset_typed q) h) =
        QLit (caseValueBranches (caseValueBranches (seqValueBranches (const_typed q) h)
          (seqValueBranches (const_typed q) h)) (seqValueBranches emptyState_typed h)) := fun h =>
    ((q_comp (reset_typed q) h).trans (((π).map_comp _ _).symm.trans (congrArg (π).map
      (case_seq_arrow (caseValueBranches (const_typed q) (const_typed q)) emptyState_typed h)))).trans
      (q_case_congr (seqValueBranches (caseValueBranches (const_typed q) (const_typed q)) h)
        (seqValueBranches emptyState_typed h)
        (caseValueBranches (seqValueBranches (const_typed q) h) (seqValueBranches (const_typed q) h))
        (seqValueBranches emptyState_typed h)
        ((q_comp (caseValueBranches (const_typed q) (const_typed q)) h).trans
          (((π).map_comp _ _).symm.trans (congrArg (π).map
            (case_seq_arrow (const_typed q) (const_typed q) h)))) rfl)
  rw [split h, split h']
  exact q_case_congr
    (caseValueBranches (seqValueBranches (const_typed q) h) (seqValueBranches (const_typed q) h))
    (seqValueBranches emptyState_typed h)
    (caseValueBranches (seqValueBranches (const_typed q) h') (seqValueBranches (const_typed q) h'))
    (seqValueBranches emptyState_typed h')
    (q_case_congr (seqValueBranches (const_typed q) h) (seqValueBranches (const_typed q) h)
      (seqValueBranches (const_typed q) h') (seqValueBranches (const_typed q) h') e e)
    (congrArg (π).map (empty_ext (seqValueBranches emptyState_typed h) (seqValueBranches emptyState_typed h')))

/-! ## Routers whose repeats carry the Bit of their target -/

section Carry

variable {M : Nat} (c : Fin (M + 1) → Bool)

theorem act_matched (a : Act M) (hc : a.Carries c) :
    (ofRegion (act_typed M a) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom) ≫
        coprod.map (𝟙 _) (resetArr c) =
      ofRegion (act_typed M a) ≫ (sumIso (Φ := signature.Instr) Bit (States M)).hom := by
  cases a with
  | ret b =>
    have e : ofRegion (act_typed M (.ret b)) =
        ofRegion (r := .br 0 (bitTm b)) (.br rfl (bitTm_typed b)) ≫
          (coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (States M)).inv) :=
      br_inl (bitTm_typed b)
    rw [e]
    simp
  | go x q =>
    have cx : c x = q := hc
    have e : ofRegion (act_typed M (.go x q)) =
        (ofRegion (const_typed q) ≫ injArr M x) ≫
          (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States M)).inv) :=
      (br_inr (injTm_typed (.inl (bitTm_typed q)) M x)).trans
        (congrArg (· ≫ (coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (States M)).inv))
          (injOf_eq (.inl (bitTm_typed q)) M x))
    rw [e]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, coprod.inr_map]
    rw [← Category.assoc (injArr M x), inj_reset, cx, Category.assoc, ← Category.assoc (ofRegion (const_typed q)),
      const_reset]

/-- A router all of whose repeats carry the Bit of their target is matched. -/
theorem router_matched (t : Router M) (hc : ∀ x a b, (t.act x a b).Carries c) : Matched c t.rows_typed :=
  fun x => gen_post (coprod.map (𝟙 _) (resetArr c)) (by simp) (t.prog x)
    (fun a b => act_typed M (t.act x a b)) (fun a b => act_typed M (t.act x a b))
    (fun a b => act_matched c (t.act x a b) (hc x a b))

end Carry

/-! ## The split states -/

section Index

variable {K : Nat}

theorem splitRow_idx (j : Fin (K + 1)) (q : Bool) : splitRow (splitIdx j q) = j := by
  cases q
  · exact joinIdx_front K id id j
  · exact joinIdx_tail K id id j

theorem splitBit_idx (j : Fin (K + 1)) (q : Bool) : splitBit (splitIdx j q) = q := by
  cases q
  · exact joinIdx_front K (fun _ => false) (fun _ => true) j
  · exact joinIdx_tail K (fun _ => false) (fun _ => true) j

theorem redirect_row (a : Act K) : (redirect a).map splitRow = a := by
  cases a with
  | ret c => rfl
  | go j q => exact congrArg (fun i => Act.go i q) (splitRow_idx j q)

theorem redirect_carries (a : Act K) : (redirect a).Carries splitBit := by
  cases a with
  | ret c => exact True.intro
  | go j q => exact splitBit_idx j q

end Index

/-! ## The split table, in the quotient -/

section Table

variable {K : Nat} (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)

theorem split_matched : Matched splitBit (entrySplit l₁ l₂ act).rows_typed :=
  router_matched splitBit (entrySplit l₁ l₂ act) fun x a b => redirect_carries (act (splitRow x) a b)

theorem duo_matched : Matched splitBit (entryDuo l₁ l₂ act).rows_typed :=
  router_matched splitBit (entryDuo l₁ l₂ act) fun x a b => by
    cases a
    · exact redirect_carries (act (splitRow x) false (splitBit x))
    · exact redirect_carries (act (splitRow x) true b)

/-- A row that keeps its entry state, entered with the constant `q`, is
the two-request row whose left return is `q`. -/
theorem entry_row_const (M : Nat) (a : Bool → Bool → Act M) (l₁ l₂ q : Bool) :
    QLit (seqValueBranches (const_typed q) (routerRow_typed M (entryProgram l₁ l₂) a)) =
      QLit (seqValueBranches (const_typed q) (routerRow_typed M (duoProgram l₁ l₂) (keptAct a q))) := by
  have fx := fixed_ask_region (fun x y => act_typed M (a x y)) q (entry_fix l₁ l₂ q)
  have rg : (fun x y => keptRegions (fun x y => Region.br 0 (actTm M (a x y))) q x y) =
      fun x y => Region.br 0 (actTm M (keptAct a q x y)) :=
    funext fun x => funext fun y => by cases x <;> rfl
  exact fx.trans (q_region_congr (congrArg (fun k => constEntry q (genRow (duoProgram l₁ l₂) k)) rg)
    (seqValueBranches (const_typed q) (genRow_typed (duoProgram l₁ l₂)
      (kept_typed (fun x y => act_typed M (a x y)) q)))
    (seqValueBranches (const_typed q) (routerRow_typed M (duoProgram l₁ l₂) (keptAct a q))))

theorem split_row_const (x : Fin (K + (K + 1) + 1)) :
    QLit (seqValueBranches (const_typed (splitBit x)) ((entrySplit l₁ l₂ act).rows_typed x)) =
      QLit (seqValueBranches (const_typed (splitBit x)) ((entryDuo l₁ l₂ act).rows_typed x)) :=
  entry_row_const (K + (K + 1)) (fun a b => redirect (act (splitRow x) a b)) (l₁ (splitRow x))
    (l₂ (splitRow x)) (splitBit x)

/-- After the reset, the split table of rows that keep their entry state
and the split table of two-request rows have the same entered loops. -/
theorem split_reset (x : Fin (K + (K + 1) + 1)) :
    QLit (reset_typed (splitBit x)) ≫ QLit ((entrySplit l₁ l₂ act).entered_typed x) =
      QLit (reset_typed (splitBit x)) ≫ QLit ((entryDuo l₁ l₂ act).entered_typed x) := by
  have rows := (Paper.Extension.Singleton.ofRegion_eq_iff N
    (dispatchEntered_typed (resetRows_typed splitBit (entrySplit l₁ l₂ act).rows_typed) x)
    (dispatchEntered_typed (resetRows_typed splitBit (entryDuo l₁ l₂ act).rows_typed) x)).2
    (dispatch_rows_eqv (resetRows_typed splitBit (entrySplit l₁ l₂ act).rows_typed)
      (resetRows_typed splitBit (entryDuo l₁ l₂ act).rows_typed)
      (fun i => q_reset_congr (splitBit i) ((entrySplit l₁ l₂ act).rows_typed i)
        ((entryDuo l₁ l₂ act).rows_typed i) (split_row_const l₁ l₂ act i)) x)
  have a := congrArg (π).map
    (reset_entered splitBit (entrySplit l₁ l₂ act).rows_typed (split_matched l₁ l₂ act) x)
  have b := congrArg (π).map (reset_entered splitBit (entryDuo l₁ l₂ act).rows_typed (duo_matched l₁ l₂ act) x)
  rw [(π).map_comp] at a b
  exact a.symm.trans (rows.trans b)

/-- The split table entered at a split state of row `j` is the original
table entered at `j`. This uses the phase-uniformity fold of router
morphisms. -/
theorem split_fold (j : Fin (K + 1)) (q : Bool) :
    Eqv false [State] ((entrySplit l₁ l₂ act).entered (splitIdx j q)) ((entryRouter l₁ l₂ act).entered j)
      [Bit] := by
  have hprog : ∀ x, (entrySplit l₁ l₂ act).prog x = (entryRouter l₁ l₂ act).prog (splitRow x) := fun _ => rfl
  have hact : ∀ x a b, (entryRouter l₁ l₂ act).act (splitRow x) a b =
      ((entrySplit l₁ l₂ act).act x a b).map splitRow := fun x a b => (redirect_row (act (splitRow x) a b)).symm
  have fold := router_morphism_eqv (entrySplit l₁ l₂ act) (entryRouter l₁ l₂ act) splitRow hprog hact
    (splitIdx j q)
  rwa [splitRow_idx] at fold

theorem q_const_reset (q : Bool) : QLit (const_typed q) ≫ QLit (reset_typed q) = QLit (const_typed q) :=
  ((π).map_comp _ _).symm.trans (congrArg (π).map (const_reset q))

/-- The original table entered with the constant `q` at row `j` is the
table of literal request trees entered with `q` at the split state. -/
theorem entry_const (j : Fin (K + 1)) (q : Bool) :
    QLit (const_typed q) ≫ QLit ((entryRouter l₁ l₂ act).entered_typed j) =
      QLit (const_typed q) ≫ QLit ((entrySource l₁ l₂ act).entered_typed (splitIdx j q)) := by
  have fold₀ := split_fold l₁ l₂ act j q
  have fold : QLit ((entrySplit l₁ l₂ act).entered_typed (splitIdx j q)) =
      QLit ((entryRouter l₁ l₂ act).entered_typed j) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 fold₀
  have duo : QLit ((entryDuo l₁ l₂ act).entered_typed (splitIdx j q)) =
      QLit ((entrySource l₁ l₂ act).entered_typed (splitIdx j q)) :=
    (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2
      (duo_table_eqv (fun x => l₁ (splitRow x)) (fun x => l₂ (splitRow x)) (entryAct act)
        (fun i => duo_stepFactors _ _) (splitIdx j q))
  have reset : QLit (reset_typed q) ≫ QLit ((entrySplit l₁ l₂ act).entered_typed (splitIdx j q)) =
      QLit (reset_typed q) ≫ QLit ((entryDuo l₁ l₂ act).entered_typed (splitIdx j q)) := by
    have r := split_reset l₁ l₂ act (splitIdx j q)
    rwa [splitBit_idx] at r
  have pre : ∀ f : (π).obj (ofType (Φ := signature.Instr) State) ⟶ (π).obj (ofType Bit),
      QLit (const_typed q) ≫ f = QLit (const_typed q) ≫ QLit (reset_typed q) ≫ f := fun f =>
    ((congrArg (· ≫ f) (q_const_reset q)).symm.trans (Category.assoc _ _ _))
  exact (congrArg (QLit (const_typed q) ≫ ·) fold.symm).trans
    ((pre _).trans ((congrArg (QLit (const_typed q) ≫ ·) reset).trans
      ((pre _).symm.trans (congrArg (QLit (const_typed q) ≫ ·) duo))))

end Table

/-! ## A state is one of its two constants -/

theorem emptyState_arrow : ofRegion emptyState_typed =
    coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (packedExitType ([] : LCtx (Ty Empty)))).inv :=
  (br_inr (.var rfl)).trans ((congrArg (· ≫ _) (ofRegion_id _)).trans (Category.id_comp _))

/-- A region on a state is the case on the state's Bit of the region
entered with the two constants, in default Paper. -/
theorem state_eta {r : Region signature.Instr} (h : ValueBranches [State] r [Bit]) :
    ofRegion h = ofRegion (caseEntry_typed (constEntry_typed false h) (constEntry_typed true h)) := by
  have bits : ofRegion (caseValueBranches (constEntry_typed false h) (constEntry_typed true h)) =
      ofRegion bitState_typed ≫ ofRegion h := by
    rw [← coprod_desc_ofRegion (constEntry_typed false h) (constEntry_typed true h),
      ← ofRegion_comp (const_typed false) h (constEntry_typed false h),
      ← ofRegion_comp (const_typed true) h (constEntry_typed true h), const_arrow, const_arrow,
      bitTm_false_arrow, bitTm_true_arrow]
    have e : coprod.desc
        (((coprod.inl ≫ (sumIso (Φ := signature.Instr) Ty.unit Ty.unit).inv) ≫ ofRegion bitState_typed) ≫
          ofRegion h)
        (((coprod.inr ≫ (sumIso (Φ := signature.Instr) Ty.unit Ty.unit).inv) ≫ ofRegion bitState_typed) ≫
          ofRegion h) =
        (sumIso (Φ := signature.Instr) Ty.unit Ty.unit).inv ≫ ofRegion bitState_typed ≫ ofRegion h := by
      apply coprod.hom_ext <;> simp
    rw [e, Iso.hom_inv_id_assoc]
  have dead : ofRegion deadBit_typed = ofRegion emptyState_typed ≫ ofRegion h :=
    (empty_ext deadBit_typed (seqValueBranches emptyState_typed h)).trans
      (ofRegion_comp emptyState_typed h (seqValueBranches emptyState_typed h)).symm
  have rhs : ofRegion (caseEntry_typed (constEntry_typed false h) (constEntry_typed true h)) =
      (sumIso (Φ := signature.Instr) Bit (packedExitType ([] : LCtx (Ty Empty)))).hom ≫
        coprod.desc (ofRegion (caseValueBranches (constEntry_typed false h) (constEntry_typed true h)))
          (ofRegion deadBit_typed) :=
    (coprod_desc_ofRegion (caseValueBranches (constEntry_typed false h) (constEntry_typed true h))
      deadBit_typed).symm
  rw [rhs, bits, dead, bitState_arrow, emptyState_arrow]
  have e : coprod.desc
      ((coprod.inl ≫ (sumIso (Φ := signature.Instr) Bit (packedExitType ([] : LCtx (Ty Empty)))).inv) ≫
        ofRegion h)
      ((coprod.inr ≫ (sumIso (Φ := signature.Instr) Bit (packedExitType ([] : LCtx (Ty Empty)))).inv) ≫
        ofRegion h) =
      (sumIso (Φ := signature.Instr) Bit (packedExitType ([] : LCtx (Ty Empty)))).inv ≫ ofRegion h := by
    apply coprod.hom_ext <;> simp
  rw [e, Iso.hom_inv_id_assoc]

/-! ## Loops that are literal sources at each constant -/

theorem q_const {D : Ty Empty} (q : Bool) {r : Region signature.Instr} (h : ValueBranches [State] r [D]) :
    QLit (constEntry_typed q h) = QLit (const_typed q) ≫ QLit h :=
  q_comp (const_typed q) h

section Pointed

variable {K K' : Nat} {r r' : Region signature.Instr} {t : Bool → LTable K} {x : Bool → Fin (K + 1)}
  {t' : Bool → LTable K'} {x' : Bool → Fin (K' + 1)}

/-- Two loops whose sources agree at each constant are equal. -/
theorem pointed_eqv (h : ValueBranches [State] r [Bit]) (h' : ValueBranches [State] r' [Bit])
    (hp : Pointed r t x) (hp' : Pointed r' t' x')
    (e : ∀ q, Eqv false [State] ((t q).entered (x q)) ((t' q).entered (x' q)) [Bit]) :
    Eqv false [State] r r' [Bit] := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N h h').1
  have point : ∀ q, QLit (constEntry_typed q h) = QLit (constEntry_typed q h') := fun q =>
    ((Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q h)
      (constEntry_typed q ((t q).entered_typed (x q)))).2 (hp q)).trans
      (((q_const q ((t q).entered_typed (x q))).trans
        ((congrArg (QLit (const_typed q) ≫ ·)
          ((Paper.Extension.Singleton.ofRegion_eq_iff N ((t q).entered_typed (x q))
            ((t' q).entered_typed (x' q))).2 (e q))).trans (q_const q ((t' q).entered_typed (x' q))).symm)).trans
        ((Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q h')
          (constEntry_typed q ((t' q).entered_typed (x' q)))).2 (hp' q)).symm)
  exact (congrArg (π).map (state_eta h)).trans
    ((q_case_congr (caseValueBranches (constEntry_typed false h) (constEntry_typed true h)) deadBit_typed
      (caseValueBranches (constEntry_typed false h') (constEntry_typed true h')) deadBit_typed
      (q_case_congr (constEntry_typed false h) (constEntry_typed true h) (constEntry_typed false h')
        (constEntry_typed true h') (point false) (point true)) rfl).trans
      (congrArg (π).map (state_eta h')).symm)

end Pointed

/-- A loop equal to a table of literal request trees is such a table at
each constant. -/
theorem pointed_of_eqv {K : Nat} {r : Region signature.Instr} (h : ValueBranches [State] r [Bit])
    (t : LTable K) (x : Fin (K + 1)) (e : Eqv false [State] r (t.entered x) [Bit]) :
    Pointed r (fun _ => t) (fun _ => x) := fun q =>
  (Paper.Extension.Singleton.ofRegion_eq_iff N (constEntry_typed q h) (constEntry_typed q (t.entered_typed x))).1
    ((q_const q h).trans ((congrArg (QLit (const_typed q) ≫ ·)
      ((Paper.Extension.Singleton.ofRegion_eq_iff N h (t.entered_typed x)).2 e)).trans
        (q_const q (t.entered_typed x)).symm))

/-- The table of rows that keep their entry state is the split table of
literal request trees at each constant. -/
theorem entry_pointed {K : Nat} (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
    (j : Fin (K + 1)) :
    Pointed ((entryRouter l₁ l₂ act).entered j) (fun _ => entrySource l₁ l₂ act) (splitIdx j) := fun q =>
  (Paper.Extension.Singleton.ofRegion_eq_iff N
    (constEntry_typed q ((entryRouter l₁ l₂ act).entered_typed j))
    (constEntry_typed q ((entrySource l₁ l₂ act).entered_typed (splitIdx j q)))).1
    ((q_const q ((entryRouter l₁ l₂ act).entered_typed j)).trans
      ((entry_const l₁ l₂ act j q).trans
        (q_const q ((entrySource l₁ l₂ act).entered_typed (splitIdx j q))).symm))

/-- The original loop is the split table entered by a case on the
original state. -/
theorem entry_case_eqv {K : Nat} (l₁ l₂ : Fin (K + 1) → Bool) (act : Fin (K + 1) → Bool → Bool → Act K)
    (j : Fin (K + 1)) :
    Eqv false [State] ((entryRouter l₁ l₂ act).entered j) (entryCase l₁ l₂ act j) [Bit] := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N ((entryRouter l₁ l₂ act).entered_typed j)
    (entryCase_typed l₁ l₂ act j)).1
  have point : ∀ q, QLit (constEntry_typed q ((entryRouter l₁ l₂ act).entered_typed j)) =
      QLit (constEntry_typed q ((entrySource l₁ l₂ act).entered_typed (splitIdx j q))) := fun q =>
    (Paper.Extension.Singleton.ofRegion_eq_iff N _ _).2 (entry_pointed l₁ l₂ act j q)
  exact (congrArg (π).map (state_eta ((entryRouter l₁ l₂ act).entered_typed j))).trans
    (q_case_congr
      (caseValueBranches (constEntry_typed false ((entryRouter l₁ l₂ act).entered_typed j))
        (constEntry_typed true ((entryRouter l₁ l₂ act).entered_typed j))) deadBit_typed
      (caseValueBranches (constEntry_typed false ((entrySource l₁ l₂ act).entered_typed (splitIdx j false)))
        (constEntry_typed true ((entrySource l₁ l₂ act).entered_typed (splitIdx j true)))) deadBit_typed
      (q_case_congr _ _ _ _ (point false) (point true)) rfl)

/-- A case of two constant entries of literal request trees is those
trees at each constant, in default Paper. -/
theorem case_pointed {K : Nat} (t : Bool → LTable K) (x : Bool → Fin (K + 1)) :
    Pointed (caseEntry (constEntry false ((t false).entered (x false)))
      (constEntry true ((t true).entered (x true)))) t x := fun q => by
  have e := const_case q (constEntry_typed false ((t false).entered_typed (x false)))
    (constEntry_typed true ((t true).entered_typed (x true))) deadBit_typed
  cases q <;> exact .paper ((Paper.TypeCategory.ofRegion_eq_iff _ _).mp e)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
