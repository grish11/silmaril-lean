module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Comparison.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Destructure.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgCase.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Guarded.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Thms

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Comparison
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem includes {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : WithEntryLet.Eqv Γ r s L) : WithBoundEntryEta.Eqv Γ r s L := by
  induction h with
  | paper h => exact .paper h
  | extra _ _ step =>
    cases step with
    | seq R ha hd hb => exact WithBoundEntryEta.guarded_entryLet _ R ha hd hb
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case ha il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | lsubstCongr hp _ ih => exact .lsubstCongr hp ih
  | lsubstPost _ hr hs hσ ih => exact .lsubstPost ih hr hs hσ
  | substVars _ hθ ih => exact .substVars ih hθ
  | renameLabels _ hρ ih => exact .renameLabels ih hρ

theorem values {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    (h : SequencedEntry Γ r L) : ValueBranches Γ r L := by
  induction h with
  | br hi ha => exact .br hi ha
  | let₁ ha _ ih => exact .let₁ ha ih
  | case he _ _ il ir => exact .case he.hasType il ir

theorem reentry_branch {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {i : Nat} {a : Tm Φ} {A : τ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (hi : At (List.ofFn R ++ L) i A) (ha : Tm.BranchValue Γ a A)
    (hb : ∀ j, HasType (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    Paper.Eqv Γ (.cfg (.br i a) n blocks)
      ((Region.br i a).bindBranchArguments.lsubst (cfgEntryContinuations blocks)) L := by
  rw [lsubst_bindBranchArguments_br]
  apply Paper.Eqv.symm
  have beta := SubstitutionEquiv.letValue ha (cfgEntryContinuations_hasType R hb hi)
  change SubstitutionEquiv Γ (.let₁ a (cfgEntryContinuations blocks i))
    (.cfg (.br i a) n (fun j => ((blocks j).renameVars (lift Nat.succ)).substVars
      (Tm.liftSubst (Tm.singleSubst a)))) L at beta
  have cancel (j : Fin n) : ((blocks j).renameVars (lift Nat.succ)).substVars
      (Tm.liftSubst (Tm.singleSubst a)) = blocks j :=
    congrFun (mapLSubstVars_single_liftVars a (fun _ => blocks j)) 0
  rw [funext cancel] at beta
  exact .cfgEta (.native beta)

private theorem weaken {n : Nat} (R : Fin n → τ) {Γ : VCtx τ} {L : LCtx τ}
    {blocks : Fin n → Region Φ}
    (hb : ∀ j, ValueBranches (R j :: Γ) (blocks j) (List.ofFn R ++ L)) (A : τ) :
    ∀ j, ValueBranches (R j :: A :: Γ) ((blocks j).renameVars (lift Nat.succ))
      (List.ofFn R ++ L) :=
  fun j => (hb j).renameVars ((Ren.wk Γ A).lift (R j))

theorem reentry_sequenced {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (hr : SequencedEntry Γ r (List.ofFn R ++ L))
    (hb : ∀ j, ValueBranches (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    WithEntryLet.Eqv Γ (.cfg r n blocks) (r.bindBranchArguments.lsubst (cfgEntryContinuations blocks)) L := by
  generalize hK : List.ofFn R ++ L = K at hr hb
  induction hr generalizing blocks with
  | @br Γ K i a A hi ha =>
    subst K
    exact .paper (reentry_branch R hi ha (fun j => (hb j).hasType))
  | @let₁ Γ K a A r ha hbody ih =>
    subst K
    have pulled := WithEntryLet.entryLet n R ha (values hbody) hb
    change WithEntryLet.Eqv Γ (.cfg (.let₁ a r) n blocks)
      (.let₁ a (r.bindBranchArguments.lsubst (liftLSubstVars (cfgEntryContinuations blocks)))) L
    rw [lift_cfgEntryContinuations]
    exact pulled.trans (.let₁ ha (ih rfl (weaken R hb A)))
  | @case Γ K e A B l r he hl hr il ir =>
    subst K
    have pushed := SubstitutionEquiv.cfg_caseValue R he (values hl).hasType
      (values hr).hasType (fun j => (hb j).hasType)
    change WithEntryLet.Eqv Γ (.cfg (.case e l r) n blocks)
      (.case e (l.bindBranchArguments.lsubst (liftLSubstVars (cfgEntryContinuations blocks)))
        (r.bindBranchArguments.lsubst (liftLSubstVars (cfgEntryContinuations blocks)))) L
    rw [lift_cfgEntryContinuations]
    exact (Extension.Eqv.paper (.cfgEta (.native pushed))).trans
      (.case he.hasType (il rfl (weaken R hb A)) (ir rfl (weaken R hb B)))

theorem reentry_guarded_le_one {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {blocks : Fin n → Region Φ} (hn : n ≤ 1) (R : Fin n → τ)
    (hr : ValueBranches Γ r (List.ofFn R ++ L))
    (hb : ∀ j, ValueBranches (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    Paper.Eqv Γ (.cfg r n blocks) (r.bindBranchArguments.lsubst (cfgEntryContinuations blocks)) L := by
  have normalize : Paper.Eqv Γ r r.bindBranchArguments (List.ofFn R ++ L) :=
    .cfgEta (.native hr.bindBranchArguments_equiv)
  cases n with
  | zero =>
    have drop : Paper.Eqv Γ (.cfg r 0 blocks) r L :=
      .cfgEta (.native (.base (.entry (.cfgZero hr.hasType blocks))))
    have idFamily : Paper.Eqv Γ (r.bindBranchArguments.lsubst (cfgEntryContinuations blocks))
        (r.bindBranchArguments.lsubst labelId) L := by
      apply Paper.Eqv.lsubstCongr hr.hasType.bindBranchArguments
      intro i A hi
      exact .cfgEta (.native (.base (.entry (.cfgZero (.br hi (.var rfl)) _))))
    rw [lsubst_labelId] at idFamily
    exact drop.trans (normalize.trans idFamily.symm)
  | succ n =>
    have hz : n = 0 := by omega
    subst n
    have one := CfgEta.Eqv.eta (A := R 0) (L := L) hr (hb 0)
    change CfgEta.Eqv Γ (.cfg r 1 (fun _ => blocks 0))
      (r.lsubst (cfgEntryContinuations (fun _ : Fin 1 => blocks 0))) L at one
    have same : (fun _ : Fin 1 => blocks 0) = blocks :=
      funext fun j => congrArg blocks (Subsingleton.elim 0 j)
    rw [same] at one
    exact (Paper.Eqv.cfgEta one).trans
      (.lsubstPost normalize hr hr.hasType.bindBranchArguments
        (cfgEntryContinuations_hasType R (fun j => (hb j).hasType)))

theorem entryLet₂ {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {A B : τ}
    {r : Region Φ} {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (ha : Tm.HasType Γ a (Silmaril.product A B))
    (hr : HasType (B :: A :: Γ) r (List.ofFn R ++ L))
    (hb : ∀ j, HasType (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    WithBoundEntryEta.Eqv Γ (.cfg (.let₂ a r) n blocks)
      (.let₂ a (.cfg r n (fun j => ((blocks j).renameVars (lift Nat.succ)).renameVars (lift Nat.succ)))) L := by
  have before := WithBoundEntryEta.reentry R (.let₂ ha hr) hb
  change WithBoundEntryEta.Eqv Γ (.cfg (.let₂ a r) n blocks)
    (.let₂ a (r.bindBranchArguments.lsubst (liftLSubstVars (liftLSubstVars (cfgEntryContinuations blocks))))) L
    at before
  rw [lift_cfgEntryContinuations, lift_cfgEntryContinuations] at before
  have after := WithBoundEntryEta.reentry R hr (fun j =>
    ((hb j).renameVars ((Ren.wk Γ A).lift (R j))).renameVars ((Ren.wk (A :: Γ) B).lift (R j)))
  exact before.trans (.let₂ ha after.symm)

theorem reentry_let₂_iff_move {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {a : Tm Φ} {A B : τ}
    {r : Region Φ} {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (ha : Tm.HasType Γ a (Silmaril.product A B))
    (hr : SequencedEntry (B :: A :: Γ) r (List.ofFn R ++ L))
    (hb : ∀ j, ValueBranches (R j :: Γ) (blocks j) (List.ofFn R ++ L)) :
    WithEntryLet.Eqv Γ (.cfg (.let₂ a r) n blocks)
      ((Region.let₂ a r).bindBranchArguments.lsubst (cfgEntryContinuations blocks)) L ↔
    WithEntryLet.Eqv Γ (.cfg (.let₂ a r) n blocks)
      (.let₂ a (.cfg r n (fun j => ((blocks j).renameVars (lift Nat.succ)).renameVars (lift Nat.succ)))) L := by
  have body := reentry_sequenced R hr (weaken R (weaken R hb A) B)
  have underLet : WithEntryLet.Eqv Γ
      (.let₂ a (.cfg r n (fun j => ((blocks j).renameVars (lift Nat.succ)).renameVars (lift Nat.succ))))
      ((Region.let₂ a r).bindBranchArguments.lsubst (cfgEntryContinuations blocks)) L := by
    change WithEntryLet.Eqv Γ _
      (.let₂ a (r.bindBranchArguments.lsubst (liftLSubstVars (liftLSubstVars (cfgEntryContinuations blocks))))) L
    rw [lift_cfgEntryContinuations, lift_cfgEntryContinuations]
    exact .let₂ ha body
  exact ⟨fun h => h.trans underLet.symm, fun h => h.trans underLet⟩

namespace DestructureFixture

open Paper.EntryLetObstruction.Destructure
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Comparison.DestructureFixture (sumEntry)

theorem rows_typed {Γ : VCtx (Ty Empty)} (j : Fin 2) :
    ValueBranches (labels j :: Γ) (rows j) (List.ofFn labels ++ [U]) :=
  Fin.cases (.br (ℓ := 1) rfl (.pair (.var rfl) .unit))
    (fun _ => .br (ℓ := 2) rfl .unit) j

theorem initializer_typed {Γ : VCtx (Ty Empty)} : Tm.HasType Γ initializer P :=
  .pair (.op .unit) .unit

theorem entry_typed : ValueBranches [] entry (List.ofFn labels ++ [U]) :=
  .let₂ initializer_typed (.br (ℓ := 0) rfl (.var (i := 1) rfl))

theorem guards : ValueBranches [] original [U] ∧ ValueBranches [] reentered [U] := by
  refine ⟨.cfg labels entry_typed rows_typed, entry_typed.hasType.bindBranchArguments.lsubst ?_⟩
  intro i A hi
  exact .cfg labels (.br hi (.var rfl))
    (fun j => (rows_typed j).renameVars ((Ren.wk [] A).lift (labels j)))

theorem reentry_eq : WithBoundEntryEta.Eqv [] original reentered [U] :=
  WithBoundEntryEta.reentry labels entry_typed.hasType (fun j => (rows_typed j).hasType)

/-- The literal product binder cannot move across this two-row table in
the unary entry-let extension. Its body is a single constructor branch. -/
theorem move_ne :
    ¬ WithEntryLet.Eqv [] original
      (.let₂ initializer (.cfg (.br 0 (.var 1)) 2
        (fun j => ((rows j).renameVars (lift Nat.succ)).renameVars (lift Nat.succ)))) [U] := by
  exact fun h => reentry_ne ((reentry_let₂_iff_move labels initializer_typed
    (.br (i := 0) rfl (.var (i := 1) rfl)) rows_typed).mpr h)

private theorem sumEntry_typed : SequencedEntry [Silmaril.coprod U P] sumEntry (List.ofFn labels ++ [U]) :=
  .case (.var rfl) (.let₁ (.op (.var rfl)) (.br (i := 0) rfl (.var rfl)))
    (.br (i := 1) rfl (.var rfl))

/-- A sum selects between differently typed local labels and one arm issues
a request before entering the shared table. Unary entry-let suffices. -/
theorem selected_reentry_eq :
    WithEntryLet.Eqv [Silmaril.coprod U P] (.cfg sumEntry 2 rows)
      (sumEntry.bindBranchArguments.lsubst (cfgEntryContinuations rows)) [U] :=
  reentry_sequenced labels sumEntry_typed rows_typed

end DestructureFixture

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Comparison
