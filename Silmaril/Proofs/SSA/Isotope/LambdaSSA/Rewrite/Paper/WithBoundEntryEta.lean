module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Thms

public section

universe u v v₁ v₂ u₁ u₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.DeBruijn (lift liftN)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

theorem reentry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (he : HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    Eqv Γ (.cfg entry n blocks) (entry.bindBranchArguments.lsubst (cfgEntryContinuations blocks)) L :=
  .extra (.cfg R he hb) (he.bindBranchArguments.hasType.lsubst (cfgEntryContinuations_hasType R hb))
    (.reentry R he hb)

theorem entryLet {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {S : τ} {a : Tm Φ} {d : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (ha : Tm.HasType Γ a S)
    (hd : HasType (S :: Γ) d (List.ofFn R ++ L))
    (hb : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    Eqv Γ (.cfg (.let₁ a d) n blocks)
      (.let₁ a (.cfg d n (fun i => (blocks i).renameVars (lift Nat.succ)))) L := by
  have before := reentry R (.let₁ ha hd) hb
  change Eqv Γ (.cfg (.let₁ a d) n blocks)
    (.let₁ a (d.bindBranchArguments.lsubst (liftLSubstVars (cfgEntryContinuations blocks)))) L at before
  rw [lift_cfgEntryContinuations] at before
  exact before.trans (.let₁ ha (reentry R hd
    (fun i => (hb i).renameVars ((Ren.wk Γ S).lift (R i)))).symm)

private theorem zeroBlocks {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} (h : HasType Γ r L)
    (blocks : Fin 0 → Region Φ) : Eqv Γ (.cfg r 0 blocks) r L :=
  .paper (.cfgEta (.native (.base (.entry (.cfgZero h blocks)))))

/-- The zero-block instance already supplies the ordinary branch-binding equation. -/
theorem bindBranch {Γ : VCtx τ} {L : LCtx τ} {i : Nat} {a : Tm Φ} {A : τ}
    (hi : At L i A) (ha : Tm.HasType Γ a A) :
    Eqv Γ (.br i a) (.let₁ a (.br i (.var 0))) L := by
  let blocks : Fin 0 → Region Φ := Fin.elim0
  have step := reentry (L := L) (blocks := blocks) (Fin.elim0 : Fin 0 → τ) (.br hi ha) (fun i => i.elim0)
  rw [lsubst_bindBranchArguments_br] at step
  exact (zeroBlocks (.br hi ha) blocks).symm.trans
    (step.trans (.let₁ ha (zeroBlocks (.br hi (.var rfl)) _)))

/-- The only two shapes introduced by re-entry and lifting under local labels. -/
private inductive ReentryContinuation : Region Φ → Prop where
  | identity (j : Nat) : ReentryContinuation (labelId j)
  | reenter {n : Nat} (blocks : Fin n → Region Φ) (j : Nat) :
      ReentryContinuation (cfgEntryContinuations blocks j)

private theorem ReentryContinuation.liftVars {r : Region Φ} (h : ReentryContinuation r) :
    ReentryContinuation (r.renameVars (lift Nat.succ)) := by
  cases h with
  | identity j => exact .identity j
  | reenter blocks j =>
    change ReentryContinuation (liftLSubstVars (cfgEntryContinuations blocks) j)
    rw [lift_cfgEntryContinuations]
    exact .reenter _ j

private theorem ReentryContinuation.renameLabels {r : Region Φ} (h : ReentryContinuation r)
    (ρ : Nat → Nat) : ReentryContinuation (r.renameLabels ρ) := by
  cases h with
  | identity j => exact .identity (ρ j)
  | @reenter n blocks j =>
    simp only [cfgEntryContinuations, Region.renameLabels, ← Region.renameVars_renameLabels]
    exact .reenter (fun i => (blocks i).renameLabels (liftN n ρ)) (liftN n ρ j)

private theorem reentryShape_liftLabels {σ : Nat → Region Φ}
    (shapes : ∀ i, ReentryContinuation (σ i)) (n : Nat) :
    ∀ i, ReentryContinuation (liftLSubstN n σ i) := by
  induction n with
  | zero => exact shapes
  | succ n ih =>
    intro i
    cases i with
    | zero => exact .identity 0
    | succ i => exact (ih i).renameLabels Nat.succ

private theorem ReentryContinuation.subst_single {Γ : VCtx τ} {K : LCtx τ}
    {r : Region Φ} {A : τ} {a : Tm Φ} (shape : ReentryContinuation r)
    (hr : HasType (A :: Γ) r K) (ha : Tm.HasType Γ a A) :
    Eqv Γ (r.substVars (Tm.singleSubst a)) (.let₁ a r) K := by
  cases shape with
  | identity j =>
    change HasType (A :: Γ) (.br j (.var 0)) K at hr
    cases hr with
    | br hi ht =>
      cases ht with
      | var h =>
        cases Option.some.inj h
        exact bindBranch hi ha
  | @reenter n blocks j =>
    have cancel (i : Fin n) : ((blocks i).renameVars (lift Nat.succ)).substVars
        (Tm.liftSubst (Tm.singleSubst a)) = blocks i :=
      congrFun (mapLSubstVars_single_liftVars a (fun _ => blocks i)) 0
    have substituted : (cfgEntryContinuations blocks j).substVars (Tm.singleSubst a) =
        .cfg (.br j a) n blocks := by
      change Region.cfg (.br j a) n
        (fun i => ((blocks i).renameVars (lift Nat.succ)).substVars
          (Tm.liftSubst (Tm.singleSubst a))) = _
      rw [show (fun i => ((blocks i).renameVars (lift Nat.succ)).substVars
          (Tm.liftSubst (Tm.singleSubst a))) = blocks from
        funext cancel]
    rw [substituted]
    cases hr with
    | cfg R he hb =>
      cases he with
      | br hi ht =>
        cases ht with
        | var h =>
          cases Option.some.inj h
          have blocksTyped i : HasType (R i :: Γ) (blocks i) (List.ofFn R ++ K) := by
            have typed := (hb i).substVars ((Tm.Subst.HasType.single ha).lift (R i))
            exact (cancel i) ▸ typed
          have bound : Eqv Γ (.cfg (.br j a) n blocks)
              (.cfg (.let₁ a (.br j (.var 0))) n blocks) K :=
            .cfg R (bindBranch hi ha) (fun i => .refl (blocksTyped i))
          exact bound.trans (entryLet R ha (.br hi (.var rfl)) blocksTyped)

private theorem bind_reentry_lsubst {Γ : VCtx τ} {L K : LCtx τ} {r : Region Φ}
    {σ : Nat → Region Φ} (hr : HasType Γ r L)
    (hσ : LSubst.HasType Γ L K σ) (shapes : ∀ i, ReentryContinuation (σ i)) :
    Eqv Γ (r.lsubst σ) (r.bindBranchArguments.lsubst σ) K := by
  induction hr generalizing K σ with
  | br hi ha =>
    rw [lsubst_bindBranchArguments_br]
    exact (shapes _).subst_single (hσ hi) ha
  | let₁ ha hb ih => exact .let₁ ha (ih (hσ.liftVars _) (fun i => (shapes i).liftVars))
  | let₂ ha hb ih =>
    exact .let₂ ha (ih ((hσ.liftVars _).liftVars _) (fun i => (shapes i).liftVars.liftVars))
  | case ha hl hr il ir =>
    exact .case ha (il (hσ.liftVars _) (fun i => (shapes i).liftVars))
      (ir (hσ.liftVars _) (fun i => (shapes i).liftVars))
  | cfg R he hb ie ib =>
    have typed := hσ.append (List.ofFn R)
    have shape := reentryShape_liftLabels shapes (List.ofFn R).length
    simp only [List.length_ofFn] at typed shape
    exact .cfg R (ie typed shape) (fun i => ib i (typed.liftVars _) (fun j => (shape j).liftVars))

theorem literal_reentry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {entry : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (he : HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    Eqv Γ (.cfg entry n blocks) (entry.lsubst (cfgEntryContinuations blocks)) L :=
  (reentry R he hb).trans
    (bind_reentry_lsubst he (cfgEntryContinuations_hasType R hb) (fun i => .reenter blocks i)).symm

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

theorem seedDenotes
    (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
      Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h) :
    Region.Paper.Extension.Singleton.SeedDenotes (Seed := Step (τ := τ) (Φ := Φ)) J M := by
  intro Γ r s L step hr hs
  cases step with
  | reentry R he hb =>
    have left := denoteRegion_spec J M (.cfg R he hb)
    have eq := denoteRegion_cfgEta_bound_sharedTensor J M shared R he hb hs
    exact ⟨_, left, eq.symm ▸ denoteRegion_spec J M hs⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta
