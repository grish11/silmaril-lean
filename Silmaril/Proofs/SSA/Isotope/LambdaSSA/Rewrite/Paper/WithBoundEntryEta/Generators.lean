module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Generators.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Comparison.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgCase.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Thms

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Generators

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.Generators
open Silmaril.DeBruijn (lift)

local notation "GenEqv" => WithBoundEntryEta.Generators.Eqv

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

private theorem weaken {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {bs : Fin n → Region Φ}
    (R : Fin n → τ) (hb : ∀ j, HasType (R j :: Γ) (bs j) (List.ofFn R ++ L)) (A : τ) :
    ∀ j, HasType (R j :: A :: Γ) (weakenRows bs j) (List.ofFn R ++ L) :=
  fun j => (hb j).renameVars ((Ren.wk Γ A).lift (R j))

theorem caseEntry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {l r : Region Φ}
    {bs : Fin n → Region Φ} (R : Fin n → τ)
    (ha : Tm.HasType Γ a (Silmaril.coprod A B))
    (hl : HasType (A :: Γ) l (List.ofFn R ++ L))
    (hr : HasType (B :: Γ) r (List.ofFn R ++ L))
    (hb : ∀ j, HasType (R j :: Γ) (bs j) (List.ofFn R ++ L)) :
    WithBoundEntryEta.Eqv Γ (.cfg (.case a l r) n bs)
      (.case a (.cfg l n (weakenRows bs)) (.cfg r n (weakenRows bs))) L := by
  have before := WithBoundEntryEta.literal_reentry R (.case ha hl hr) hb
  change WithBoundEntryEta.Eqv Γ (.cfg (.case a l r) n bs)
    (.case a (l.lsubst (liftLSubstVars (cfgEntryContinuations bs)))
      (r.lsubst (liftLSubstVars (cfgEntryContinuations bs)))) L at before
  rw [lift_cfgEntryContinuations] at before
  exact before.trans (.case ha
    (WithBoundEntryEta.literal_reentry R hl (weaken R hb A)).symm
    (WithBoundEntryEta.literal_reentry R hr (weaken R hb B)).symm)

theorem nested {m n : Nat} {Γ : VCtx τ} {L : LCtx τ} {e : Region Φ}
    {inner : Fin m → Region Φ} {outer : Fin n → Region Φ} (S : Fin m → τ) (R : Fin n → τ)
    (he : HasType Γ e (List.ofFn S ++ (List.ofFn R ++ L)))
    (hi : ∀ j, HasType (S j :: Γ) (inner j) (List.ofFn S ++ (List.ofFn R ++ L)))
    (ho : ∀ j, HasType (R j :: Γ) (outer j) (List.ofFn R ++ L)) :
    WithBoundEntryEta.Eqv Γ (.cfg (.cfg e m inner) n outer)
      (.cfg (e.lsubst (liftLSubstN m (cfgEntryContinuations outer))) m
        (fun j => (inner j).lsubst (liftLSubstVars (liftLSubstN m (cfgEntryContinuations outer))))) L :=
  WithBoundEntryEta.literal_reentry R (.cfg S he hi) ho

private theorem step_into_bound {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Step Γ r s L) : WithBoundEntryEta.Eqv Γ r s L := by
  cases h with
  | entryLet h =>
    cases h with
    | unary R ha hr hb => exact WithBoundEntryEta.entryLet R ha hr hb
    | binary R ha hr hb => exact WithBoundEntryEta.Comparison.entryLet₂ R ha hr hb
  | branch hi ha => exact WithBoundEntryEta.bindBranch hi ha
  | caseEntry R ha hl hr hb => exact caseEntry R ha hl hr hb
  | nested S R he hi ho => exact nested S R he hi ho

private theorem map_eqv {Seed Target : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (gen : ∀ {Γ L r s}, Seed Γ r s L → Extension.Eqv Target Γ r s L)
    {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (h : Extension.Eqv Seed Γ r s L) : Extension.Eqv Target Γ r s L := by
  induction h with
  | paper h => exact .paper h
  | extra _ _ h => exact gen h
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

private theorem normalize {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} (hr : HasType Γ r L) :
    GenEqv Γ r r.bindBranchArguments L := by
  induction hr with
  | br hi ha => exact .extra (.br hi ha) (.let₁ ha (.br hi (.var rfl))) (.branch hi ha)
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case ha il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib

private theorem literal_guarded {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {bs : Fin n → Region Φ} (R : Fin n → τ)
    (hr : ValueBranches Γ r (List.ofFn R ++ L))
    (hb : ∀ j, HasType (R j :: Γ) (bs j) (List.ofFn R ++ L)) :
    GenEqv Γ (.cfg r n bs) (r.lsubst (cfgEntryContinuations bs)) L := by
  generalize hK : List.ofFn R ++ L = K at hr hb
  induction hr generalizing bs with
  | @br K i A Γ a hi ha =>
    subst K
    change GenEqv Γ (.cfg (.br i a) n bs)
      (.cfg (.br i a) n (fun j => ((bs j).renameVars (lift Nat.succ)).substVars
        (Tm.liftSubst (Tm.singleSubst a)))) L
    have cancel (j : Fin n) : ((bs j).renameVars (lift Nat.succ)).substVars
        (Tm.liftSubst (Tm.singleSubst a)) = bs j :=
      congrFun (mapLSubstVars_single_liftVars a (fun _ => bs j)) 0
    rw [funext cancel]
    exact .refl (.cfg R (.br hi ha.hasType) hb)
  | @let₁ Γ a A r K ha hr ih =>
    subst K
    have pull : GenEqv Γ (.cfg (.let₁ a r) n bs) (.let₁ a (.cfg r n (weakenRows bs))) L :=
      .extra (.cfg R (.let₁ ha hr.hasType) hb) (.let₁ ha (.cfg R hr.hasType (weaken R hb A)))
        (.entryLet (.unary R ha hr.hasType hb))
    change GenEqv Γ (.cfg (.let₁ a r) n bs) (.let₁ a (r.lsubst (liftLSubstVars (cfgEntryContinuations bs)))) L
    rw [lift_cfgEntryContinuations]
    exact pull.trans (.let₁ ha (ih rfl (weaken R hb A)))
  | @let₂ Γ a A B r K ha hr ih =>
    subst K
    have wb := weaken R (weaken R hb A) B
    have pull : GenEqv Γ (.cfg (.let₂ a r) n bs) (.let₂ a (.cfg r n (weakenRows (weakenRows bs)))) L :=
      .extra (.cfg R (.let₂ ha hr.hasType) hb) (.let₂ ha (.cfg R hr.hasType wb))
        (.entryLet (.binary R ha hr.hasType hb))
    change GenEqv Γ (.cfg (.let₂ a r) n bs)
      (.let₂ a (r.lsubst (liftLSubstVars (liftLSubstVars (cfgEntryContinuations bs))))) L
    rw [lift_cfgEntryContinuations, lift_cfgEntryContinuations]
    exact pull.trans (.let₂ ha (ih rfl wb))
  | @case Γ a A B l K r ha hl hr il ir =>
    subst K
    have pull : GenEqv Γ (.cfg (.case a l r) n bs)
        (.case a (.cfg l n (weakenRows bs)) (.cfg r n (weakenRows bs))) L :=
      .extra (.cfg R (.case ha hl.hasType hr.hasType) hb)
        (.case ha (.cfg R hl.hasType (weaken R hb A)) (.cfg R hr.hasType (weaken R hb B)))
        (.caseEntry R ha hl.hasType hr.hasType hb)
    change GenEqv Γ (.cfg (.case a l r) n bs)
      (.case a (l.lsubst (liftLSubstVars (cfgEntryContinuations bs)))
        (r.lsubst (liftLSubstVars (cfgEntryContinuations bs)))) L
    rw [lift_cfgEntryContinuations]
    exact pull.trans (.case ha (il rfl (weaken R hb A)) (ir rfl (weaken R hb B)))
  | @cfg m Γ e K inner S he hi ie ii =>
    subst K
    have typed : HasType Γ (.cfg e m inner) (List.ofFn R ++ L) :=
      .cfg S he.hasType (fun i => (hi i).hasType)
    exact .extra (.cfg R typed hb) (typed.lsubst (cfgEntryContinuations_hasType R hb))
      (.nested S R he.hasType (fun i => (hi i).hasType) hb)

theorem reentry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ}
    {bs : Fin n → Region Φ} (R : Fin n → τ)
    (hr : HasType Γ r (List.ofFn R ++ L))
    (hb : ∀ j, HasType (R j :: Γ) (bs j) (List.ofFn R ++ L)) :
    GenEqv Γ (.cfg r n bs) (r.bindBranchArguments.lsubst (cfgEntryContinuations bs)) L :=
  (Extension.Eqv.cfg R (normalize hr) (fun j => .refl (hb j))).trans
    (literal_guarded R hr.bindBranchArguments hb)

theorem iff_bound {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ} :
    GenEqv Γ r s L ↔ WithBoundEntryEta.Eqv Γ r s L :=
  ⟨map_eqv step_into_bound, map_eqv (fun h => by
    cases h with
    | reentry R he hb => exact reentry R he hb)⟩

theorem candidate_caseEntry {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {A B : τ} {a : Tm Φ} {l r : Region Φ}
    {bs : Fin n → Region Φ} (R : Fin n → τ)
    (ha : Tm.HasType Γ a (Silmaril.coprod A B))
    (hl : ValueBranches (A :: Γ) l (List.ofFn R ++ L))
    (hr : ValueBranches (B :: Γ) r (List.ofFn R ++ L))
    (hb : ∀ j, ValueBranches (R j :: Γ) (bs j) (List.ofFn R ++ L)) :
    Extension.Eqv Candidate Γ (.cfg (.case a l r) n bs)
      (.case a (.cfg l n (weakenRows bs)) (.cfg r n (weakenRows bs))) L := by
  let C := Silmaril.coprod A B
  let K := List.ofFn R ++ L
  have hs : ValueBranches (C :: Γ) (RetainedCase.boundCase l r) K :=
    RetainedCase.boundCase_typed hl hr
  have ws := weaken R (fun j => (hb j).hasType) C
  have first := Extension.Eqv.cfg R
    (WithCaseBind.case_eq_let (Seed := Candidate) Or.inr ha hl hr)
    (fun j => .refl (hb j).hasType)
  have seq : Extension.Eqv Candidate Γ
      (.cfg (.let₁ a (RetainedCase.boundCase l r)) n bs)
      (.let₁ a (.cfg (RetainedCase.boundCase l r) n (weakenRows bs))) L :=
    .extra (.cfg R (.let₁ ha hs.hasType) (fun j => (hb j).hasType))
      (.let₁ ha (.cfg R hs.hasType ws))
      (.inl (.unary R ha hs.hasType (fun j => (hb j).hasType)))
  have left := hl.renameVars ((Ren.wk Γ C).lift A)
  have right := hr.renameVars ((Ren.wk Γ C).lift B)
  have pureCase := SubstitutionEquiv.cfg_caseValue R
    (.var (i := 0) (rfl : At (C :: Γ) 0 C)) left.hasType right.hasType ws
  have align : lift (lift Nat.succ) ∘ lift Nat.succ = lift Nat.succ ∘ lift Nat.succ := by
    funext i
    cases i <;> rfl
  have after : SubstitutionEquiv (C :: Γ) (.cfg (RetainedCase.boundCase l r) n (weakenRows bs))
      (RetainedCase.boundCase (.cfg l n (weakenRows bs)) (.cfg r n (weakenRows bs))) L := by
    simpa only [RetainedCase.boundCase, weakenRows, Region.renameVars, renameVars_comp, align] using pureCase
  have rows (T : τ) (j : Fin n) :
      ValueBranches (R j :: T :: Γ) (weakenRows bs j) K :=
    (hb j).renameVars ((Ren.wk Γ T).lift (R j))
  exact first.trans (seq.trans ((Extension.Eqv.let₁ (Seed := Candidate) ha (.paper (.cfgEta (.native after)))).trans
    (WithCaseBind.case_eq_let (Seed := Candidate) Or.inr ha
      (.cfg R hl (rows A)) (.cfg R hr (rows B))).symm))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Generators
