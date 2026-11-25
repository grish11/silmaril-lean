module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Sequencing.Uniformity.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Coherence.Thms

public import Silmaril.SSA.Isotope.LetIter.Categorical.Sequencing.Associativity.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Sequencing.Codiagonal.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Sequencing.Naturality.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Empty.Soundness.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.LetEta.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Product.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open Silmaril.Isotope.LetIter.LocallyNameless
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory PremonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (duplicate)
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]




variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  (M : TypeModel τ V) [InstructionModel J M Φ]
  {ε : Type*} [HasEff Φ ε] {pe : ε}

private theorem compare_endpoints
    (coherent : TypingCoherent (ν := ν) J M Φ)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (l : Derivation Φ Γ β a A) (r : Derivation Φ Γ β b A)
    (h : denote J M l = denote J M r)
    (l' : Derivation Φ Γ β a A) (r' : Derivation Φ Γ β b A) :
    denote J M l' = denote J M r' :=
  (coherent l' l).trans (h.trans (coherent r r'))

/-- Assemble all congruence constructors and typed uniformity from soundness
of the core schemes at their endpoint judgments. -/
private theorem denote_equiv_of_core_sound
    (coherent : TypingCoherent (ν := ν) J M Φ)
    (diagonal : ∀ R : V, IsCentral (J.map (duplicate R) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) R R).inv))
    (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    (core : ∀ {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ},
      CoreAxiom pe a b → ∀ (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A),
      denote J M da = denote J M db)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (h : Equiv pe Γ β a b A) : ∀ (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A),
      denote J M da = denote J M db := by
  induction h with
  | refl => exact coherent
  | symm _ ih => intro l r; exact (ih r l).symm
  | trans h _ ih₁ ih₂ =>
    obtain ⟨mid⟩ := Derivation.ofHasType h.hasType.2
    intro l r
    exact (ih₁ l mid).trans (ih₂ mid r)
  | unit => exact coherent
  | op ha iha =>
    obtain ⟨la⟩ := Derivation.ofHasType ha.hasType.1
    obtain ⟨ra⟩ := Derivation.ofHasType ha.hasType.2
    apply compare_endpoints J M coherent (.op la) (.op ra)
    simp only [denote, iha la ra]
  | let₁ ha hb iha ihb =>
    obtain ⟨la⟩ := Derivation.ofHasType ha.hasType.1
    obtain ⟨ra⟩ := Derivation.ofHasType ha.hasType.2
    obtain ⟨lb⟩ := Derivation.ofHasType hb.hasType.1
    obtain ⟨rb⟩ := Derivation.ofHasType hb.hasType.2
    apply compare_endpoints J M coherent (.let₁ la lb) (.let₁ ra rb)
    simp only [denote, iha la ra, ihb lb rb]
  | pair ha hb iha ihb =>
    obtain ⟨la⟩ := Derivation.ofHasType ha.hasType.1
    obtain ⟨ra⟩ := Derivation.ofHasType ha.hasType.2
    obtain ⟨lb⟩ := Derivation.ofHasType hb.hasType.1
    obtain ⟨rb⟩ := Derivation.ofHasType hb.hasType.2
    apply compare_endpoints J M coherent (.pair la lb) (.pair ra rb)
    simp only [denote, iha la ra, ihb lb rb]
  | let₂ he hc ihe ihc =>
    obtain ⟨le⟩ := Derivation.ofHasType he.hasType.1
    obtain ⟨re⟩ := Derivation.ofHasType he.hasType.2
    obtain ⟨lc⟩ := Derivation.ofHasType hc.hasType.1
    obtain ⟨rc⟩ := Derivation.ofHasType hc.hasType.2
    apply compare_endpoints J M coherent (.let₂ le lc) (.let₂ re rc)
    simp only [denote, ihe le re, ihc lc rc]
  | inl ha iha =>
    obtain ⟨la⟩ := Derivation.ofHasType ha.hasType.1
    obtain ⟨ra⟩ := Derivation.ofHasType ha.hasType.2
    apply compare_endpoints J M coherent (.inl la) (.inl ra)
    simp only [denote, iha la ra]
  | inr hb ihb =>
    obtain ⟨lb⟩ := Derivation.ofHasType hb.hasType.1
    obtain ⟨rb⟩ := Derivation.ofHasType hb.hasType.2
    apply compare_endpoints J M coherent (.inr lb) (.inr rb)
    simp only [denote, ihb lb rb]
  | case he hl hr ihe ihl ihr =>
    obtain ⟨le⟩ := Derivation.ofHasType he.hasType.1
    obtain ⟨re⟩ := Derivation.ofHasType he.hasType.2
    obtain ⟨ll⟩ := Derivation.ofHasType hl.hasType.1
    obtain ⟨rl⟩ := Derivation.ofHasType hl.hasType.2
    obtain ⟨lr⟩ := Derivation.ofHasType hr.hasType.1
    obtain ⟨rr⟩ := Derivation.ofHasType hr.hasType.2
    apply compare_endpoints J M coherent (.case le ll lr) (.case re rl rr)
    simp only [denote, ihe le re, ihl ll rl, ihr lr rr]
  | abort ha iha =>
    obtain ⟨la⟩ := Derivation.ofHasType ha.hasType.1
    obtain ⟨ra⟩ := Derivation.ofHasType ha.hasType.2
    apply compare_endpoints J M coherent (.abort la) (.abort ra)
    simp only [denote, iha la ra]
  | iter ha hb iha ihb =>
    obtain ⟨la⟩ := Derivation.ofHasType ha.hasType.1
    obtain ⟨ra⟩ := Derivation.ofHasType ha.hasType.2
    obtain ⟨lb⟩ := Derivation.ofHasType hb.hasType.1
    obtain ⟨rb⟩ := Derivation.ofHasType hb.hasType.2
    apply compare_endpoints J M coherent (.iter la lb) (.iter ra rb)
    simp only [denote, iha la ra, ihb lb rb]

  | ax hax _ _ => exact core hax
  | uniformity ha hh hp hb hb' _ ih =>
    obtain ⟨da⟩ := Derivation.ofHasType ha
    obtain ⟨dh⟩ := Derivation.ofHasType hh
    obtain ⟨db⟩ := Derivation.ofHasType hb
    obtain ⟨db'⟩ := Derivation.ofHasType hb'
    apply compare_endpoints J M coherent (.iter da db) (.iter (.let₁ da dh) db')
    exact denote_iter_uniformity_of_pure J M (diagonal _) da dh db db' pureInstr hp (ih _ _)


/-- Typing a renamed term gives the original typing when the renaming preserves
the types of the original slots. -/
private theorem typing_of_rename {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {t : Tm ν Φ n} {A : τ} (ρ : TypedRenaming β δ) (d : HasType Φ Γ δ (t.rename ρ.toFun) A) :
    HasType Φ Γ β t A := by
  induction t generalizing m A with
  | fv x =>
    cases d with
    | fv h => exact .fv h
  | bv i =>
    cases d
    exact (ρ.typed i).symm ▸ HasType.bv (ι := i)
  | op f a ih =>
    cases d with
    | op h => exact .op (ih ρ h)
  | let₁ a b ih₁ ih₂ =>
    cases d with
    | let₁ ha hb => exact .let₁ (ih₁ ρ ha) (ih₂ (TypedRenaming.up ρ _) hb)
  | unit =>
    cases d
    exact .unit
  | pair a b ih₁ ih₂ =>
    cases d with
    | pair ha hb => exact .pair (ih₁ ρ ha) (ih₂ ρ hb)
  | let₂ a b ih₁ ih₂ =>
    cases d with
    | let₂ ha hb => exact .let₂ (ih₁ ρ ha) (ih₂ (TypedRenaming.up (TypedRenaming.up ρ _) _) hb)
  | inl a ih =>
    cases d with
    | inl h => exact .inl (ih ρ h)
  | inr a ih =>
    cases d with
    | inr h => exact .inr (ih ρ h)
  | case e l r ihe ihl ihr =>
    cases d with
    | case he hl hr =>
      exact .case (ihe ρ he) (ihl (TypedRenaming.up ρ _) hl) (ihr (TypedRenaming.up ρ _) hr)
  | abort a ih =>
    cases d with
    | abort h => exact .abort (ih ρ h)
  | iter a b ih₁ ih₂ =>
    cases d with
    | iter ha hb => exact .iter (ih₁ ρ ha) (ih₂ (TypedRenaming.up ρ _) hb)


variable [FreydCategory.CentralUnit J]

local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

omit [FreydCategory.CentralUnit J] in
private theorem diagonal_of_shared
    (shared : ∀ R S : V, ∃ e : J.obj R ⊗ J.obj S = J.obj (R ⊗ S), tensorIso R S = eqToIso e)
    (R : V) :
    IsCentral (J.map (duplicate R) ≫ (tensorIso R R).inv) := by
  obtain ⟨e, h⟩ := shared R R
  exact duplicate_central_of_tensor_eqToIso J R e h

theorem denote_core_of_coherent_shared_tensor_proof
    (coherent : TypingCoherent (ν := ν) J M Φ)
    (shared : ∀ R S : V, ∃ e : J.obj R ⊗ J.obj S = J.obj (R ⊗ S), tensorIso R S = eqToIso e)
    (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (hax : CoreAxiom pe a b) (l : Derivation Φ Γ β a A) (r : Derivation Φ Γ β b A) :
    denote J M l = denote J M r := by
  cases hax with
  | structural h =>
    cases h with
    | letBeta hp =>
      cases l with
      | let₁ da db =>
        exact (denote_let_beta J M pureInstr da db hp).trans (coherent _ r)
    | letEta a =>
      exact compare_endpoints J M coherent _ _ (denote_let_eta_of_centralUnit J M r) l r
    | unitEta a =>
      cases l with
      | let₁ da d =>
        cases d
        exact compare_endpoints J M coherent _ _ (denote_unit_eta_of_centralUnit J M r) _ r
    | pairBeta a b c =>
      cases r with
      | let₁ da d =>
        cases d with
        | let₁ weakened dc =>
          obtain ⟨db⟩ := Derivation.ofHasType (typing_of_rename (TypedRenaming.succ β _) weakened.toHasType)
          exact compare_endpoints J M coherent _ _ (denote_pair_beta_of_diagonals J M
            (diagonal_of_shared J shared _) (diagonal_of_shared J shared _) da db dc) l _
    | pairEta a =>
      cases l with
      | let₂ da dp =>
        cases dp with
        | pair d₁ d₂ =>
          cases d₁
          cases d₂
          exact (denote_pair_eta J M da).trans (coherent _ r)
    | caseBetaL e left right =>
      cases r with
      | let₁ de dl =>
        cases l with
        | case _ _ dr =>
          exact compare_endpoints J M coherent _ _ (denote_case_beta_left J M de dl dr) _ _
    | caseBetaR e left right =>
      cases r with
      | let₁ de dr =>
        cases l with
        | case _ dl _ =>
          exact compare_endpoints J M coherent _ _ (denote_case_beta_right J M de dl dr) _ _
    | caseEta e =>
      cases l with
      | case de dl dr =>
        cases dl with
        | inl d =>
          exact compare_endpoints J M coherent _ _ (denote_case_eta J M r) _ r
    | emptyInitial a b c =>
      cases l with
      | let₁ dl db =>
        cases r with
        | let₁ dr dc =>
          cases dl with
          | abort de =>
            cases dr with
            | abort de' =>
              exact compare_endpoints J M coherent _ _ (denote_emptyInitial J M de db dc) _ _
  | sequencing h =>
    cases h with
    | bindOp a c =>
      cases l with
      | let₁ op dc =>
        cases op with
        | op da => exact (denote_bind_op J M da dc).trans (coherent _ r)
    | bindLet a b c =>
      cases l with
      | let₁ inner dc =>
        cases inner with
        | let₁ da db =>
          exact (denote_bind_let_of_diagonal J M (diagonal_of_shared J shared _) da db dc).trans
            (coherent _ r)
    | bindLetPair e c d =>
      cases l with
      | let₁ inner dd =>
        cases inner with
        | let₂ de dc =>
          exact (denote_bind_let_pair_of_diagonal J M
            (diagonal_of_shared J shared _) de dc dd).trans (coherent _ r)
    | bindLetCase e l' r' d =>
      cases l with
      | let₁ inner dd =>
        cases inner with
        | case de dl dr =>
          exact (denote_bind_let_case_of_diagonal J M
            (diagonal_of_shared J shared _) de dl dr dd).trans (coherent _ r)
    | bindPair a c =>
      cases l with
      | let₂ da dc => exact (denote_bind_pair J M da dc).trans (coherent _ r)
    | bindCase e l' r' =>
      cases l with
      | case de dl dr => exact (denote_bind_case J M de dl dr).trans (coherent _ r)
  | iteration h =>
    cases h with
    | fixpoint a b =>
      cases l with
      | iter da db => exact (denote_iter_fixpoint J M da db).trans (coherent _ r)
    | naturality a b c =>
      cases l with
      | let₁ inner dc =>
        cases inner with
        | iter da db =>
          exact (denote_iter_naturality_of_shared_tensor J M (diagonal_of_shared J shared _)
            (shared _ _) da db dc).trans (coherent _ r)
    | codiagonal a b =>
      cases l with
      | iter da inner =>
        cases inner with
        | iter newest weakened =>
          cases newest
          obtain ⟨db⟩ := Derivation.ofHasType
            (typing_of_rename (TypedRenaming.underBinder β _ _) weakened.toHasType)
          exact compare_endpoints J M coherent _ _ (denote_iter_codiagonal_of_shared_tensor J M
            (diagonal_of_shared J shared _) (shared _ _) da db) _ r
    | iterBind a b =>
      cases l with
      | iter da db => exact (denote_iter_bind J M da db).trans (coherent _ r)

theorem denote_equiv_of_coherent_shared_tensor_proof
    (coherent : TypingCoherent (ν := ν) J M Φ)
    (shared : ∀ R S : V, ∃ e : J.obj R ⊗ J.obj S = J.obj (R ⊗ S), tensorIso R S = eqToIso e)
    (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    (h : Equiv pe Γ β a b A) (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b A) :
    denote J M da = denote J M db :=
  denote_equiv_of_core_sound J M coherent (diagonal_of_shared J shared) pureInstr
    (fun law l r => denote_core_of_coherent_shared_tensor_proof J M coherent shared pureInstr law l r)
    h da db

end Silmaril.Isotope.LetIter.Semantics.Categorical
