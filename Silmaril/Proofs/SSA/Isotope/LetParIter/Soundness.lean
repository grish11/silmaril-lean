module

public import Silmaril.SSA.Isotope.LetParIter.Equations.Defs
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Substitution

public section

namespace Silmaril.Isotope.LetParIter.Proofs

open Parallel LetIter.ProofRelevant.Semantics

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν] {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Elgot.Iterate m]
  [InstructionModel Φ τ ε m]
variable (P : Elgot.ParallelPairing m)
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A B C D : τ}
variable {a b c p e : Tm ν Φ n} {f g l r : Tm ν Φ (n + 1)}
variable (γ : CtxDen Γ) (ρ : BoundDen β)

-- The dependent snoc environment reduces to pairs under constructors.
set_option backward.isDefEq.respectTransparency false

@[local simp] private theorem get_zero {X : τ} (x : TyDen X) :
    BoundDen.get (β := .snoc β X) (ρ, x) 0 = x := rfl

@[local simp] private theorem get_one {X Y : τ} (x : TyDen X) (y : TyDen Y) :
    BoundDen.get (β := .snoc (.snoc β X) Y) ((ρ, x), y) 1 = x := rfl

@[local simp] private theorem get_two {X Y Z : τ} (x : TyDen X) (y : TyDen Y) (z : TyDen Z) :
    BoundDen.get (β := .snoc (.snoc (.snoc β X) Y) Z) (((ρ, x), y), z) 2 = x := rfl

private theorem swap_sound (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B) :
    denote (ε := ε) P (Typing.swap (.par da db)) γ ρ = denote (ε := ε) P (.par db da) γ ρ := by
  have h := congrArg (Functor.map (TypeModel.productEquiv B A).symm)
    (P.swap (denote (ε := ε) P da γ ρ) (denote (ε := ε) P db γ ρ))
  simp [Typing.swap, denote, evalPar, bind_pure_comp]
  change ((fun p : TyDen A × TyDen B => (TypeModel.productEquiv B A).symm (p.2, p.1)) <$>
      P.pair (denote (ε := ε) P da γ ρ) (denote (ε := ε) P db γ ρ)) = _
  simpa [← comp_map, Function.comp_def, Prod.swap] using h

private theorem assoc_sound (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B)
    (dc : Derivation Φ Γ β c C) :
    denote (ε := ε) P (Typing.assoc (.par (.par da db) dc)) γ ρ =
      denote (ε := ε) P (.par da (.par db dc)) γ ρ := by
  let x := denote (ε := ε) P da γ ρ
  let y := denote (ε := ε) P db γ ρ
  let z := denote (ε := ε) P dc γ ρ
  have hl := (P.natural (TypeModel.productEquiv A B).symm id (P.pair x y) z).symm
  have hr := (P.natural id (TypeModel.productEquiv B C).symm x (P.pair y z)).symm
  simp only [id_map] at hl hr
  dsimp only [x, y, z] at hl hr
  simp [Typing.assoc, denote, evalPar, bind_pure_comp]
  rw [hl, hr]
  have h := congrArg (Functor.map fun p : TyDen A × (TyDen B × TyDen C) =>
    (TypeModel.productEquiv A (product B C)).symm
      (p.1, (TypeModel.productEquiv B C).symm p.2)) (P.assoc x y z)
  simp only [← comp_map, Function.comp_def, Prod.map, Equiv.apply_symm_apply]
  change ((fun a : (TyDen A × TyDen B) × TyDen C =>
        (TypeModel.productEquiv A (product B C)).symm
          (a.1.1, (TypeModel.productEquiv B C).symm (a.1.2, a.2))) <$> P.pair (P.pair x y) z) =
    ((fun p : TyDen A × (TyDen B × TyDen C) =>
        (TypeModel.productEquiv A (product B C)).symm
          (p.1, (TypeModel.productEquiv B C).symm p.2)) <$> P.pair x (P.pair y z))
  simpa [← comp_map, Function.comp_def] using h

private theorem purePair_sound (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B)
    (ha : Pure (⊥ : ε) a) (hb : Pure (⊥ : ε) b) :
    denote (ε := ε) P (.par da db) γ ρ = denote (ε := ε) P (.pair da db) γ ρ := by
  obtain ⟨x, hx⟩ := denote_pure P da ha γ ρ
  obtain ⟨y, hy⟩ := denote_pure P db hb γ ρ
  simp only [denote, evalPar, hx, hy, P.pure_pair, map_pure, pure_bind]

private theorem unitLeft_sound (da : Derivation Φ Γ β a A) :
    denote (ε := ε) P (Typing.dropLeft (.par .unit da)) γ ρ = denote (ε := ε) P da γ ρ := by
  simp [Typing.dropLeft, denote, evalPar, bind_pure_comp, P.pair_pure_left]
  exact id_map (denote (ε := ε) P da γ ρ)

private theorem unitRight_sound (da : Derivation Φ Γ β a A) :
    denote (ε := ε) P (Typing.dropRight (.par da .unit)) γ ρ = denote (ε := ε) P da γ ρ := by
  simp [Typing.dropRight, denote, evalPar, bind_pure_comp, P.pair_pure_right]

private theorem map_sound (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B)
    (df : Derivation Φ Γ (.snoc β A) f C) (dg : Derivation Φ Γ (.snoc β B) g D)
    (hf : Pure (⊥ : ε) f) (hg : Pure (⊥ : ε) g) :
    denote (ε := ε) P (.par (.let₁ da df) (.let₁ db dg)) γ ρ =
      denote (ε := ε) P
        (.let₂ (.par da db) (.pair (Typing.leftResult df) (Typing.underBinder dg))) γ ρ := by
  choose fv hfv using fun x : TyDen A => denote_pure P df hf γ (ρ, x)
  choose gv hgv using fun y : TyDen B => denote_pure P dg hg γ (ρ, y)
  simp [denote, Typing.leftResult, Typing.underBinder, denote_rename, hfv, hgv,
    bind_pure_comp, evalPar, ← P.natural, Prod.map]

private theorem parCaseLeft_sound (de : Derivation Φ Γ β e (coprod A B)) (he : Pure (⊥ : ε) e)
    (dl : Derivation Φ Γ (.snoc β A) l C) (dr : Derivation Φ Γ (.snoc β B) r C)
    (dp : Derivation Φ Γ β p D) :
    denote (ε := ε) P (.par (.case (h := hasCase) de dl dr) dp) γ ρ =
      denote (ε := ε) P
        (.case (h := hasCase) de (.par dl (Typing.lift dp)) (.par dr (Typing.lift dp))) γ ρ := by
  obtain ⟨v, hv⟩ := denote_pure P de he γ ρ
  simp only [denote, hv, pure_bind, Typing.lift, denote_rename, pull_succ]
  cases TypeModel.coprodEquiv A B v <;> rfl

private theorem parCaseRight_sound (de : Derivation Φ Γ β e (coprod A B)) (he : Pure (⊥ : ε) e)
    (dl : Derivation Φ Γ (.snoc β A) l C) (dr : Derivation Φ Γ (.snoc β B) r C)
    (dp : Derivation Φ Γ β p D) :
    denote (ε := ε) P (.par dp (.case (h := hasCase) de dl dr)) γ ρ =
      denote (ε := ε) P
        (.case (h := hasCase) de (.par (Typing.lift dp) dl) (.par (Typing.lift dp) dr)) γ ρ := by
  obtain ⟨v, hv⟩ := denote_pure P de he γ ρ
  simp only [denote, hv, pure_bind, Typing.lift, denote_rename, pull_succ]
  cases TypeModel.coprodEquiv A B v <;> rfl

private theorem letBeta_sound (da : Derivation Φ Γ β a A)
    (db : Derivation Φ Γ (.snoc β A) f B) (ha : Pure (⊥ : ε) a) :
    denote (ε := ε) P (.let₁ da db) γ ρ =
      denote (ε := ε) P (Typing.instantiate db da) γ ρ := by
  obtain ⟨x, hx⟩ := denote_pure P da ha γ ρ
  rw [denote, hx, pure_bind]
  exact (denote_instantiate P γ db da ρ x hx).symm

variable [Elgot.LawfulElgotMonad m]

private theorem iterUniformity_sound {A' : τ} {h b b' : Tm ν Φ (n + 1)}
    (da : Derivation Φ Γ β a A)
    (dh : Derivation Φ Γ (.snoc β A) h A') (hp : Pure (⊥ : ε) h)
    (db : Derivation Φ Γ (.snoc β A) b (coprod B A))
    (db' : Derivation Φ Γ (.snoc β A') b' (coprod B A'))
    (hsquare : ∀ x : TyDen A,
      denote (ε := ε) P (Typing.uniformityLeft db dh) γ (ρ, x) =
        denote (ε := ε) P (Typing.uniformityRight db' dh) γ (ρ, x)) :
    denote (ε := ε) P (.iter (h := rfl) da db) γ ρ =
      denote (ε := ε) P (.iter (h := rfl) (.let₁ da dh) db') γ ρ := by
  choose k hk using fun x : TyDen A => denote_pure P dh hp γ (ρ, x)
  let f : TyDen A → m (TyDen B ⊕ TyDen A) :=
    fun x => denote (ε := ε) P db γ (ρ, x) >>= Elgot.liftPure (TypeModel.coprodEquiv B A)
  let g : TyDen A' → m (TyDen B ⊕ TyDen A') :=
    fun x => denote (ε := ε) P db' γ (ρ, x) >>= Elgot.liftPure (TypeModel.coprodEquiv B A')
  have comm : (f >=> Elgot.liftPure (Sum.map id k)) = (Elgot.liftPure k >=> g) := by
    funext x
    have hs := hsquare x
    rw [Typing.uniformityRight, denote_instantiate P γ _ dh (ρ, x) (k x) (hk x)] at hs
    rw [Typing.underBinder, denote_rename, pull_underBinder] at hs
    calc
      (f >=> Elgot.liftPure (Sum.map id k)) x =
          denote (ε := ε) P (Typing.uniformityLeft db dh) γ (ρ, x) >>=
            Elgot.liftPure (TypeModel.coprodEquiv B A') := by
        simp only [f, Bind.kleisliRight, Elgot.liftPure, Function.comp_apply, bind_assoc,
          pure_bind, Typing.uniformityLeft, Typing.newest, denote, Typing.underBinder,
          denote_rename, pull_underBinder, hk]
        apply bind_congr
        intro s
        cases TypeModel.coprodEquiv B A s with
        | inl =>
            simp
            rfl
        | inr => simp
      _ = g (k x) := congrArg (fun z => z >>= Elgot.liftPure (TypeModel.coprodEquiv B A')) hs
      _ = (Elgot.liftPure k >=> g) x := by
        simp only [Bind.kleisliRight, Elgot.liftPure, Function.comp_apply, pure_bind]
  simp only [denote, evalIter, bind_assoc]
  apply bind_congr
  intro x
  change Elgot.iter f x = _
  rw [congrFun (Elgot.LawfulElgotMonad.uniformity f g k comm) x]
  simp only [Bind.kleisliRight, Elgot.liftPure, Function.comp_apply, pure_bind, hk]
  rfl

theorem sound {da : Derivation Φ Γ β a A} {db : Derivation Φ Γ β b A}
    (h : Equiv (⊥ : ε) Γ da db) :
    denote (ε := ε) P da γ ρ = denote (ε := ε) P db γ ρ := by
  induction h with
  | refl => rfl
  | symm _ ih => exact (ih ρ).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ ρ).trans (ih₂ ρ)
  | native _ _ h => simpa only [denote_embed] using
      LetIter.ProofRelevant.Semantics.related_sound h γ ρ
  | rename r _ ih => simpa only [denote_rename] using ih (pull r ρ)
  | bsubst s hs _ ih =>
      choose v hv using fun i => denote_pure P (s i) (hs i) γ ρ
      let ξ := envOf _ v
      have hξ : SubstDen (ε := ε) P γ s ρ ξ := fun i => by
        simpa only [ξ, get_envOf] using hv i
      simpa only [denote_bsubst P γ _ s ρ ξ hξ] using ih ξ
  | op _ ih | inl _ ih | inr _ ih | abort _ ih => simp only [denote, ih]
  | let₁ _ _ ih₁ ih₂ | pair _ _ ih₁ ih₂ | let₂ _ _ ih₁ ih₂ | par _ _ ih₁ ih₂ =>
      simp only [denote, ih₁, ih₂]
  | case _ _ _ ihe ihl ihr => simp only [denote, ihe, ihl, ihr]
  | iter _ _ ih₁ ih₂ => simpa only [denote] using evalIter_congr (ih₁ ρ) fun x => ih₂ (ρ, x)
  | swap da db => exact swap_sound P γ ρ da db
  | assoc da db dc => exact assoc_sound P γ ρ da db dc
  | purePair ha hb da db => exact purePair_sound P γ ρ da db ha hb
  | unitLeft da => exact unitLeft_sound P γ ρ da
  | unitRight da => exact unitRight_sound P γ ρ da
  | map da db df dg hf hg => exact map_sound P γ ρ da db df dg hf hg
  | parCaseLeft de he dl dr dp => exact parCaseLeft_sound P γ ρ de he dl dr dp
  | parCaseRight de he dl dr dp => exact parCaseRight_sound P γ ρ de he dl dr dp
  | letBeta da db ha => exact letBeta_sound P γ ρ da db ha
  | letEta da => simp only [Typing.newest, denote, get_zero, bind_pure]
  | iterFixpoint da db =>
      simp only [Typing.newest, denote, Typing.underBinder, denote_rename, pull_underBinder]
      rw [evalIter_unfold]
      apply bind_congr
      intro a
      apply bind_congr
      intro s
      cases TypeModel.coprodEquiv _ _ s <;> rfl
  | iterUniformity da dh hp db db' _ ih =>
      exact iterUniformity_sound P γ ρ da dh hp db db' (fun x => ih (ρ, x))
  | iterBind da db =>
      simp only [Typing.newest, denote, evalIter, Typing.underBinder, denote_rename, pull_underBinder,
        get_zero, pure_bind]

end Silmaril.Isotope.LetParIter.Proofs
