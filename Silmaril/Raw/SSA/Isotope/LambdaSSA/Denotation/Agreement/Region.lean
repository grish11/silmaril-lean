module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Denotation.Monadic.Region
public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Denotation.Agreement.Term

@[expose] public section

set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

/-! # Agreement of direct and categorical lambda-SSA region semantics -/

namespace Silmaril.Isotope.LambdaSSA.Semantics

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (typeJ bind_of pair_of caseWithContext_of comp_map_of contextualLoop_of)

universe u v q r

namespace Agreement

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Iterate m] [LawfulElgotMonad m] [InstructionModel Φ τ ε m]

def envFromCategorical : {Γ : VCtx τ} →
    Categorical.ctxObj (Categorical.ofMonadicTypeModel (τ := τ)) Γ → Monadic.Env Γ
  | [], ρ => ρ
  | _ :: _, ρ => (envFromCategorical ρ.1, ρ.2)

@[simp] private theorem envFrom_to {Γ : VCtx τ} (ρ : Monadic.Env Γ) :
    envFromCategorical (envToCategorical ρ) = ρ := by
  induction Γ with
  | nil => rfl
  | cons _ _ ih => simp [envFromCategorical, envToCategorical, ih]

@[simp] private theorem envTo_from {Γ : VCtx τ}
    (ρ : Categorical.ctxObj (Categorical.ofMonadicTypeModel (τ := τ)) Γ) :
    envToCategorical (envFromCategorical ρ) = ρ := by
  induction Γ with
  | nil => rfl
  | cons _ _ ih => simp [envFromCategorical, envToCategorical, ih]

private theorem envPair_agrees {Γ : VCtx τ} {A B : τ} (ρ : Monadic.Env Γ)
    (ab : TyDen (Silmaril.product A B)) :
    (Categorical.ctxPairIso (Categorical.ofMonadicTypeModel (τ := τ)) Γ A B).hom
      (envToCategorical ρ, ((Categorical.ofMonadicTypeModel (τ := τ)).productIso A B).hom ab) =
    let p := TypeModel.productEquiv A B ab
    envToCategorical (Γ := B :: A :: Γ) ((ρ, p.1), p.2) := by rfl

/-- Interpret a direct dispatcher on the corresponding categorical inputs and outputs. -/
noncomputable def collectiveArrow {Γ : VCtx τ} {n : Nat} {R : Fin n → τ} {L : LCtx τ}
    (collective : Monadic.Env Γ × Monadic.FiniteLabelDen R →
      m (Monadic.LabelDen (List.ofFn R ++ L))) :
    (typeJ (m := m)).obj
      (Categorical.ctxObj (Categorical.ofMonadicTypeModel (τ := τ)) Γ ×
        Categorical.finiteLabelObj (Categorical.ofMonadicTypeModel (τ := τ)) R) ⟶
    (typeJ (m := m)).obj
      (Categorical.labelObj (Categorical.ofMonadicTypeModel (τ := τ)) (List.ofFn R ++ L)) :=
  Kleisli.Hom.mk (TypeCat.ofHom fun p =>
    (show m _ from collective (envFromCategorical p.1,
      (Monadic.finiteCategoricalEquiv R).symm p.2) >>= fun x =>
        pure (Monadic.LabelValue.categoricalEquiv (List.ofFn R ++ L) x)))

omit [Iterate m] [LawfulElgotMonad m] in
theorem collective_toCategorical {Γ : VCtx τ} {n : Nat}
    {R : Fin n → τ} {L : LCtx τ}
    {fb : ∀ i, Monadic.Env (R i :: Γ) →
      m (Monadic.LabelDen (List.ofFn R ++ L))}
    {collective : Monadic.Env Γ × Monadic.FiniteLabelDen R →
      m (Monadic.LabelDen (List.ofFn R ++ L))}
    (dc : Monadic.CollectiveDenotes Γ R L fb collective)
    {FB : ∀ i, (typeJ (m := m)).obj (Categorical.ctxObj (Categorical.ofMonadicTypeModel (τ := τ)) (R i :: Γ)) ⟶
      (typeJ (m := m)).obj (Categorical.labelObj (Categorical.ofMonadicTypeModel (τ := τ)) (List.ofFn R ++ L))}
    (eFB : ∀ i ρ, (FB i).of (envToCategorical ρ) =
      (fb i ρ >>= fun x =>
        (pure (Monadic.LabelValue.categoricalEquiv (List.ofFn R ++ L) x) :
          m (Categorical.labelObj (Categorical.ofMonadicTypeModel (τ := τ)) (List.ofFn R ++ L))))) :
    Categorical.CollectiveDenotes (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := τ)) Γ R L FB
      (collectiveArrow collective) := by
  constructor
  intro i
  apply Kleisli.hom_ext
  apply ConcreteCategory.hom_ext
  rintro ⟨ρ, a⟩
  unfold collectiveArrow
  erw [Kleisli.Type.comp_of_eq_kleisliRight]
  simp [Bind.kleisliRight]
  have hfinite : (Monadic.finiteCategoricalEquiv R).symm
      (Categorical.finiteLabelInject (Categorical.ofMonadicTypeModel (τ := τ)) R i a) =
      Monadic.finiteLabelInject R i a := by
    unfold Monadic.finiteCategoricalEquiv Categorical.finiteLabelInject
    apply CofanTypes.equivOfIsColimit_symm_apply
  change (Monadic.LabelValue.categoricalEquiv (List.ofFn R ++ L) <$>
    collective (envFromCategorical ρ,
      (Monadic.finiteCategoricalEquiv R).symm
        (Categorical.finiteLabelInject (Categorical.ofMonadicTypeModel (τ := τ)) R i a))) =
    (FB i).of (ρ, a)
  rw [hfinite, dc.restrict]
  have agreed := (eFB i (envFromCategorical ρ, a)).symm
  simpa [envToCategorical, envTo_from] using agreed

/-- Agreement for the program-independent CFG dispatcher. Both typing presentations
supply their entry and block interpretations to this same Elgot calculation. -/
theorem cfgDenotation_agrees {Γ : VCtx τ} {n : Nat} {R : Fin n → τ} {L : LCtx τ}
    {fe : Monadic.Env Γ → m (Monadic.LabelDen (List.ofFn R ++ L))}
    {FE : (typeJ (m := m)).obj (Categorical.ctxObj (Categorical.ofMonadicTypeModel (τ := τ)) Γ) ⟶
      (typeJ (m := m)).obj
        (Categorical.labelObj (Categorical.ofMonadicTypeModel (τ := τ)) (List.ofFn R ++ L))}
    (eFE : (fun ρ => FE.of (envToCategorical ρ)) =
      (fun ρ => fe ρ >>= fun x => pure (Monadic.LabelValue.categoricalEquiv (List.ofFn R ++ L) x)))
    (collective : Monadic.Env Γ × Monadic.FiniteLabelDen R →
      m (Monadic.LabelDen (List.ofFn R ++ L))) :
    let M := Categorical.ofMonadicTypeModel (τ := τ)
    let J := typeJ (m := m)
    let split := J.map (Categorical.labelAppendSplit M (List.ofFn R) L)
    let body := J.map ((𝟙 (Categorical.ctxObj M Γ)) ⊗ₘ Categorical.labelObjToFinite M R) ≫
      collectiveArrow collective ≫ split
    (fun ρ => (Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.caseWithContext J
      (FE ≫ split) (J.map (CartesianMonoidalCategory.snd _ _))
      (Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.contextualLoop J body)).of
        (envToCategorical ρ)) =
    (fun ρ => Monadic.cfgDenotation fe collective ρ >>= fun x =>
      pure (Monadic.LabelValue.categoricalEquiv L x)) := by
  unfold Monadic.cfgDenotation
  dsimp only
  funext ρ
  erw [caseWithContext_of]
  simp [Monadic.labelAppendSplit, Bind.kleisliRight, joinM, bind_map_left]
  refine (congrArg (fun (x : m _) => x >>= _) (congrFun eFE ρ)).trans ?_
  simp only [bind_assoc, pure_bind]
  apply bind_congr (m := m)
  intro target
  rw [Monadic.LabelValue.categoricalEquiv_appendSplit]
  generalize hsM : Monadic.LabelValue.appendSplit (List.ofFn R) L target = destination
  cases destination with
  | inl external =>
      simp
      rfl
  | inr loopTarget =>
      have hinr := congrArg (fun f => f (Monadic.LabelValue.categoricalEquiv (List.ofFn R) loopTarget))
        (Types.binaryCoproductIso_inr_comp_hom
        (Categorical.labelObj (Categorical.ofMonadicTypeModel (τ := τ)) L)
        (Categorical.labelObj (Categorical.ofMonadicTypeModel (τ := τ)) (List.ofFn R)))
      change
        (Types.binaryCoproductIso
          (Categorical.labelObj (Categorical.ofMonadicTypeModel (τ := τ)) L)
          (Categorical.labelObj (Categorical.ofMonadicTypeModel (τ := τ)) (List.ofFn R))).hom
            ((coprod.inr :
                Categorical.labelObj (Categorical.ofMonadicTypeModel (τ := τ)) (List.ofFn R) ⟶
                  Categorical.labelObj (Categorical.ofMonadicTypeModel (τ := τ)) L ⨿
                    Categorical.labelObj (Categorical.ofMonadicTypeModel (τ := τ)) (List.ofFn R))
              (Monadic.LabelValue.categoricalEquiv
                (List.ofFn R) loopTarget)) =
          Sum.inr (Monadic.LabelValue.categoricalEquiv
            (List.ofFn R) loopTarget) at hinr
      simp only
      rw [hinr]
      simp only
      erw [contextualLoop_of]
      let f := fun current =>
        Monadic.LabelValue.appendSplit (List.ofFn R) L <$>
          collective (ρ, Monadic.labelDenToFinite R current)
      let g := fun current =>
        Bind.kleisliRight (m := m)
          ((typeJ (m := m)).map (MonoidalCategoryStruct.whiskerLeft
                (Categorical.ctxObj (Categorical.ofMonadicTypeModel (τ := τ)) Γ)
                (Categorical.labelObjToFinite (Categorical.ofMonadicTypeModel (τ := τ)) R)) ≫ collectiveArrow collective ≫
            (typeJ (m := m)).map (Categorical.labelAppendSplit
              (Categorical.ofMonadicTypeModel (τ := τ)) (List.ofFn R) L)).of
          (fun s => pure ((Types.binaryCoproductIso
            (Categorical.labelObj (Categorical.ofMonadicTypeModel (τ := τ)) L)
            (Categorical.labelObj (Categorical.ofMonadicTypeModel (τ := τ)) (List.ofFn R))).hom s))
          (envToCategorical ρ, current)
      let k : Monadic.LabelValue L →
          m (Categorical.labelObj (Categorical.ofMonadicTypeModel (τ := τ)) L) :=
        fun x => pure (Monadic.LabelValue.categoricalEquiv L x)
      change Silmaril.Elgot.iter (m := m) g
          (Monadic.LabelValue.categoricalEquiv (List.ofFn R) loopTarget) =
        (Monadic.LabelValue.categoricalEquiv L) <$>
          Silmaril.Elgot.iter (m := m) f loopTarget
      rw [show (Monadic.LabelValue.categoricalEquiv L) <$>
            Silmaril.Elgot.iter (m := m) f loopTarget =
          Bind.kleisliRight (Silmaril.Elgot.iter (m := m) f) k loopTarget by
        simp [Bind.kleisliRight, k]]
      rw [LawfulElgotMonad.naturality]
      symm
      have hcomm :
          Bind.kleisliRight (Silmaril.Elgot.mapReturn f k)
              (Silmaril.Elgot.liftPure (Sum.map id
                (Monadic.LabelValue.categoricalEquiv (List.ofFn R)))) =
            Bind.kleisliRight
              (Silmaril.Elgot.liftPure
                (Monadic.LabelValue.categoricalEquiv (List.ofFn R))) g := by
        funext current
        set_option maxRecDepth 4096 in
          set_option maxHeartbeats 1000000 in
            simp [f, g, k, Silmaril.Elgot.mapReturn, Bind.kleisliRight,
            Silmaril.Elgot.liftPure, Monadic.labelDenToFinite, collectiveArrow,
            joinM, bind_map_left, Function.comp_def,
            Monadic.LabelValue.categoricalEquiv_appendSplit]
        let input := (Monadic.finiteCategoricalEquiv R).symm
          (Categorical.labelObjToFinite (Categorical.ofMonadicTypeModel (τ := τ)) R
            (Monadic.LabelValue.categoricalEquiv (List.ofFn R) current))
        have env_eq : envFromCategorical (envToCategorical ρ) = ρ := envFrom_to ρ
        simp only [← bind_pure_comp]
        change
          (collective (ρ, input) >>= _) =
          (collective (envFromCategorical (envToCategorical ρ), input) >>= _)
        rw [env_eq]
        apply bind_congr
        intro a
        cases Monadic.LabelValue.appendSplit (List.ofFn R) L a <;>
          simp
      have hu := congrFun (LawfulElgotMonad.uniformity
        (Silmaril.Elgot.mapReturn f k) g
        (Monadic.LabelValue.categoricalEquiv (List.ofFn R)) hcomm) loopTarget
      simpa [Silmaril.Elgot.liftPure, Bind.kleisliRight] using hu

/-- A direct monadic region witness induces a categorical witness in the
Kleisli/Freyd model with the same result on corresponding environments. -/
theorem regionDenotes_toCategorical {Γ : VCtx τ} {region : Region Φ} {L : LCtx τ}
    {h : Region.HasType Γ region L}
    {f : Monadic.Env Γ → m (Monadic.LabelDen L)}
    (d : Monadic.RegionDenotes (m := m) ε h f) :
    let _ := Categorical.ofMonadicInstructionModel
      (τ := τ) (Φ := Φ) (ε := ε) (m := m)
    ∃ F, Categorical.RegionDenotes (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := τ)) h F ∧
      (fun ρ => F.of (envToCategorical ρ)) =
        (fun ρ => f ρ >>= fun x => pure (Monadic.LabelValue.categoricalEquiv L x)) := by
  dsimp
  let _ := Categorical.ofMonadicInstructionModel
    (τ := τ) (Φ := Φ) (ε := ε) (m := m)
  induction d with
  | br dt =>
      rename_i Γ t A ht fa L i hi
      rcases denotes_toCategorical dt with ⟨F, dF, eF⟩
      refine ⟨_, Categorical.RegionDenotes.br (h := by assumption) dF, ?_⟩
      funext ρ
      erw [Kleisli.Type.comp_of_eq_kleisliRight]
      have hF := congrFun eF ρ
      simp only [Bind.kleisliRight, Monadic.labelInject, bind_pure_comp, Functor.map_map]
      refine (congrArg (fun (x : m _) => x >>= _) hF).trans ?_
      let inject : TyDen A → Monadic.CategoricalLabelDen L := fun a =>
        Categorical.labelInject (Categorical.ofMonadicTypeModel (τ := τ)) i hi a
      let equiv := Monadic.LabelValue.categoricalEquiv L
      change (fa ρ >>= fun a => pure (inject a)) =
        (fun a => equiv (equiv.symm (inject a))) <$> fa ρ
      exact (bind_pure_comp (m := m) inject (fa ρ)).trans
        (congrArg (fun g : TyDen A → Monadic.CategoricalLabelDen L => g <$> fa ρ)
          (funext fun a => (equiv.apply_symm_apply (inject a)).symm))
  | case de dl dr ihl ihr =>
      rcases denotes_toCategorical de with ⟨E, dE, eE⟩
      rcases ihl with ⟨FL, dFL, eFL⟩
      rcases ihr with ⟨FR, dFR, eFR⟩
      refine ⟨_, .case dE dFL dFR, ?_⟩
      funext ρ
      erw [caseWithContext_of]
      simp [Bind.kleisliRight, joinM, bind_map_left]
      refine congrArg₂ (fun (x : m _) (k : _ → m _) => x >>= k) (congrFun eE ρ) ?_
      funext e
      rw [coprod_hom_agrees]
      cases TypeModel.coprodEquiv _ _ e with
      | inl a =>
          have agreed := congrFun eFL (ρ, a)
          change (_ : m _) = _ at agreed
          rwa [bind_pure_comp] at agreed
      | inr b =>
          have agreed := congrFun eFR (ρ, b)
          change (_ : m _) = _ at agreed
          rwa [bind_pure_comp] at agreed
  | let₁ da db ihb =>
      rcases denotes_toCategorical da with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .let₁ dF dG, ?_⟩
      funext ρ
      erw [bind_of]
      simp only [Bind.kleisliRight, bind_assoc]
      exact congrArg₂ (fun (x : m _) (k : _ → m _) => x >>= k)
        (congrFun eF ρ) (funext fun a => congrFun eG (ρ, a))
  | let₂ da db ihb =>
      rename_i Γ t A B ha fa r L hb fb
      rcases denotes_toCategorical da with ⟨F, dF, eF⟩
      rcases ihb with ⟨G, dG, eG⟩
      refine ⟨_, .let₂ dF dG, ?_⟩
      funext ρ
      erw [bind_of]
      simp [Bind.kleisliRight]
      refine congrArg₂ (fun (x : m _) (k : _ → m _) => x >>= k) (congrFun eF ρ) ?_
      funext ab
      let values := TypeModel.productEquiv A B ab
      have agreed := congrFun eG ((ρ, values.1), values.2)
      change (_ : m _) = _ at agreed
      rwa [bind_pure_comp] at agreed
  | cfgZero he hb de ih =>
      rcases ih with ⟨F, dF, eF⟩
      exact ⟨F, .cfgZero he hb dF, eF⟩
  | cfg he hb de db dc ihe ihb =>
      rcases ihe with ⟨FE, dFE, eFE⟩
      choose FB dFB eFB using ihb
      rename_i n R Γ L entry blocks fe fb collective
      let FC := collectiveArrow collective
      have dFC : Categorical.CollectiveDenotes (typeJ (m := m)) (Categorical.ofMonadicTypeModel (τ := τ))
          Γ R L FB FC := collective_toCategorical dc (fun i ρ => congrFun (eFB i) ρ)
      refine ⟨_, .cfg he hb dFE dFB dFC, ?_⟩
      exact cfgDenotation_agrees (Γ := Γ) (R := R) (L := L) (fe := fe) (FE := FE) eFE collective

end Agreement
end Silmaril.Isotope.LambdaSSA.Semantics
