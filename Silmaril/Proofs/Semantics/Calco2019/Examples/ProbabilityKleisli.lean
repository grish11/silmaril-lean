module

public import Silmaril.Semantics.Calco2019.Examples.Probability.Thms
public import Silmaril.Semantics.Calco2019.CompleteElgot.Defs

public section

open scoped ENNReal

namespace Silmaril.Calco2019.Examples.Probability.KleisliProofs

universe u

open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local notation "T" => ofTypeMonad PMF
local notation "K" => typeCoproducts.kleisli T
local notation "J" => Kleisli.Adjunction.toKleisli T

variable {A B C D : Type u}

private noncomputable abbrev arrow {X Y : Type u} (f : X → PMF Y) := computation PMF f
private noncomputable abbrev pureArrow {X Y : Type u} (h : X → Y) := (J).map (↾h)

private theorem comp (f : A → PMF B) (g : B → PMF C) :
    arrow f ≫ arrow g = arrow (fun x => (f x).bind g) := by
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  exact Kleisli.Type.comp_of_eq_kleisliRight PMF _ _

private theorem pure_comp (h : A → B) (g : B → PMF C) :
    pureArrow h ≫ arrow g = arrow (g ∘ h) := by
  change arrow (PMF.pure ∘ h) ≫ arrow g = _
  rw [comp]
  simp only [Function.comp_apply, PMF.pure_bind]
  rfl

private theorem comp_pure (f : A → PMF B) (h : B → C) :
    arrow f ≫ pureArrow h = arrow (fun x => (f x).map h) := by
  change arrow f ≫ arrow (PMF.pure ∘ h) = _
  rw [comp]
  rfl

private theorem desc (f : A → PMF C) (g : B → PMF C) :
    (K).desc (arrow f) (arrow g) = arrow (Sum.elim f g) := by
  apply (K).hom_ext
  · rw [(K).inl_desc]
    exact (pure_comp Sum.inl (Sum.elim f g)).symm
  · rw [(K).inr_desc]
    exact (pure_comp Sum.inr (Sum.elim f g)).symm

private theorem map_pure (f : A → C) (g : B → D) :
    (K).map (pureArrow f) (pureArrow g) = pureArrow (Sum.map f g) := by
  unfold Coproducts.map
  apply (K).hom_ext
  · rw [(K).inl_desc]
    change (J).map (↾f) ≫ (J).map (↾Sum.inl) = (J).map (↾Sum.inl) ≫ (J).map (↾(Sum.map f g))
    rw [← (J).map_comp, ← (J).map_comp]
    rfl
  · rw [(K).inr_desc]
    change (J).map (↾g) ≫ (J).map (↾Sum.inr) = (J).map (↾Sum.inr) ≫ (J).map (↾(Sum.map f g))
    rw [← (J).map_comp, ← (J).map_comp]
    rfl

noncomputable def pmfGuard : MonadGuardedness typeCoproducts.{u} T where
  guarded {X Y Z} f := Guarded (fun x : X.of => f.of x)
  trivial {X Y Z} f := by
    obtain ⟨A⟩ := X
    obtain ⟨B⟩ := Y
    obtain ⟨C⟩ := Z
    let f' : A → PMF B := f.of
    change Guarded (fun x => (arrow f' ≫ pureArrow (Sum.inl : B → B ⊕ C)).of x)
    rw [comp_pure]
    intro x
    obtain ⟨y, hy⟩ := (f' x).support_nonempty
    refine ⟨y, ?_⟩
    change 0 < ((f' x).map (Sum.inl : B → B ⊕ C)) (.inl y)
    rw [PMF.apply_pos_iff, PMF.mem_support_map_iff]
    exact ⟨y, hy, rfl⟩
  parallel {X Y V W} {f g} hf hg := by
    obtain ⟨A⟩ := X
    obtain ⟨B⟩ := Y
    obtain ⟨C⟩ := V
    obtain ⟨D⟩ := W
    let f' : A → PMF (C ⊕ D) := f.of
    let g' : B → PMF (C ⊕ D) := g.of
    change Guarded (fun x => ((K).desc (arrow f') (arrow g')).of x)
    rw [desc]
    change Guarded (Sum.elim f' g')
    intro x
    cases x with
    | inl a => exact hf a
    | inr b => exact hg b
  compose {X Y Z V W} {f g} h hf hg := by
    obtain ⟨A⟩ := X
    obtain ⟨B⟩ := Y
    obtain ⟨C⟩ := Z
    obtain ⟨D⟩ := V
    obtain ⟨E⟩ := W
    let f' : A → PMF (B ⊕ C) := f.of
    let g' : B → PMF (D ⊕ E) := g.of
    let h' : C → PMF (D ⊕ E) := h.of
    change Guarded (fun x => (arrow f' ≫ (K).desc (arrow g') (arrow h')).of x)
    rw [desc, comp]
    intro a
    obtain ⟨b, hb⟩ := hf a
    obtain ⟨d, hd⟩ := hg b
    refine ⟨d, ?_⟩
    change 0 < ((f' a).bind (Sum.elim g' h')) (.inl d)
    rw [PMF.apply_pos_iff, PMF.mem_support_bind_iff]
    exact ⟨.inl b, (PMF.apply_pos_iff _ _).mp hb, (PMF.apply_pos_iff _ _).mp hd⟩

theorem guarded_iff (f : A → PMF (B ⊕ C)) : pmfGuard.guarded (computation PMF f) ↔ Guarded f := by
  unfold pmfGuard
  rfl

private theorem step_bind (f : A → PMF (B ⊕ A)) (g : A → PMF B) (x : A) (y : B) :
    step f (fun x y => g x y) x y = ((f x).bind (Sum.elim PMF.pure g)) y := by
  classical
  rw [step, PMF.bind_apply, Summable.tsum_sum CompleteLattice.summable CompleteLattice.summable]
  simp only [Sum.elim_inl, Sum.elim_inr]
  congr 1
  symm
  rw [tsum_eq_single y]
  · simp
  · intro b hb
    rw [PMF.pure_apply_of_ne b y (Ne.symm hb), mul_zero]

theorem pmf_fixpoint_iff (f : A → PMF (B ⊕ A)) (g : A → PMF B) :
    Guardedness.IsFixpoint (P := K) (computation PMF f) (computation PMF g) ↔
      step f (fun x y => g x y) = fun x y => g x y := by
  change (arrow f ≫ (K).desc (arrow PMF.pure) (arrow g) = arrow g) ↔ _
  rw [desc, comp]
  constructor
  · intro h
    funext x y
    rw [step_bind]
    exact congrArg (fun q => (show PMF B from q.of x) y) h
  · intro h
    apply Kleisli.hom_ext
    apply ConcreteCategory.coe_ext
    funext x
    apply PMF.ext
    intro y
    exact (step_bind f g x y).symm.trans (congrFun (congrFun h x) y)

theorem normalized_pmf_counterexample :
    ¬ Guardedness.IsFixpoint (P := K) (computation PMF (chain coloredExit))
      (computation PMF (normalized (chain coloredExit) (chain_guarded coloredExit))) := by
  intro h
  have h₀ := congrFun (congrFun ((pmf_fixpoint_iff _ _).mp h) 0) false
  simp only [normalized_apply] at h₀
  exact normalized_not_fixpoint h₀

theorem normalized_pmf_fixpoint_of_mass_one (f : A → PMF (B ⊕ A)) (hf : Guarded f)
    (hm : ∀ x, mass (least f) x = 1) :
    Guardedness.IsFixpoint (P := K) (computation PMF f) (computation PMF (normalized f hf)) := by
  apply (pmf_fixpoint_iff _ _).mpr
  have h : (fun x y => normalized f hf x y) = least f := by
    funext x y
    simp [normalizedWeight, hm x]
  rw [h, least_fixpoint]

private theorem iterate_congr (I : pmfGuard.{u}.Conway)
    {X Y : Kleisli T} {f g : X ⟶ (K).sum Y X} (h : f = g)
    (hf : pmfGuard.guarded f) (hg : pmfGuard.guarded g) :
    I.iterate f hf = I.iterate g hg := by
  subst g
  rfl

theorem no_conway_uniform (I : pmfGuard.{0}.Conway)
    (hu : I.toFixpoints.Uniform J) : False := by
  let run (f : ℕ → PMF (ℕ ⊕ ℕ)) (hf : Guarded f) (x : ℕ) : PMF ℕ :=
    (I.iterate (arrow f) ((guarded_iff f).mpr hf)).of x
  have hid : pureArrow (id : ℕ → ℕ) = 𝟙 (Kleisli.mk T ℕ) := (J).map_id ℕ
  let N : NatIteration := {
    run
    fixpoint := fun f hf => (pmf_fixpoint_iff f (run f hf)).mp
      (I.fixpoint (arrow f) ((guarded_iff f).mpr hf))
    naturality := fun f g hf hg h comm x => by
      have hmap : arrow f ≫ (K).map (pureArrow h) (𝟙 _) = arrow g := by
        rw [← hid]
        change arrow f ≫ (K).map (pureArrow h) (pureArrow id) = arrow g
        rw [map_pure, comp_pure]
        exact congrArg arrow (funext comm)
      have hguard := (guarded_iff g).mpr hg
      have law := I.naturalCodiagonal.naturality (arrow f) (pureArrow h)
        ((guarded_iff f).mpr hf) (hmap.symm ▸ hguard)
      have law := (iterate_congr I hmap _ hguard).symm.trans law
      change arrow (run g hg) = arrow (run f hf) ≫ pureArrow h at law
      rw [comp_pure] at law
      exact congrArg (fun q => q.of x) law.symm
    uniformity := fun f g hf hg h comm x => by
      have hmap : pureArrow h ≫ arrow g = arrow f ≫ (K).map (𝟙 _) (pureArrow h) := by
        rw [← hid]
        change pureArrow h ≫ arrow g = arrow f ≫ (K).map (pureArrow id) (pureArrow h)
        rw [map_pure, pure_comp, comp_pure]
        exact congrArg arrow (funext comm).symm
      have law := hu (arrow g) (arrow f) (↾h) ((guarded_iff g).mpr hg)
        ((guarded_iff f).mpr hf) hmap
      change pureArrow h ≫ arrow (run g hg) = arrow (run f hf) at law
      rw [pure_comp] at law
      exact congrArg (fun q => q.of x) law.symm
  }
  exact no_nat_iteration.false N

theorem no_total_fixpoints (F : (Guardedness.greatest (typeCoproducts.kleisli
    (ofTypeMonad PMF.{0}))).Fixpoints) : False := by
  let loop : Unit → PMF (Empty ⊕ Unit) := fun x => PMF.pure (.inr x)
  let p : PMF Empty := (F.iterate (computation PMF loop) True.intro).of ()
  have h := p.tsum_coe
  simp at h

end Silmaril.Calco2019.Examples.Probability.KleisliProofs
