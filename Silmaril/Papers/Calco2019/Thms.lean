module

public import Silmaril.Papers.Calco2019.Defs
public import Silmaril.Semantics.Calco2019.Thms
public import Silmaril.Semantics.Calco2019.ResumptionThms
public import Silmaril.Semantics.Calco2019.InductiveResumption.Free.Thms
public import Silmaril.Semantics.Calco2019.Maybe.Resumption.Thms
public import Silmaril.Semantics.Calco2019.Maybe.Hyperextensive.Iteration.Thms
public import Silmaril.Semantics.Calco2019.ResumptionConway
public import Silmaril.Semantics.Calco2019.VacuousThms
public import Silmaril.Semantics.Calco2019.ExceptionResumption.Specializations

/-! # Numbered results for CALCO 2019, Article 13 -/

public section

universe u v u' v'

namespace Silmaril.Papers.Calco2019

open CategoryTheory CategoryTheory.Limits Silmaril.Calco2019

/-- Section 1.3. On Set, Maybe resumptions freely add the operations of the
endofunctor in the category of total Elgot monads. -/
theorem maybeResumption_freeOn {H : Type u ⥤ Type u}
    (R : FinalResumptions (Exception.parametrizedElgot Maybe.Types.elgot.{u} H).toParametrizedMonad)
    (S : Maybe.TotalElgot (typeCoproducts : Coproducts (Type u)))
    (σ : H ⟶ (S.obj.monad : Type u ⥤ Type u)) :
    ∃! k : (⟨(Exception.parametrizedElgot Maybe.Types.elgot H).resumptionElgotMonad R,
        Exception.resumption_isElgot Maybe.Types.elgot H R Maybe.Types.elgot_total⟩ :
          Maybe.TotalElgot typeCoproducts) ⟶ S,
      Exception.suspension Maybe.Types.elgot H R ≫ k.hom.hom.toNatTrans = σ :=
  Maybe.resumption_freeOn Maybe.Types.elgot_total R Maybe.Types.initial S σ

/-- Section 1.3. On a hyperextensive category, Maybe resumptions freely add
the operations of the endofunctor among total Elgot monads. -/
theorem hyperextensiveMaybeResumption_freeOn {C : Type u} [Category.{v} C] [Maybe.Hyperextensive C]
    {P : Coproducts C} {E : C} (terminal : IsTerminal E) {H : C ⥤ C}
    (R : FinalResumptions (Exception.parametrizedElgot (Maybe.hyperextensiveElgot (P := P)
      terminal) H).toParametrizedMonad)
    (S : Maybe.TotalElgot P) (σ : H ⟶ (S.obj.monad : C ⥤ C)) :
    ∃! k : (⟨(Exception.parametrizedElgot (Maybe.hyperextensiveElgot terminal) H).resumptionElgotMonad R,
        Exception.resumption_isElgot (Maybe.hyperextensiveElgot terminal) H R
          (Maybe.hyperextensiveElgot_total terminal)⟩ : Maybe.TotalElgot P) ⟶ S,
      Exception.suspension (Maybe.hyperextensiveElgot terminal) H R ≫ k.hom.hom.toNatTrans = σ :=
  Maybe.resumption_freeOn (Maybe.hyperextensiveElgot_total terminal) R
    (Maybe.hyperextensiveInitial terminal) S σ

section InductiveResumptions

variable {C : Type u} [Category.{v} C] (P : Coproducts C)

/-- Section 1.2. The chosen initial algebras of `Z ↦ T (X + H Z)` give the
inductive resumption monad. -/
abbrev inductiveResumption (T : CategoryTheory.Monad C) (H : C ⥤ C)
    (R : InitialResumptions (Exception.parametrized P T H)) : CategoryTheory.Monad C :=
  R.monad

/-- Section 1.3. Inductive resumptions give an ordinary free extension
of the base monad by the operation endofunctor. -/
theorem inductiveFreeExtension (T : CategoryTheory.Monad C) (H : C ⥤ C)
    (R : InitialResumptions (Exception.parametrized P T H)) :
    (Inductive.monadBimodule C).IsFreeExtension (Inductive.suspension P R)
      (Inductive.baseEmbedding P R) :=
  Inductive.resumption_free P R

end InductiveResumptions

section FreeExtensions

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {O : Bimodule C D} {A : C} {B I V W : D}

/-- Proposition 4. The initial leg is unique at every vertex. -/
theorem proposition4 (i : IsInitial I) (e : O.Hom A V) :
    O.IsFreeExtension e (i.to V) ↔ O.IsFreeObject e :=
  isFreeExtension_initial_iff i e

/-- Proposition 5. The free object determines the left coproduct leg uniquely from the
free-extension generator. -/
theorem proposition5 {d : O.Hom A W} (hd : O.IsFreeObject d) (l : W ⟶ V) (r : B ⟶ V) :
    O.IsFreeExtension (O.post d l) r ↔ Nonempty (IsColimit (BinaryCofan.mk l r)) :=
  isFreeExtension_coprod_iff hd l r

/-- Proposition 5, recovering the left leg from a free extension. -/
theorem proposition5_coprodLeg {d : O.Hom A W} (hd : O.IsFreeObject d)
    {e : O.Hom A V} {r : B ⟶ V} (hr : O.IsFreeExtension e r) :
    ∃! l : W ⟶ V, O.post d l = e ∧ Nonempty (IsColimit (BinaryCofan.mk l r)) :=
  freeExtension_coprodLeg hd hr

end FreeExtensions

section Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A X Y Z V W : K}

/-- Proposition 8(1). -/
theorem proposition8_initial (i : IsInitial A) : G.guarded (i.to (P.sum Y Z)) :=
  G.initial i

/-- Proposition 8(2). -/
theorem proposition8_comp {f : X ⟶ P.sum Y Z} (hf : G.guarded f)
    (u : A ⟶ X) (g : Y ⟶ V) (h : Z ⟶ W) : G.guarded (u ≫ f ≫ P.map g h) :=
  G.precomp (G.map hf g h) u

/-- Proposition 8(3). -/
theorem proposition8_weakening {f : X ⟶ P.sum (P.sum Y Z) W} (hf : G.nested f) :
    G.guarded f :=
  G.weaken hf

/-- Proposition 9(1). Total guardedness is greatest. -/
theorem proposition9_greatest {f : X ⟶ P.sum Y Z} :
    G.guarded f → (Guardedness.greatest P).guarded f := fun _ => True.intro

/-- Proposition 9(2). Factoring through the left injection gives the least guardedness. -/
theorem proposition9_least {f : X ⟶ P.sum Y Z} :
    ((Guardedness.least P).guarded f ↔ ∃ g, f = g ≫ P.inl) ∧
      ((Guardedness.least P).guarded f → G.guarded f) :=
  ⟨Iff.rfl, G.least_le⟩

/-- Lemma 13. -/
theorem lemma13 {f : X ⟶ P.sum (P.sum Y Z) X} (hf : G.nested f)
    {g : X ⟶ P.sum Y Z} (hg : Guardedness.IsFixpoint f g) : G.guarded g :=
  G.guarded_fixpoint hf hg

/-- Proposition 17. Dinaturality follows from naturality, codiagonal and uniformity
along a functor preserving the selected coproducts and covering every object. -/
theorem proposition17 (F : G.Fixpoints)
    {C : Type u'} [Category.{v'} C] {Q : Coproducts C} {J : C ⥤ K}
    (S : PreservesSelectedCoproducts Q P J) (surj : Function.Surjective J.obj) :
    (F.NaturalCodiagonal ∧ F.Uniform J) ↔
      (F.NaturalCodiagonal ∧ F.Dinaturality ∧ F.Uniform J) :=
  ⟨fun ⟨n, u⟩ => ⟨n, F.dinaturality_of_uniform S surj n u, u⟩, fun ⟨n, _, u⟩ => ⟨n, u⟩⟩

/-- Proposition 18. Unique fixpoints satisfy the Conway laws and uniformity for every map. -/
theorem proposition18 (h : G.Iterative) :
    (Guardedness.Fixpoints.ofIterative h).NaturalCodiagonal ∧
      (Guardedness.Fixpoints.ofIterative h).Dinaturality ∧
      (Guardedness.Fixpoints.ofIterative h).Uniform (𝟭 K) :=
  ⟨Guardedness.Fixpoints.ofIterative_naturalCodiagonal h,
    Guardedness.Fixpoints.ofIterative_dinaturality h,
    Guardedness.Fixpoints.ofIterative_uniform h (𝟭 K)⟩

/-- The general vacuous-guardedness assertion of Example 20(1). -/
theorem example20_vacuous : (Guardedness.least P).Iterative :=
  Guardedness.vacuous_iterative

end Guardedness

section Elgot

variable {C : Type u} [Category.{v} C] {P : Coproducts C}

/-- The observation after Definition 19, with the initial object as the result type. -/
theorem definition19_divergence (T : GuardedElgotMonad P) (h : T.IsElgot) [HasInitial C] (X : C) :
    Nonempty (X ⟶ T.monad.obj (⊥_ C)) :=
  T.divergent_at h X (⊥_ C)

end Elgot

section Exception

variable {C : Type u} [Category.{v} C] (P : Coproducts C)

/-- The underlying monad-valued functor of Example 22 has the stated object action. -/
theorem example22_carrier (T : CategoryTheory.Monad C) (H : C ⥤ C) (X W : C) :
    ((Exception.parametrized P T H).obj W).obj X = T.obj (P.sum X (H.obj W)) :=
  rfl

/-- The guard in Example 22 agrees with guardedness after moving the parameter
into the return summand in the base monad. -/
theorem example22_guard {T : GuardedElgotMonad P} {E X Y Z : C}
    (f : X ⟶ T.monad.obj (P.sum (P.sum Y Z) E)) :
    (Exception.guardedness T E).guarded
      (Y := Kleisli.mk ((Exception.family P T.monad).obj E) Y)
      (Z := Kleisli.mk ((Exception.family P T.monad).obj E) Z) (kleisliArrow f) ↔
    Exception.Guard P T E (Y := Y) (Z := Z) f :=
  Iff.rfl

/-- Pure uniformity for the chosen fixed-parameter iteration of Example 22. -/
theorem example22_uniformity (T : GuardedElgotMonad P) (E : C) :
    (Exception.fixpoints T E).Uniform
      (Kleisli.Adjunction.toKleisli ((Exception.family P T.monad).obj E)) :=
  Exception.uniformity T E

/-- Example 22. The parametrized guarded Elgot monad has the paper's carrier. -/
theorem example22 (T : GuardedElgotMonad P) (H : C ⥤ C) (X W : C) :
    ((Exception.parametrizedElgot T H).obj W).monad.obj X = T.monad.obj (P.sum X (H.obj W)) :=
  rfl

/-- Corollary 26. The guarded Elgot structure of the coinductive exception resumptions. -/
noncomputable def corollary26 (T : GuardedElgotMonad P) (H : C ⥤ C)
    (R : FinalResumptions (Exception.parametrizedElgot T H).toParametrizedMonad) :
    { S : GuardedElgotMonad P // S.monad = R.monad P } :=
  ⟨(Exception.parametrizedElgot T H).resumptionElgotMonad R, rfl⟩

/-- Lemma 27(1). The suspension generator is guarded. -/
theorem lemma27_suspension [HasInitial C] (T : GuardedElgotMonad P) (H : C ⥤ C)
    (R : FinalResumptions (Exception.parametrizedElgot T H).toParametrizedMonad) :
    MonadGuardedness.GuardedNatTrans P ((Exception.parametrizedElgot T H).resumptionElgotMonad R).guard
      (Exception.suspension T H R) :=
  Exception.suspension_guarded T H R

/-- Lemma 27(2). The base embedding is a guarded Elgot monad morphism with the
stated components. -/
theorem lemma27_base (T : GuardedElgotMonad P) (H : C ⥤ C)
    (R : FinalResumptions (Exception.parametrizedElgot T H).toParametrizedMonad) :
    ∃ e : GuardedElgotMonadHom P T ((Exception.parametrizedElgot T H).resumptionElgotMonad R),
      ∀ X, e.hom.app X = T.monad.map (P.inl (Y := H.obj (R.obj X))) ≫ R.roll X :=
  ⟨Exception.baseEmbedding T H R, Exception.baseEmbedding_app T H R⟩

/-- Theorem 28. Exception resumptions freely extend the guarded Elgot base by
the endofunctor, with the specified base and suspension embeddings. -/
theorem theorem28 [HasInitial C] (T : GuardedElgotMonad P) (H : C ⥤ C)
    (R : FinalResumptions (Exception.parametrizedElgot T H).toParametrizedMonad) :
    (guardedBimodule P).IsFreeExtension (Exception.resumptionGenerator R)
      (Exception.baseEmbedding T H R) :=
  Exception.resumption_free R

/-- Corollary 29. The second coproduct summand comes from the final coalgebras
of `Z ↦ X + H Z`, the identity-base instance of the resumption construction. -/
theorem corollary29 [HasInitial C] (T : GuardedElgotMonad P) (H : C ⥤ C)
    (R : FinalResumptions (Exception.parametrizedElgot T H).toParametrizedMonad)
    (R₀ : FinalResumptions (Exception.parametrizedElgot (guardedIdentity P) H).toParametrizedMonad) :
    ∃! l : (Exception.parametrizedElgot (guardedIdentity P) H).resumptionElgotMonad R₀ ⟶
        (Exception.parametrizedElgot T H).resumptionElgotMonad R,
      (guardedBimodule P).post (Exception.resumptionGenerator R₀) l = Exception.resumptionGenerator R ∧
        Nonempty (IsColimit (BinaryCofan.mk l (Exception.baseEmbedding T H R))) :=
  Exception.resumption_coproduct R R₀

end Exception

section Resumptions

variable {C : Type u} [Category.{v} C] {M : ParametrizedMonad C}
  (R : FinalResumptions M) (P : Coproducts C) {X Y : C}

include P in
/-- Proposition 23(1). The extension is the unique solution of the observation diagram. -/
theorem proposition23_extension (f : X ⟶ R.obj Y) : ∃! k, R.IsExtension f k :=
  ⟨R.extend P f, R.extend_spec P f, fun k hk => R.extend_unique P f k hk⟩

/-- Proposition 23(2). The recursive diagram has a unique solution.
The input uses the sum order in the paper's diagram. -/
theorem proposition23_solution (f : X ⟶ (M.obj (R.obj (P.sum Y X))).obj Y) :
    ∃! g, R.IsSolution P f g :=
  ⟨R.solve P f, R.solve_spec P f, fun g hg => R.solve_unique P f g hg⟩

/-- Proposition 23(3). The monad built from the observation map has the specified unit
and Kleisli extension. Its carrier at `X` is `R.obj X` by construction. -/
theorem proposition23_monad (f : X ⟶ R.obj Y) :
    (R.monad P).η.app X = (M.obj (R.obj X)).η.app X ≫ R.roll X ∧
      (R.monad P).map f ≫ (R.monad P).μ.app Y = R.extend P f :=
  ⟨rfl, R.monad_extend P f⟩

end Resumptions

section GuardedResumptions

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (M : ParametrizedGuardedElgotMonad P) (R : FinalResumptions M.toParametrizedMonad)
  {X Y : C}

/-- The unique observation-diagram solution in Theorem 25. -/
theorem theorem25_characterization (f : X ⟶ R.obj (P.sum Y X))
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    ∃! g, R.IsSolution P (M.diamond R f hf) g :=
  ⟨M.iterateResumption R f hf, (M.iterateResumption_characterization R f hf).1,
    (M.iterateResumption_characterization R f hf).2⟩

/-- The fixpoint law for the iteration in Theorem 25. -/
theorem theorem25_fixpoint (f : X ⟶ R.obj (P.sum Y X))
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    f ≫ R.extend P (P.desc (R.unit Y) (M.iterateResumption R f hf)) =
      M.iterateResumption R f hf :=
  M.iterateResumption_fixpoint R f hf

/-- Pure uniformity for the iteration in Theorem 25. -/
theorem theorem25_uniformity {Z : C}
    (f : X ⟶ R.obj (P.sum Y X)) (g : Z ⟶ R.obj (P.sum Y Z)) (h : Z ⟶ X)
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f)
    (hg : M.ResumptionGuard R (Y := Y) (Z := Z) g)
    (comm : h ≫ f = g ≫ (R.monad P).map (P.map (𝟙 Y) h)) :
    h ≫ M.iterateResumption R f hf = M.iterateResumption R g hg :=
  M.iterateResumption_uniform R f g h hf hg comm

/-- Naturality for the iteration in Theorem 25. -/
theorem theorem25_naturality {Z : C} (f : X ⟶ R.obj (P.sum Y X)) (g : Y ⟶ R.obj Z)
    (hf : M.ResumptionGuard R (Y := Y) (Z := X) f) :
    M.iterateResumption R (M.naturalityBody R f g) (M.naturalityBody_guarded R f g hf) =
      M.iterateResumption R f hf ≫ R.extend P g :=
  M.iterateResumption_naturality R f g hf

/-- Theorem 25. The resumption monad is guarded Elgot, with the uniquely
characterized solution on every guarded loop. -/
theorem theorem25 (f : Kleisli.mk (R.monad P) X ⟶ Kleisli.mk (R.monad P) (P.sum Y X))
    (hf : (M.resumptionElgotMonad R).guard.guarded
      (Y := Kleisli.mk (R.monad P) Y) (Z := Kleisli.mk (R.monad P) X) f) :
    (M.resumptionElgotMonad R).monad = R.monad P ∧
      R.IsSolution P (M.diamond R f.of ((M.resumptionGuardedness_iff R f).mp hf))
        ((M.resumptionElgotMonad R).iteration.iterate f hf).of ∧
      ∀ g, R.IsSolution P (M.diamond R f.of ((M.resumptionGuardedness_iff R f).mp hf)) g →
        g = ((M.resumptionElgotMonad R).iteration.iterate f hf).of :=
  ⟨rfl, M.iterateResumption_characterization R f.of ((M.resumptionGuardedness_iff R f).mp hf)⟩

end GuardedResumptions
end Silmaril.Papers.Calco2019
