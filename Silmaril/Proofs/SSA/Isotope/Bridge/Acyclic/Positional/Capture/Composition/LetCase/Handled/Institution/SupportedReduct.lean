module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Reduct.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Logic.Institution (Room)
open Silmaril.Isotope.Institution.Acyclic (CoherentRegionModel restrictInstructions ssaSignatureCorridor
  ssaSignatureCorridor_primitive_mod)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation mapRanked sat_mapRanked mapRanked_id mapRanked_comp
  rankedSignatureCorridor)
open LetIter.Semantics.Categorical (TypeModel InstructionModel TypingCoherent denote)
open LetIter.LocallyNameless (Derivation)

variable {τ ε : Type}

private theorem hom_cases_aux {Q : InstrSig τ ε}
    (motive : ∀ {P : InstrSig τ ε}, (P ⟶ Q) → Prop)
    (pulled : ∀ {Φ : Type} (r : Φ → Q.Instr), motive (pullHom Q r))
    (Φ : Type) (hasTy : HasTy Φ τ) (hasEff : HasEff Φ ε) (r : Φ → Q.Instr)
    (source : ∀ x, instrSrc (r x) = hasTy.src x) (target : ∀ x, instrTrg (r x) = hasTy.trg x)
    (effect : ∀ x, instrEff (r x) = hasEff.eff x) :
    motive (P := @InstrSig.mk τ ε Φ hasTy hasEff) ⟨r, source, target, effect⟩ := by
  have types : hasTy = ⟨fun x => instrSrc (r x), fun x => instrTrg (r x)⟩ := by
    cases hasTy with
    | mk src trg => exact congrArg₂ HasTy.mk (funext fun x => (source x).symm) (funext fun x => (target x).symm)
  have effects : hasEff = ⟨fun x => instrEff (r x)⟩ := by
    cases hasEff with
    | mk eff => exact congrArg HasEff.mk (funext fun x => (effect x).symm)
  subst types effects
  exact pulled r

/-- Every relabelling is the instruction map of a pulled-back signature. -/
theorem instrSig_hom_cases_proof {Q : InstrSig τ ε}
    (motive : ∀ {P : InstrSig τ ε}, (P ⟶ Q) → Prop)
    (pulled : ∀ {Φ : Type} (r : Φ → Q.Instr), motive (pullHom Q r))
    {P : InstrSig τ ε} (f : P ⟶ Q) : motive f := by
  cases P with
  | @mk Φ hasTy hasEff =>
    rcases f with ⟨r, source, target, effect⟩
    exact hom_cases_aux motive pulled Φ hasTy hasEff r source target effect

variable [TypeFormers τ]
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  {Q : InstrSig τ ε} {Φ : Type} (r : Φ → Q.Instr)
  (M : TypeModel τ V) (I : InstructionModel J M Q.Instr)
  {ν : Type} [DecidableEq ν] {Γ : Ctx ν τ}

/-- The arrow of a derivation in the reduct interpretation is the arrow of
the relabelled derivation in the original interpretation. -/
theorem denote_relabel_proof {n : Nat} {β : BoundCtx τ n} {t : LetIter.LocallyNameless.Tm ν Φ n} {A : τ}
    (d : Derivation (pullSig Q r).Instr Γ β t A) :
    (letI := restrictInstructions (pullHom Q r) I; denote J M d) = (letI := I; denote J M (relabelIter d)) := by
  induction d with
  | fv h => rfl
  | bv => rfl
  | unit => rfl
  | op ha ih => exact congrArg (fun x => x ≫ I.denote (r _)) ih
  | inl ha ih | inr ha ih | abort ha ih =>
    simp only [denote, relabelIter] at ih ⊢
    rw [ih]
    rfl
  | let₁ ha hb iha ihb | pair ha hb iha ihb | let₂ ha hb iha ihb | iter ha hb iha ihb =>
    simp only [denote, relabelIter] at iha ihb ⊢
    rw [iha, ihb]
    rfl
  | case he hl hr ihe ihl ihr =>
    simp only [denote, relabelIter] at ihe ihl ihr ⊢
    rw [ihe, ihl, ihr]
    rfl

section Law

variable {τ ε : Type} [TypeFormers τ]
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] {P Q S : InstrSig τ ε} {pe : ε}

omit [FreydCategory.CentralUnit J] in
private theorem supported_reduct_pulled {Φ : Type} (r : Φ → Q.Instr) (K : CoherentRegionModel J Q)
    (supported : Supported pe K) : Supported pe (K.reduct (pullHom Q r)) where
  typing := fun d e => by
    have left := denote_relabel_proof r K.types K.instructions d
    have right := denote_relabel_proof r K.types K.instructions e
    exact left.trans ((supported.typing (relabelIter d) (relabelIter e)).trans right.symm)
  shared := supported.shared
  pure := fun x pure => supported.pure (r x) pure

omit [FreydCategory.CentralUnit J] in
/-- The reduct of a supported model along a relabelling is supported. -/
theorem supported_reduct_proof (f : P ⟶ Q) :
    ∀ K : CoherentRegionModel J Q, Supported pe K → Supported pe (K.reduct f) :=
  instrSig_hom_cases_proof (Q := Q)
    (fun {_} f => ∀ K : CoherentRegionModel J Q, Supported pe K → Supported pe (K.reduct f))
    (fun r K supported => supported_reduct_pulled r K supported) f

/-- The model reduct of the existing ranked corridor at a relabelling is
the fixed-type reduct. -/
theorem corridor_reduct_proof (f : P ⟶ Q) (K : CoherentRegionModel J Q) :
    (ssaSignatureCorridor (J := J) f.toSignatureMap).mod.obj (ShrinkHoms.toShrinkHoms (Discrete.mk K)) =
      ShrinkHoms.toShrinkHoms (Discrete.mk (K.reduct f)) := by
  rw [ssaSignatureCorridor_primitive_mod]
  rfl

theorem sat_reduct_proof (f : P ⟶ Q) (K : CoherentRegionModel J Q) (e : RankedEquation P) :
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J Q).Sat
        (ShrinkHoms.toShrinkHoms (Discrete.mk K)) (mapRanked f.toSignatureMap e) ↔
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J P).Sat
        (ShrinkHoms.toShrinkHoms (Discrete.mk (K.reduct f))) e := by
  exact (sat_mapRanked (J := J) f.toSignatureMap (ShrinkHoms.toShrinkHoms (Discrete.mk K)) e).trans
    (Iff.of_eq (congrArg (fun N => (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J P).Sat N e)
      (corridor_reduct_proof f K)))

private instance (pe : ε) (P : InstrSig τ ε) : IsDiscrete (supportedRankedRoom J pe P).Mod where
  subsingleton _ _ :=
    (ShrinkHoms.inverse.{0} (Discrete (SupportedModel J pe P))).map_injective.subsingleton
  eq_of_hom f :=
    congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk)
      (Discrete.eq_of_hom ((ShrinkHoms.inverse.{0} (Discrete (SupportedModel J pe P))).map f))

theorem supportedFunctor_ext_proof {D : Type*} [Category* D]
    {F G : (supportedRankedRoom J pe P).Mod ⥤ D} (h : ∀ N, F.obj N = G.obj N) : F = G := by
  refine Functor.ext_of_iso (NatIso.ofComponents (fun N => eqToIso (h N)) ?_) h (fun _ => rfl)
  intro N L f
  obtain rfl := obj_ext_of_isDiscrete f
  have hf : f = 𝟙 N := Subsingleton.elim _ _
  subst f
  simp

theorem supportedReduct_id_proof (P : InstrSig τ ε)
    (closed : ∀ N : SupportedModel J pe P, Supported pe (N.1.reduct (𝟙 P))) :
    supportedReductOf J pe (𝟙 P) closed = 𝟭 _ :=
  supportedFunctor_ext_proof fun N => congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk)
    (Subtype.ext (CoherentRegionModel.reduct_id N.fromShrinkHoms.as.1))

theorem supportedReduct_comp_proof (f : P ⟶ Q) (g : Q ⟶ S)
    (closedF : ∀ N : SupportedModel J pe Q, Supported pe (N.1.reduct f))
    (closedG : ∀ N : SupportedModel J pe S, Supported pe (N.1.reduct g))
    (closed : ∀ N : SupportedModel J pe S, Supported pe (N.1.reduct (f ≫ g))) :
    supportedReductOf J pe (f ≫ g) closed =
      supportedReductOf J pe g closedG ⋙ supportedReductOf J pe f closedF :=
  supportedFunctor_ext_proof fun N => congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk)
    (Subtype.ext (CoherentRegionModel.reduct_comp f g N.fromShrinkHoms.as.1))

theorem supported_square_mod_proof (f : P ⟶ Q)
    (closed : ∀ N : SupportedModel J pe Q, Supported pe (N.1.reduct f)) :
    (includeSupported J pe Q).mod ⋙ (ssaSignatureCorridor (J := J) f.toSignatureMap).mod =
      supportedReductOf J pe f closed ⋙ (includeSupported J pe P).mod :=
  supportedFunctor_ext_proof fun N => corridor_reduct_proof f N.fromShrinkHoms.as.1

end Law

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
