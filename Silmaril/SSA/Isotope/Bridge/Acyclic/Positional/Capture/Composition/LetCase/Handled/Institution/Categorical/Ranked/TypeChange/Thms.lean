module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Reduct.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Pullback.Witness.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.SupportedReduct
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.SupportedPullback

/-! # Supported models are closed under type-changing pullbacks

The existing signature maps may translate types and effects, as long as
the type translation keeps products, unit, sums and empty. The existing
pullback of a model of the ranked room along such a map reinterprets each
source type by its image and transports the chosen isomorphisms.

The pullback of a supported model is supported. Every exact LetIter
derivation over the source signature, at the empty named context, has a
derivation of the translated term over the target signature with the same
arrow. Two derivations of one source term therefore give two derivations of
one target term, and coherent expression typing transports. The shared
tensor depends on the functor alone. A primitive that is pure at a source
marker is pure at the translated marker, and its value map transports
along the two type equations.

This is a law about model reducts. It does not reflect validity from the
target signature to the source signature.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room)
open Morphism (SignatureMap)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CoherentRegionModel pullbackTypes pullbackInstructions transportArrow
  RegionWitnessPullback regionWitnessPullback)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation mapRanked rankedSignatureCorridor)
open LetIter.Semantics.Categorical (TypeModel InstructionModel TypingCoherent denote)
open LetIter.LocallyNameless (Derivation)

variable {τ υ ε δ : Type} [TypeFormers τ] [TypeFormers υ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ}
  (g : SignatureMap P.Instr Q.Instr τ υ ε δ) [g.PreservesProducts] [g.PreservesSums]
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

/-! ## Transport of expression typing and purity -/

/-- A derivation over the source signature has a derivation of the
translated term over the target signature with the same arrow, read in the
pulled-back interpretation. Iteration is included. -/
theorem denote_pullback (M : TypeModel υ V) (I : InstructionModel J M Q.Instr) {n : Nat} {β : BoundCtx τ n}
    {t : LetIter.LocallyNameless.Tm Empty P.Instr n} {A : τ}
    (d : Derivation P.Instr (Ctx.nil : Ctx Empty τ) β t A) :
    ∃ d' : Derivation Q.Instr (Ctx.nil : Ctx Empty υ) (β.mapTypes g.ty) (t.mapInstr g.instr) (g.ty A),
      HEq (letI := pullbackInstructions g I; denote J (pullbackTypes g M) d) (letI := I; denote J M d') :=
  denote_pullback_proof g M I d

/-- Coherent expression typing transports to the pulled-back interpretation. -/
theorem typingCoherent_pullback (M : TypeModel υ V) (I : InstructionModel J M Q.Instr)
    (coherent : letI := I; TypingCoherent (ν := Empty) J M Q.Instr) :
    letI := pullbackInstructions g I
    TypingCoherent (ν := Empty) J (pullbackTypes g M) P.Instr :=
  typingCoherent_pullback_proof g M I coherent

variable [FreydCategory.CentralUnit J] {pe : ε}

/-! ## The model law -/

omit [FreydCategory.CentralUnit J] in
/-- The pullback of a supported model along a signature map is supported.
The source marker is one that the map sends to the target marker. -/
theorem supported_pullback (K : CoherentRegionModel J Q) (w : RegionWitnessPullback g K)
    (supported : Supported (g.eff pe) K) : Supported pe (K.pullbackOfWitness g w) :=
  supported_pullback_proof g K w supported

/-- The existing satisfaction condition of the ranked room along a
signature map, with the pullback written out. -/
theorem sat_pullback (K : CoherentRegionModel J Q) (e : RankedEquation P) :
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J Q).Sat
        (ShrinkHoms.toShrinkHoms (Discrete.mk K)) (mapRanked g e) ↔
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J P).Sat
        (ShrinkHoms.toShrinkHoms (Discrete.mk (K.pullbackOfWitness g (regionWitnessPullback g K)))) e :=
  sat_pullback_proof g K e

/-- Validity in the supported models is preserved by every signature map,
from a source marker to its image. -/
theorem rankedValid_mapRanked_typeChange (e : RankedEquation P) (valid : RankedValid pe e) :
    RankedValid (g.eff pe) (mapRanked g e) := by
  intro V C vcat ccat cart sym prem symPrem sumV sumC distV distC iter elgot J freyd central K supported
  exact (sat_pullback g K e).mpr
    (valid J _ (supported_pullback g K (regionWitnessPullback g K) supported))

/-! ## The restricted rooms -/

/-- Pullback of supported models along a signature map. -/
noncomputable def supportedPullback (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
    (pe : ε) : (supportedRankedRoom J (g.eff pe) Q).Mod ⥤ (supportedRankedRoom J pe P).Mod :=
  ShrinkHoms.inverse.{0} (Discrete (SupportedModel J (g.eff pe) Q)) ⋙
    Discrete.functor (fun N => Discrete.mk
      ⟨N.1.pullbackOfWitness g (regionWitnessPullback g N.1),
        supported_pullback g N.1 (regionWitnessPullback g N.1) N.2⟩) ⋙
    ShrinkHoms.functor.{0} (Discrete (SupportedModel J pe P))

/-- A signature map as a corridor of the restricted rooms. Sentences move
by the existing ranked signature map and models by the pullback. -/
noncomputable def supportedTypeCorridor (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
    (pe : ε) : supportedRankedRoom J pe P ⟶ supportedRankedRoom J (g.eff pe) Q where
  sen := mapRanked g
  mod := supportedPullback g J pe
  sat N e := sat_pullback g N.fromShrinkHoms.as.1 e

/-- Restricting models commutes with the existing ranked signature
corridor, on sentences and on models. -/
theorem supported_typeChange_square :
    rankedSignatureCorridor (J := J) g ≫ includeSupported J (g.eff pe) Q =
      includeSupported J pe P ≫ supportedTypeCorridor g J pe :=
  Room.hom_ext rfl (supportedFunctor_ext_proof fun _ => rfl)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
