module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Reduct.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Renaming.Category.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.SupportedReduct

/-! # Supported models are closed under relabelling reducts

A relabelling of instruction signatures keeps source types, target types
and effects. The existing reduct of a model of the ranked room along a
relabelling keeps the type interpretation and reads each primitive through
the map. The reduct of a supported model is supported:

* expression typing coherence transports because the arrow of a derivation
  in the reduct is the arrow of the relabelled derivation in the original
  model, and two derivations of one term relabel to two derivations of one
  term;
* the shared tensor is a property of the functor alone;
* a pure primitive is sent to a pure primitive, with the same arrow.

The ranked room restricted to supported models is therefore functorial in
relabellings, and the restriction commutes with the existing ranked
signature corridor.

Relabellings need not be injective here. Signature maps that translate
types are treated separately.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CoherentRegionModel restrictInstructions ssaSignatureCorridor)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation mapRanked mapRanked_id mapRanked_comp
  rankedSignatureCorridor)
open LetIter.Semantics.Categorical (TypeModel InstructionModel denote)
open LetIter.LocallyNameless (Derivation)

variable {τ ε : Type}

/-- Every relabelling is the instruction map of a pulled-back signature. A
property of relabellings holds when it holds for those. -/
theorem instrSig_hom_cases {Q : InstrSig τ ε}
    (motive : ∀ {P : InstrSig τ ε}, (P ⟶ Q) → Prop)
    (pulled : ∀ {Φ : Type} (r : Φ → Q.Instr), motive (pullHom Q r))
    {P : InstrSig τ ε} (f : P ⟶ Q) : motive f :=
  instrSig_hom_cases_proof motive pulled f

variable [TypeFormers τ]
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]

/-- The arrow of a derivation in the reduct interpretation is the arrow of
the relabelled derivation in the original interpretation. -/
theorem denote_relabel {Q : InstrSig τ ε} {Φ : Type} (r : Φ → Q.Instr) (M : TypeModel τ V)
    (I : InstructionModel J M Q.Instr) {ν : Type} [DecidableEq ν] {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : LetIter.LocallyNameless.Tm ν Φ n} {A : τ} (d : Derivation (pullSig Q r).Instr Γ β t A) :
    (letI := restrictInstructions (pullHom Q r) I; denote J M d) = (letI := I; denote J M (relabelIter d)) :=
  denote_relabel_proof r M I d

variable [FreydCategory.CentralUnit J] {P Q S : InstrSig τ ε} {pe : ε}

/-! ## The model law -/

omit [FreydCategory.CentralUnit J] in
/-- The reduct of a supported model along a relabelling is supported. -/
theorem supported_reduct (f : P ⟶ Q) (K : CoherentRegionModel J Q) (supported : Supported pe K) :
    Supported pe (K.reduct f) :=
  supported_reduct_proof f K supported

/-- The model reduct of the existing ranked signature corridor, at a
relabelling, is the fixed-type reduct. -/
theorem corridor_reduct (f : P ⟶ Q) (K : CoherentRegionModel J Q) :
    (ssaSignatureCorridor (J := J) f.toSignatureMap).mod.obj (ShrinkHoms.toShrinkHoms (Discrete.mk K)) =
      ShrinkHoms.toShrinkHoms (Discrete.mk (K.reduct f)) :=
  corridor_reduct_proof f K

/-- The satisfaction condition of the ranked room at a relabelling, with
the reduct written out. -/
theorem sat_reduct (f : P ⟶ Q) (K : CoherentRegionModel J Q) (e : RankedEquation P) :
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J Q).Sat
        (ShrinkHoms.toShrinkHoms (Discrete.mk K)) (mapRanked f.toSignatureMap e) ↔
      (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J P).Sat
        (ShrinkHoms.toShrinkHoms (Discrete.mk (K.reduct f))) e :=
  sat_reduct_proof f K e

/-! ## The restricted room is functorial -/

/-- Reduct of supported models along a relabelling. -/
noncomputable def supportedReduct (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
    (pe : ε) (f : P ⟶ Q) : (supportedRankedRoom J pe Q).Mod ⥤ (supportedRankedRoom J pe P).Mod :=
  supportedReductOf J pe f fun N => supported_reduct f N.1 N.2

/-- A relabelling as a corridor of the restricted rooms. Sentences move by
the existing ranked signature map and models by the reduct. -/
noncomputable def supportedCorridor (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
    (pe : ε) (f : P ⟶ Q) : supportedRankedRoom J pe P ⟶ supportedRankedRoom J pe Q where
  sen := mapRanked f.toSignatureMap
  mod := supportedReduct J pe f
  sat N e := sat_reduct f N.fromShrinkHoms.as.1 e

theorem supportedCorridor_id (P : InstrSig τ ε) :
    supportedCorridor J pe (𝟙 P) = 𝟙 (supportedRankedRoom J pe P) :=
  Room.hom_ext (funext mapRanked_id) (supportedReduct_id_proof P _)

theorem supportedCorridor_comp (f : P ⟶ Q) (g : Q ⟶ S) :
    supportedCorridor J pe (f ≫ g) = supportedCorridor J pe f ≫ supportedCorridor J pe g :=
  Room.hom_ext (funext (mapRanked_comp f.toSignatureMap g.toSignatureMap))
    (supportedReduct_comp_proof f g _ _ _)

/-- Ranked sentences over supported models, as a functor from
relabellings to rooms. -/
noncomputable def supportedRankedInst (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
    (pe : ε) : InstrSig τ ε ⥤ Room.{0, 0, 1} where
  obj := supportedRankedRoom J pe
  map f := supportedCorridor J pe f
  map_id := supportedCorridor_id
  map_comp := supportedCorridor_comp

/-- The restriction commutes with the existing ranked signature corridor:
translating a sentence and restricting models is restricting models and
translating the sentence, on sentences and on models. -/
theorem supported_square (f : P ⟶ Q) :
    rankedSignatureCorridor (J := J) f.toSignatureMap ≫ includeSupported J pe Q =
      includeSupported J pe P ≫ supportedCorridor J pe f :=
  Room.hom_ext rfl (supported_square_mod_proof f _)

/-! ## Validity -/

/-- Validity in the supported models is preserved by every relabelling,
with the existing ranked signature map. -/
theorem rankedValid_mapRanked (f : P ⟶ Q) (e : RankedEquation P) (valid : RankedValid pe e) :
    RankedValid pe (mapRanked f.toSignatureMap e) := by
  intro V C vcat ccat cart sym prem symPrem sumV sumC distV distC iter elgot J freyd central K supported
  exact (sat_reduct f K e).mpr (valid J (K.reduct f) (supported_reduct f K supported))

/-! ## Over the category of structural signatures -/

/-- Structural signatures and injective renamings, as instruction
signatures and relabellings. -/
def structuralInstrSig : StructuralSig ⥤ InstrSig (Ty Empty) Bool where
  obj X := sig X.Instr
  map f := f.hom

/-- Ranked sentences over supported categorical models, over the category
of structural signatures of the handled-trace institutions. -/
noncomputable def supportedStructuralInst (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : StructuralSig ⥤ Room.{0, 0, 1} :=
  structuralInstrSig ⋙ supportedRankedInst J false

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
