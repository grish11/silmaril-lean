module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.TypeChange.Marked.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.SupportedReduct
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.MarkedSupported

/-! # Supported ranked rooms over marked type-changing signatures

The corridor of supported rooms along a type-changing signature map goes
from a source marker to its image under the effect map. Over signatures
with a chosen marker and morphisms that preserve it, these corridors have
identities and composites. Both laws come from the laws of the existing
ranked corridor, because the support of a model is a proposition.

The supported rooms are a functor from marked signatures to rooms. Forgetting
the marker and taking the existing ranked room is another functor, and the
inclusion of supported models is a natural transformation between them.

Nothing here reflects validity along a signature map.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room Inst)
open Morphism (SignatureMap)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (TypeSignature)
open Silmaril.Isotope.Institution.Acyclic.Captured (rankedSignatureCorridor)

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

/-! ## Laws of the supported corridor -/

/-- The supported corridor along the identity signature map is the identity. -/
theorem supportedTypeCorridor_id (pe : ε) (P : InstrSig τ ε) :
    supportedTypeCorridor (P := P) (Q := P) SignatureMap.id J pe = 𝟙 (supportedRankedRoom J pe P) :=
  supportedTypeCorridor_id_proof pe P

/-- The supported corridor along a composite is the composite of the
supported corridors. The second starts at the image of the marker. -/
theorem supportedTypeCorridor_comp (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
    (h : SignatureMap Q.Instr S.Instr υ κ δ ξ)
    [g.PreservesProducts] [g.PreservesSums] [h.PreservesProducts] [h.PreservesSums] (pe : ε) :
    supportedTypeCorridor (h.comp g) J pe =
      supportedTypeCorridor g J pe ≫ supportedTypeCorridor h J (g.eff pe) :=
  supportedTypeCorridor_comp_proof g h pe

/-! ## Marked signatures -/

/-- The supported corridor along a morphism of marked signatures. -/
noncomputable def supportedMarkedCorridor (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
    {X Y : MarkedSignature} (f : X ⟶ Y) :
    supportedRankedRoom J X.marker X.sig.prim ⟶ supportedRankedRoom J Y.marker Y.sig.prim :=
  f.marker ▸ supportedTypeCorridor f.hom.signatureMap J X.marker

/-- When the target marker is the image of the source marker by
definition, this is the corridor of a signature map. -/
theorem supportedMarkedCorridor_mk (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
    [g.PreservesProducts] [g.PreservesSums] (pe : ε) :
    supportedMarkedCorridor J (X := ⟨⟨τ, ε, P⟩, pe⟩) (Y := ⟨⟨υ, δ, Q⟩, g.eff pe⟩) ⟨⟨g⟩, rfl⟩ =
      supportedTypeCorridor g J pe :=
  rfl

theorem supportedMarkedCorridor_id (X : MarkedSignature) :
    supportedMarkedCorridor J (𝟙 X) = 𝟙 (supportedRankedRoom J X.marker X.sig.prim) :=
  supportedTypeCorridor_id X.marker X.sig.prim

private theorem marked_comp_aux (sigX sigY sigZ : TypeSignature) (mx : sigX.effects) (my : sigY.effects)
    (mz : sigZ.effects) (f : sigX ⟶ sigY) (hf : f.signatureMap.eff mx = my) (g : sigY ⟶ sigZ)
    (hg : g.signatureMap.eff my = mz) :
    supportedMarkedCorridor J (X := ⟨sigX, mx⟩) (Y := ⟨sigZ, mz⟩)
        (CategoryStruct.comp (X := (⟨sigX, mx⟩ : MarkedSignature)) (Y := ⟨sigY, my⟩) (Z := ⟨sigZ, mz⟩)
          (MarkedSignature.Hom.mk f hf) (MarkedSignature.Hom.mk g hg)) =
      supportedMarkedCorridor J (X := ⟨sigX, mx⟩) (Y := ⟨sigY, my⟩) (MarkedSignature.Hom.mk f hf) ≫
        supportedMarkedCorridor J (X := ⟨sigY, my⟩) (Y := ⟨sigZ, mz⟩) (MarkedSignature.Hom.mk g hg) := by
  subst hf
  subst hg
  exact supportedTypeCorridor_comp f.signatureMap g.signatureMap mx

theorem supportedMarkedCorridor_comp {X Y Z : MarkedSignature} (f : X ⟶ Y) (g : Y ⟶ Z) :
    supportedMarkedCorridor J (f ≫ g) = supportedMarkedCorridor J f ≫ supportedMarkedCorridor J g :=
  marked_comp_aux X.sig Y.sig Z.sig X.marker Y.marker Z.marker f.hom f.marker g.hom g.marker

/-- Ranked sentences over supported categorical models, as a functor from
marked type-changing signatures to rooms. -/
noncomputable def supportedMarkedInst (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J] :
    MarkedSignature ⥤ Room.{0, 0, 1} where
  obj X := supportedRankedRoom J X.marker X.sig.prim
  map f := supportedMarkedCorridor J f
  map_id := supportedMarkedCorridor_id
  map_comp := supportedMarkedCorridor_comp

/-- The bundled institution of ranked sentences over supported models. -/
noncomputable abbrev supportedMarkedInstitution (J : V ⥤ C) [StrongElgotFreydCategory J]
    [FreydCategory.CentralUnit J] : Inst.{1, 0, 0, 0, 1} :=
  ⟨MarkedSignature, supportedMarkedInst J⟩

/-! ## Comparison with the unrestricted room -/

private theorem marked_square_aux (sigX sigY : TypeSignature) (mx : sigX.effects) (my : sigY.effects)
    (f : sigX ⟶ sigY) (hf : f.signatureMap.eff mx = my) :
    rankedSignatureCorridor (J := J) f.signatureMap ≫ includeSupported J my sigY.prim =
      includeSupported J mx sigX.prim ≫
        supportedMarkedCorridor J (X := ⟨sigX, mx⟩) (Y := ⟨sigY, my⟩) (MarkedSignature.Hom.mk f hf) := by
  subst hf
  exact supported_typeChange_square f.signatureMap

/-- Restricting models commutes with the existing ranked signature
corridor at every morphism of marked signatures. -/
theorem supportedMarked_square {X Y : MarkedSignature} (f : X ⟶ Y) :
    rankedSignatureCorridor (J := J) f.hom.signatureMap ≫ includeSupported J Y.marker Y.sig.prim =
      includeSupported J X.marker X.sig.prim ≫ supportedMarkedCorridor J f :=
  marked_square_aux X.sig Y.sig X.marker Y.marker f.hom f.marker

/-- The inclusion of supported models is natural: the existing ranked
room over the underlying signature maps to the supported room, compatibly
with every morphism of marked signatures. -/
noncomputable def supportedComparison (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J] :
    MarkedSignature.forget ⋙ Silmaril.Isotope.Institution.Acyclic.Captured.rankedInst J ⟶
      supportedMarkedInst J where
  app X := includeSupported J X.marker X.sig.prim
  naturality _ _ f := supportedMarked_square f

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
