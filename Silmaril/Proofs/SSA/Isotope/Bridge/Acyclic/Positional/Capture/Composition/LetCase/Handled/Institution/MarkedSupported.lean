module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.TypeChange.Marked.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.SupportedReduct

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room)
open Morphism (SignatureMap)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CoherentRegionModel ssaRoom ssaSignatureCorridor ssaSignatureCorridor_id
  ssaSignatureCorridor_comp)
open Silmaril.Isotope.Institution.Acyclic.Captured (mapRanked mapRanked_id mapRanked_comp)

variable {τ υ κ ε δ ξ : Type} [TypeFormers τ] [TypeFormers υ] [TypeFormers κ]
  {P : InstrSig τ ε} {Q : InstrSig υ δ} {S : InstrSig κ ξ}
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] {J : V ⥤ C} [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

/-- The identity law, from the identity law of the existing corridor. The
support proofs are propositions and play no part. -/
theorem supportedTypeCorridor_id_proof (pe : ε) (P : InstrSig τ ε) :
    supportedTypeCorridor (P := P) (Q := P) SignatureMap.id J pe = 𝟙 (supportedRankedRoom J pe P) := by
  refine Room.hom_ext (funext mapRanked_id) (supportedFunctor_ext_proof fun N => ?_)
  have law := congrArg
    (fun c : ssaRoom J P ⟶ ssaRoom J P =>
      c.mod.obj (ShrinkHoms.toShrinkHoms (Discrete.mk N.fromShrinkHoms.as.1)))
    (ssaSignatureCorridor_id (J := J) (P := P))
  exact congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk)
    (Subtype.ext (congrArg (fun M : (ssaRoom J P).Mod => M.fromShrinkHoms.as) law))

/-- The composition law, from the composition law of the existing corridor. -/
theorem supportedTypeCorridor_comp_proof (g : SignatureMap P.Instr Q.Instr τ υ ε δ)
    (h : SignatureMap Q.Instr S.Instr υ κ δ ξ)
    [g.PreservesProducts] [g.PreservesSums] [h.PreservesProducts] [h.PreservesSums] (pe : ε) :
    supportedTypeCorridor (h.comp g) J pe =
      supportedTypeCorridor g J pe ≫ supportedTypeCorridor h J (g.eff pe) := by
  refine Room.hom_ext (funext (mapRanked_comp g h)) (supportedFunctor_ext_proof fun N => ?_)
  have law := congrArg
    (fun c : ssaRoom J P ⟶ ssaRoom J S =>
      c.mod.obj (ShrinkHoms.toShrinkHoms (Discrete.mk N.fromShrinkHoms.as.1)))
    (ssaSignatureCorridor_comp (J := J) g h)
  exact congrArg (ShrinkHoms.toShrinkHoms ∘ Discrete.mk)
    (Subtype.ext (congrArg (fun M : (ssaRoom J P).Mod => M.fromShrinkHoms.as) law))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
