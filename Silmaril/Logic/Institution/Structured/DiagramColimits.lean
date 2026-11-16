module

public import Silmaril.Logic.Institution.Structured.DiagramInitial
public import Silmaril.Logic.Institution.Structured.DiagramCoproducts
public import Silmaril.Logic.Institution.Structured.DiagramPushouts
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

@[expose] public section
namespace Silmaril.Logic.Institution.CoDiagram
open CategoryTheory CategoryTheory.Limits
universe u w x
variable {C : Type w} [Category.{x} C]

/-- Small colimits of varying-shape diagrams exist whenever their values have
small colimits (Durán–Meseguer 1999, Theorem 3.3). -/
instance hasColimits [HasColimitsOfSize.{u,u} C] :
    HasColimitsOfSize.{u,u} (CoDiagram.{u,u} C) := by
  have : HasInitial (CoDiagram.{u,u} C) := (emptyIsInitial C).hasInitial
  have : HasBinaryCoproducts (CoDiagram.{u,u} C) :=
    hasBinaryCoproducts_of_hasInitial_and_pushouts (CoDiagram.{u,u} C)
  have : HasCoequalizers (CoDiagram.{u,u} C) :=
    hasCoequalizers_of_hasPushouts_and_binary_coproducts
  exact has_colimits_of_hasCoequalizers_and_coproducts

end Silmaril.Logic.Institution.CoDiagram
