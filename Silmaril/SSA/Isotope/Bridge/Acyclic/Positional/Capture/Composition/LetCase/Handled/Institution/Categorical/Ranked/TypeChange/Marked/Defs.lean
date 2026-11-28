module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.TypeChange.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.TypeChange.Defs

/-! # Type-changing signatures with a chosen effect marker

A marked signature is one of the existing type-changing signatures with a
chosen effect. A morphism is an existing type-changing signature morphism
whose effect map sends the source marker to the target marker.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory
open Silmaril.Isotope.Institution.Acyclic (TypeSignature)

/-- A type-changing signature with a chosen effect marker. Primitives with
that effect are the ones treated as pure. -/
structure MarkedSignature where
  sig : TypeSignature
  marker : sig.effects

namespace MarkedSignature

/-- A type-changing signature morphism that preserves the marker. -/
structure Hom (X Y : MarkedSignature) where
  hom : X.sig ⟶ Y.sig
  marker : hom.signatureMap.eff X.marker = Y.marker

@[ext] theorem Hom.ext {X Y : MarkedSignature} {f g : Hom X Y} (same : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases same
  rfl

instance : Category.{0} MarkedSignature where
  Hom := Hom
  id X := ⟨𝟙 X.sig, rfl⟩
  comp f g := ⟨f.hom ≫ g.hom, (congrArg g.hom.signatureMap.eff f.marker).trans g.marker⟩
  id_comp f := Hom.ext (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.hom)
  assoc f g h := Hom.ext (Category.assoc f.hom g.hom h.hom)

/-- Forget the marker. -/
def forget : MarkedSignature ⥤ TypeSignature where
  obj X := X.sig
  map f := f.hom

end MarkedSignature

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
