module

public import Silmaril.Semantics.ITree.Signature.Trace.Defs
public import Mathlib.CategoryTheory.Widesubcategory

@[expose] public section

namespace Silmaril.Elgot.ITree

open CategoryTheory

universe u

namespace Signature

/-- Only the complete request key must be preserved injectively. Each
backward reply map is an arbitrary typed function. -/
def injectiveRequests : MorphismProperty Signature.{u} :=
  fun _ _ f => Function.Injective f.request

instance : injectiveRequests.{u}.IsMultiplicative where
  id_mem _ := Function.injective_id
  comp_mem _ _ hf hg := hg.comp hf

/-- All ITree signatures, with arrows restricted to injective request maps. -/
abbrev InjectiveRequests := WideSubcategory injectiveRequests.{u}

end Signature

namespace TraceSignature

/-- The existing bijective-reply arrows are included without changing their
underlying signature maps. -/
def includeInjectiveRequests : TraceSignature.{u} ⥤ Signature.InjectiveRequests.{u} where
  obj S := ⟨S.toSignature⟩
  map f := ⟨f.hom, f.request_injective⟩

instance : includeInjectiveRequests.{u}.Faithful where
  map_injective {X Y f g} same := by
    have underlying : f.hom = g.hom :=
      congrArg (fun (h : includeInjectiveRequests.obj X ⟶ includeInjectiveRequests.obj Y) => h.hom) same
    cases f
    cases g
    cases underlying
    rfl

end TraceSignature

end Silmaril.Elgot.ITree
