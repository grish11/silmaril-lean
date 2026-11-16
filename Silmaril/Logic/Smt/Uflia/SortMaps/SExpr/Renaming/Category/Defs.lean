module

public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Core.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Category.Thms

/-! Declaration environments and checked prefixes with coherent concrete names
and genuine varying-sort arrows. These categories do not assume that decoding
commutes with source normalization. -/

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Algebraic
open Uflia.SExpr
variable {E F G : Environment}

namespace NameMap

@[ext] theorem ext (f g : NameMap E F) (rename : f.rename = g.rename)
    (abstract : f.abstract = g.abstract) : f = g := by
  cases f
  cases g
  cases rename
  cases abstract
  rfl

def id (E : Environment) : NameMap E E where
  rename := fun name => name
  abstract := 𝟙 (environmentSignature E)
  lookup _ _ h := h
  targetName name i h := Uflia.SExpr.Renaming.lookup_declaration_name name i h

/-- Reconstructing a declared symbol retains its full dependent profile before
the second map selects its actual target declaration. -/
theorem symbolIndex_map (g : NameMap F G) {n : Nat}
    {inputs : Fin n → SortCode String} {output : SortCode String}
    (symbol : Symbol F n inputs output) :
    Uflia.SExpr.Renaming.symbolIndex
      (g.abstract.operations (.declared (Uflia.SExpr.Renaming.symbolIndex symbol))) =
    Uflia.SExpr.Renaming.symbolIndex (g.abstract.operations symbol) := by
  cases symbol with
  | declared i => rfl

def comp (f : NameMap E F) (g : NameMap F G) : NameMap E G where
  rename := fun name => g.rename (f.rename name)
  abstract := f.abstract ≫ g.abstract
  lookup name i h := by
    have selected := f.lookup name i h
    have mapped := g.lookup (f.rename name) _ selected
    rw [symbolIndex_map g (f.abstract.operations (.declared i))] at mapped
    exact mapped
  targetName name i h := by
    have selected := f.lookup name i h
    have named := g.targetName (f.rename name) _ selected
    rw [symbolIndex_map g (f.abstract.operations (.declared i))] at named
    exact named

@[simp] theorem id_comp (f : NameMap E F) : (id E).comp f = f :=
  ext _ _ rfl (Category.id_comp f.abstract)

@[simp] theorem comp_id (f : NameMap E F) : f.comp (id F) = f :=
  ext _ _ rfl (Category.comp_id f.abstract)

theorem assoc {H : Environment} (f : NameMap E F) (g : NameMap F G)
    (h : NameMap G H) : (f.comp g).comp h = f.comp (g.comp h) :=
  ext _ _ rfl (Category.assoc f.abstract g.abstract h.abstract)

end NameMap

structure EnvironmentSignature where
  environment : Environment

structure PrefixSignature where
  «prefix» : DeclarationPrefix

instance : Category EnvironmentSignature where
  Hom E F := NameMap E.environment F.environment
  id E := NameMap.id E.environment
  comp := NameMap.comp
  id_comp := NameMap.id_comp
  comp_id := NameMap.comp_id
  assoc := NameMap.assoc

instance : Category PrefixSignature where
  Hom E F := NameMap E.prefix.environment F.prefix.environment
  id E := NameMap.id E.prefix.environment
  comp := NameMap.comp
  id_comp := NameMap.id_comp
  comp_id := NameMap.comp_id
  assoc := NameMap.assoc

def environmentFunctor : EnvironmentSignature ⥤ SortMaps.Signature where
  obj E := environmentSignature E.environment
  map f := f.abstract
  map_id _ := rfl
  map_comp _ _ := rfl

def prefixFunctor : PrefixSignature ⥤ EnvironmentSignature where
  obj E := ⟨E.prefix.environment⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

def prefixAbstractFunctor : PrefixSignature ⥤ SortMaps.Signature :=
  prefixFunctor ⋙ environmentFunctor

end Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming
