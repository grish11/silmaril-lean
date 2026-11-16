module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Core.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory Uflia.SExpr
variable {E F G H : Environment}

/-- Canonical spelling has the same admission as an admitted source sort atom. -/
theorem sortExpr_of_sort (expression : Expr) (sort : SortCode String)
    (h : E.sort? expression = some sort) : sortExpr sort = expression := by
  cases expression with
  | list es => simp [Environment.sort?] at h
  | atom name =>
    by_cases hb : name = "Bool"
    · subst name
      simp only [Environment.sort?] at h
      cases h
      rfl
    · by_cases hi : name = "Int"
      · subst name
        simp only [Environment.sort?] at h
        cases h
        rfl
      · have parsed : (if simpleSymbol name && E.sorts.contains name then
            some (SortCode.user name) else none) = some sort := by
          simpa only [Environment.sort?, hb, hi] using h
        split at parsed
        · cases parsed
          rfl
        · contradiction

theorem sortExpr_admitted (expression : Expr) (sort : SortCode String)
    (h : E.sort? expression = some sort) : E.sort? (sortExpr sort) = some sort := by
  rw [sortExpr_of_sort expression sort h]
  exact h

namespace NameMap
@[ext] theorem ext (f g : NameMap E F) (h : f.toNameMap = g.toNameMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (E : Environment) : NameMap E E where
  toNameMap := SortMaps.SExpr.Renaming.NameMap.id E
  sorts expression sort h := sortExpr_admitted expression sort h

def comp (f : NameMap E F) (g : NameMap F G) : NameMap E G where
  toNameMap := f.toNameMap.comp g.toNameMap
  sorts expression sort h := g.sorts _ _ (f.sorts expression sort h)

@[simp] theorem id_comp (f : NameMap E F) : (id E).comp f = f := by
  apply ext
  exact SortMaps.SExpr.Renaming.NameMap.id_comp f.toNameMap

@[simp] theorem comp_id (f : NameMap E F) : f.comp (id F) = f := by
  apply ext
  exact SortMaps.SExpr.Renaming.NameMap.comp_id f.toNameMap

theorem assoc (f : NameMap E F) (g : NameMap F G) (h : NameMap G H) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply ext
  exact SortMaps.SExpr.Renaming.NameMap.assoc f.toNameMap g.toNameMap h.toNameMap
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

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
