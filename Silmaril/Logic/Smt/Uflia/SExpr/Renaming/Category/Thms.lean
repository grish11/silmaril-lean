module

public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Category.Defs

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming

open CategoryTheory

variable {E F G : Environment}

@[simp] theorem NameMap.id_rename (E : Environment) (name : String) :
    (NameMap.id E).rename name = name := rfl

@[simp] theorem NameMap.id_abstract (E : Environment) :
    (NameMap.id E).abstract = 𝟙 E.signature := rfl

@[simp] theorem NameMap.comp_rename (f : NameMap E F) (g : NameMap F G)
    (name : String) :
    (f.comp g).rename name = g.rename (f.rename name) := rfl

@[simp] theorem NameMap.comp_abstract (f : NameMap E F) (g : NameMap F G) :
    (f.comp g).abstract = f.abstract ≫ g.abstract := rfl

/-- The two routes from checked prefixes to abstract signatures agree exactly. -/
theorem prefixAbstractFunctor_eq :
    prefixAbstractFunctor = prefixFunctor ⋙ environmentFunctor := rfl

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming
