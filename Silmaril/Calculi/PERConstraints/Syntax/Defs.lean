module

public import Mathlib.CategoryTheory.Types.Basic
public import Silmaril.Formats.PER.Defs

/-! A syntax is a carrier with total functions as its chosen maps. A pre-semantic
type adds a PER; its maps preserve relatedness, without having to reflect it. -/

@[expose] public section
namespace Silmaril.Calculi.PERConstraints

open CategoryTheory Silmaril.Formats

structure Syntax where
  Term : Type

@[ext] structure Syntax.Hom (source target : Syntax) where
  term : source.Term → target.Term

instance : Category Syntax where
  Hom := Syntax.Hom
  id _ := ⟨id⟩
  comp first second := ⟨second.term ∘ first.term⟩

/-- PERs on a fixed carrier, with total endofunctions as the underlying maps. -/
structure Fixed (α : Type) where
  per : PER α

/-- A total endofunction of the common syntax, not a map between supports. -/
@[ext] structure Fixed.Hom {α : Type} (source target : Fixed α) where
  term : α → α
  preserves : source.per.Sub (target.per.pull term)

instance (α : Type) : Category (Fixed α) where
  Hom := Fixed.Hom
  id _ := ⟨id, fun {_left _right} related => related⟩
  comp first second := ⟨second.term ∘ first.term,
    fun {_left _right} related => second.preserves (first.preserves related)⟩

/-- The total category allows the syntax carrier to vary. -/
structure SemanticType where
  signature : Syntax
  per : PER signature.Term

@[ext] structure SemanticType.Hom (source target : SemanticType) where
  syntaxMap : source.signature ⟶ target.signature
  preserves : source.per.Sub (target.per.pull syntaxMap.term)

instance : Category SemanticType where
  Hom := SemanticType.Hom
  id _ := ⟨𝟙 _, fun {_left _right} related => related⟩
  comp first second := ⟨first.syntaxMap ≫ second.syntaxMap,
    fun {_left _right} related => second.preserves (first.preserves related)⟩

def SemanticType.forgetSyntax : SemanticType ⥤ Syntax where
  obj model := model.signature
  map morphism := morphism.syntaxMap

/-- Include the fixed-carrier category in the total category. Maps need not
have identity underlying syntax map, so this is not the strict fiber. -/
def SemanticType.includeFixed (α : Type) : Fixed α ⥤ SemanticType where
  obj model := ⟨⟨α⟩, model.per⟩
  map morphism := ⟨⟨morphism.term⟩, morphism.preserves⟩

end Silmaril.Calculi.PERConstraints
