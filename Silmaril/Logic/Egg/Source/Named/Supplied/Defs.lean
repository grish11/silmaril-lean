module

public import Silmaril.Logic.Egg.Source.Named.Family.Defs
public import Silmaril.Logic.Egg.Source.Named.Representation.Local.Thms
public import Silmaril.Logic.Egglog.Source.Named.Supplied.Defs

@[expose] public section
namespace Silmaril.Logic.Egg.Source.Named
open CategoryTheory Silmaril.Logic.Institution.Examples

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Reuse actual spelling-preserving maps of checked vocabularies. Empty
predicate/table declarations ensure these are precisely constructor maps. -/
abbrev DeclarationHom (D E : Declarations) :=
  Silmaril.Logic.Egglog.Source.Named.DeclarationHom D.checked E.checked

namespace DeclarationHom

def mapContext {D E : Declarations} (f : DeclarationHom D E)
    (Γ : CheckedContext D) : CheckedContext E := Silmaril.Logic.Egglog.Source.Named.DeclarationHom.mapContext f Γ

theorem mapContext_profile {D E : Declarations} (f : DeclarationHom D E)
    (Γ : CheckedContext D) : (mapContext f Γ).profile = f.symbols.sorts ∘ Γ.profile :=
  Silmaril.Logic.Egglog.Source.Named.DeclarationHom.mapContext_profile f Γ
def identity (D : Declarations) : DeclarationHom D D where
  symbols := 𝟙 D.checked.signature
  sort_name := fun _ => rfl
  constructor_name := fun _ => rfl
  relation_name := fun _ => rfl
  function_name := fun _ => rfl

def compose {D E F : Declarations} (f : DeclarationHom D E) (g : DeclarationHom E F) :
    DeclarationHom D F where
  symbols := f.symbols ≫ g.symbols
  sort_name := fun s => (g.sort_name _).trans (f.sort_name s)
  constructor_name := fun o => (g.constructor_name _).trans (f.constructor_name o)
  relation_name := fun r => (g.relation_name _).trans (f.relation_name r)
  function_name := fun t => (g.function_name _).trans (f.function_name t)

end DeclarationHom

/-- Variable names are retained independently of the sorted context. Result
annotations follow the actual output sort of each constructor occurrence. -/
def eraseTermAt {D : Declarations} {k : Nat} {profile : Fin k → D.checked.LocalSort}
    (names : Fin k → String) : {s : D.checked.LocalSort} →
      EQ.Term D.signature profile s → RawTerm
  | _, .var i => .var (names i)
  | s, .app o arguments => .app o.val.name s.val _
      (fun i => eraseTermAt names (arguments i))

def eraseEqualityAt {D : Declarations} {k : Nat} {profile : Fin k → D.checked.LocalSort}
    (names : Fin k → String) (e : Core.Equality D.signature profile) : RawEquality :=
  ⟨eraseTermAt names e.lhs, eraseTermAt names e.rhs⟩

/-- A supplied finite vocabulary has an actual interpretation in an arbitrary
ambient signature. No global enumeration or name oracle is required. -/
structure SuppliedSignature where
  ambient : Core.Signature
  declarations : Declarations
  symbols : declarations.signature ⟶ ambient

structure SuppliedSignature.Hom (S T : SuppliedSignature) where
  ambient : S.ambient ⟶ T.ambient
  vocabulary : DeclarationHom S.declarations T.declarations
  commutes : vocabulary.symbols.toHom ≫ T.symbols = S.symbols ≫ ambient

@[ext] theorem SuppliedSignature.Hom.ext {S T : SuppliedSignature}
    (f g : SuppliedSignature.Hom S T) (ambient : f.ambient = g.ambient)
    (vocabulary : f.vocabulary = g.vocabulary) : f = g := by
  cases f
  cases g
  cases ambient
  cases vocabulary
  rfl

namespace SuppliedSignature.Hom

def identity (S : SuppliedSignature) : Hom S S where
  ambient := 𝟙 S.ambient
  vocabulary := DeclarationHom.identity S.declarations
  commutes := rfl

def compose {S T U : SuppliedSignature} (f : Hom S T) (g : Hom T U) : Hom S U where
  ambient := f.ambient ≫ g.ambient
  vocabulary := DeclarationHom.compose f.vocabulary g.vocabulary
  commutes := by
    change ((f.vocabulary.symbols.toHom : S.declarations.signature ⟶ T.declarations.signature) ≫
      (g.vocabulary.symbols.toHom : T.declarations.signature ⟶ U.declarations.signature)) ≫
      U.symbols = S.symbols ≫ (f.ambient ≫ g.ambient)
    rw [Category.assoc, g.commutes, ← Category.assoc, f.commutes, Category.assoc]
theorem identity_comp {S T : SuppliedSignature} (f : Hom S T) : compose (identity S) f = f := by
  apply SuppliedSignature.Hom.ext
  · rfl
  · exact Silmaril.Logic.Egglog.Source.Named.DeclarationHom.ext _ _ rfl

theorem comp_identity {S T : SuppliedSignature} (f : Hom S T) : compose f (identity T) = f := by
  apply SuppliedSignature.Hom.ext
  · rfl
  · exact Silmaril.Logic.Egglog.Source.Named.DeclarationHom.ext _ _ rfl

theorem compose_assoc {R S T U : SuppliedSignature} (f : Hom R S) (g : Hom S T) (h : Hom T U) :
    compose (compose f g) h = compose f (compose g h) := by
  apply SuppliedSignature.Hom.ext
  · rfl
  · exact Silmaril.Logic.Egglog.Source.Named.DeclarationHom.ext _ _ rfl
end SuppliedSignature.Hom

instance : Category SuppliedSignature where
  Hom := SuppliedSignature.Hom
  id := SuppliedSignature.Hom.identity
  comp := SuppliedSignature.Hom.compose
  id_comp := SuppliedSignature.Hom.identity_comp
  comp_id := SuppliedSignature.Hom.comp_identity
  assoc := SuppliedSignature.Hom.compose_assoc

end Silmaril.Logic.Egg.Source.Named
