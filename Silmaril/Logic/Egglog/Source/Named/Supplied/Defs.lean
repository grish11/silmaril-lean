module

public import Silmaril.Logic.Egglog.Source.Named.Family.Thms
public import Silmaril.Logic.Egglog.Source.Named.Representation.Local.Thms

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named
open CategoryTheory Silmaril.Logic.Institution.Examples

/-- Actual local signature maps preserving the source spellings. Targets may
contain additional declarations. No condition is imposed on ambient naming. -/
structure DeclarationHom (D E : Declarations) where
  symbols : D.signature ⟶ E.signature
  sort_name : ∀ s, (symbols.sorts s).val = s.val
  constructor_name : ∀ {n w s} (o : D.signature.Op n w s),
    (symbols.ops o).val.name = o.val.name
  relation_name : ∀ {n w} (r : D.signature.Rel n w),
    (symbols.rels r).val.name = r.val.name
  function_name : ∀ {n w s} (f : D.signature.Function n w s),
    (symbols.functions f).val.name = f.val.name

/-- Erasure with explicit variable spellings is independent of context sorts. -/
def eraseTermAt {D : Declarations} {k : Nat} {profile : Fin k → D.LocalSort}
    (names : Fin k → String) :
    {s : D.LocalSort} → EQ.Term D.signature.toSignature profile s → RawTerm
  | _, .var i => .var (names i)
  | _, .app o arguments => .app o.val.name _ (fun i => eraseTermAt names (arguments i))

def eraseAtomAt {D : Declarations} {k : Nat} {profile : Fin k → D.LocalSort}
    (names : Fin k → String) : Core.Atom D.signature profile → RawAtom
  | .equal e => .equal (eraseTermAt names e.lhs) (eraseTermAt names e.rhs)
  | .relation r arguments => .relation r.val.name _ (fun i => eraseTermAt names (arguments i))
  | .row f arguments value => .row f.val.name _
      (fun i => eraseTermAt names (arguments i)) (eraseTermAt names value)

namespace DeclarationHom

def mapContext {D E : Declarations} (f : DeclarationHom D E)
    (Γ : CheckedContext D) : CheckedContext E where
  bindings := Γ.bindings
  unique := Γ.unique
  declared i := by
    have member := (f.symbols.sorts (Γ.profile i)).property
    change (Γ.profile i).val ∈ E.data.sorts
    exact (congrArg (fun name => name ∈ E.data.sorts)
      (f.sort_name (Γ.profile i))).mp member

theorem mapContext_profile {D E : Declarations} (f : DeclarationHom D E)
    (Γ : CheckedContext D) : (f.mapContext Γ).profile = f.symbols.sorts ∘ Γ.profile := by
  funext i
  exact Subtype.ext (f.sort_name (Γ.profile i)).symm
end DeclarationHom

@[ext] theorem DeclarationHom.ext {D E : Declarations} (f g : DeclarationHom D E)
    (same : f.symbols = g.symbols) : f = g := by
  cases f
  cases g
  cases same
  rfl

instance : Category Declarations where
  Hom := DeclarationHom
  id D :=
    { symbols := 𝟙 D.signature
      sort_name := fun _ => rfl
      constructor_name := fun _ => rfl
      relation_name := fun _ => rfl
      function_name := fun _ => rfl }
  comp f g :=
    { symbols := f.symbols ≫ g.symbols
      sort_name := fun s => (g.sort_name _).trans (f.sort_name s)
      constructor_name := fun o => (g.constructor_name _).trans (f.constructor_name o)
      relation_name := fun r => (g.relation_name _).trans (f.relation_name r)
      function_name := fun t => (g.function_name _).trans (f.function_name t) }
  id_comp _ := DeclarationHom.ext _ _ rfl
  comp_id _ := DeclarationHom.ext _ _ rfl
  assoc _ _ _ := DeclarationHom.ext _ _ rfl

/-- A supplied vocabulary names finite support in an arbitrary ambient signature. -/
structure SuppliedSignature where
  ambient : Core.Signature
  names : NameView ambient

/-- The local map preserves source spellings and the actual interpretation square
commutes. Resolver naturality is a theorem, never part of this structure. -/
structure SuppliedSignature.Hom (S T : SuppliedSignature) where
  ambient : S.ambient ⟶ T.ambient
  vocabulary : S.names.declarations ⟶ T.names.declarations
  commutes : vocabulary.symbols ≫ T.names.symbols = S.names.symbols ≫ ambient

@[ext] theorem SuppliedSignature.Hom.ext {S T : SuppliedSignature}
    (f g : SuppliedSignature.Hom S T) (ambient : f.ambient = g.ambient)
    (vocabulary : f.vocabulary = g.vocabulary) : f = g := by
  cases f
  cases g
  cases ambient
  cases vocabulary
  rfl

instance : Category SuppliedSignature where
  Hom := SuppliedSignature.Hom
  id S :=
    { ambient := 𝟙 S.ambient
      vocabulary := 𝟙 S.names.declarations
      commutes := rfl }
  comp f g :=
    { ambient := f.ambient ≫ g.ambient
      vocabulary := f.vocabulary ≫ g.vocabulary
      commutes := by
        change (f.vocabulary.symbols ≫ g.vocabulary.symbols) ≫ _ = _ ≫ (f.ambient ≫ g.ambient)
        rw [Category.assoc, g.commutes, ← Category.assoc, f.commutes, Category.assoc] }
  id_comp _ := SuppliedSignature.Hom.ext _ _ rfl (DeclarationHom.ext _ _ rfl)
  comp_id _ := SuppliedSignature.Hom.ext _ _ rfl (DeclarationHom.ext _ _ rfl)
  assoc _ _ _ := SuppliedSignature.Hom.ext _ _ rfl (DeclarationHom.ext _ _ rfl)

end Silmaril.Logic.Egglog.Source.Named
