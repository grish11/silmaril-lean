module

public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Thms

/-! Concrete declaration environments and checked prefixes with actual name-map
arrows. These categories retain the complete abstract operation maps; no profile
is reconstructed from equality of declaration indices. The existing discrete
institutions are independent of these signature categories. -/

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming

open CategoryTheory Silmaril.Logic.Algebraic

variable {E F G : Environment}

/-- Successful concrete lookup selects a declaration with the requested name. -/
theorem lookup_declaration_name (name : String) (i : Fin E.declarations.length)
    (h : lookup? E name = some i) : (E.declarations.get i).name = name := by
  unfold lookup? at h
  split at h
  · have selected : ((E.declarations.get i).name == name) = true :=
      List.find?_some (p := fun j : Fin E.declarations.length =>
        (E.declarations.get j).name == name) h
    exact beq_iff_eq.mp selected
  · cases h

namespace NameMap

/-- The computational fields determine a name map; coherence fields are proofs. -/
@[ext] theorem ext (f g : NameMap E F) (rename : f.rename = g.rename)
    (abstract : f.abstract = g.abstract) : f = g := by
  cases f
  cases g
  cases rename
  cases abstract
  rfl

/-- Identity acts on concrete names and the actual abstract signature. -/
def id (E : Environment) : NameMap E E where
  rename := fun name => name
  abstract := 𝟙 E.signature
  lookup _ _ h := h
  targetName name i h := lookup_declaration_name name i h

/-- Reconstruction transports the entire typed symbol before taking its index.
The heterogeneous equality retains arity, inputs and output simultaneously. -/
theorem symbolIndex_map (g : NameMap F G) {n : Nat}
    {inputs : Fin n → SortCode String} {output : SortCode String}
    (symbol : Symbol F n inputs output) :
    symbolIndex (g.abstract.operations (.declared (symbolIndex symbol))) =
      symbolIndex (g.abstract.operations symbol) := by
  cases symbol with
  | declared i =>
      exact congrArg (fun s => symbolIndex (g.abstract.operations s))
        (eq_of_heq (symbol_reconstruct (Symbol.declared i)))

/-- Compose concrete renaming and abstract operation maps in the same order. -/
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

/-- A raw concrete signature retains an explicit declaration environment. -/
structure EnvironmentSignature where
  environment : Environment

/-- A checked signature retains its actual successful declaration-prefix decode. -/
structure PrefixSignature where
  «prefix» : DeclarationPrefix

instance environmentSignatureCategory : Category EnvironmentSignature where
  Hom E F := NameMap E.environment F.environment
  id E := NameMap.id E.environment
  comp := NameMap.comp
  id_comp := NameMap.id_comp
  comp_id := NameMap.comp_id
  assoc := NameMap.assoc

instance prefixSignatureCategory : Category PrefixSignature where
  Hom E F := NameMap E.prefix.environment F.prefix.environment
  id E := NameMap.id E.prefix.environment
  comp := NameMap.comp
  id_comp := NameMap.id_comp
  comp_id := NameMap.comp_id
  assoc := NameMap.assoc

/-- Forget concrete names through each name map's actual abstract operation map. -/
def environmentFunctor : EnvironmentSignature ⥤ Uflia.Signature String where
  obj E := E.environment.signature
  map f := f.abstract
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forget checked-prefix evidence, retaining every concrete name-map arrow. -/
def prefixFunctor : PrefixSignature ⥤ EnvironmentSignature where
  obj E := ⟨E.prefix.environment⟩
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Checked prefixes also map to the actual abstract UF/LIA signature category. -/
def prefixAbstractFunctor : PrefixSignature ⥤ Uflia.Signature String :=
  prefixFunctor ⋙ environmentFunctor

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming
