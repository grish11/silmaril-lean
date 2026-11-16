module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Raw

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
open CategoryTheory

/-- Total syntax action, preserving variable names/namespaces and all binder
structure. No alias expansion or parser/checker success is hidden here. -/
def raw (sortMap nameMap : String → String) (p : RawPattern) : RawPattern :=
  match p with
  | .evar name s => .evar name (sortMap s)
  | .svar name s => .svar name (sortMap s)
  | .domainValue s text => .domainValue (sortMap s) text
  | .app name args => .app (nameMap name) (args.attach.map (fun arg => raw sortMap nameMap arg.val))
  | .top s => .top (sortMap s)
  | .bottom s => .bottom (sortMap s)
  | .neg s p => .neg (sortMap s) (raw sortMap nameMap p)
  | .conj s p q => .conj (sortMap s) (raw sortMap nameMap p) (raw sortMap nameMap q)
  | .disj s p q => .disj (sortMap s) (raw sortMap nameMap p) (raw sortMap nameMap q)
  | .ex s name bound p => .ex (sortMap s) name (sortMap bound) (raw sortMap nameMap p)
  | .all s name bound p => .all (sortMap s) name (sortMap bound) (raw sortMap nameMap p)
  | .mu name s p => .mu name (sortMap s) (raw sortMap nameMap p)
  | .nu name s p => .nu name (sortMap s) (raw sortMap nameMap p)
termination_by sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals first | omega | have bound := List.sizeOf_lt_of_mem arg.property; omega

def declaration (sortMap nameMap : String → String) (d : Kore.Modules.SymbolDeclaration) :
    Kore.Modules.SymbolDeclaration :=
  ⟨nameMap d.name, d.arguments.map sortMap, sortMap d.result⟩

def symbol (sortMap nameMap : String → String) (d : Kore.Modules.NamedSymbol) :
    Kore.Modules.NamedSymbol := ⟨d.origin, declaration sortMap nameMap d.declaration⟩

def renameAlias (sortMap nameMap : String → String) (d : Alias) : Alias where
  symbol := declaration sortMap nameMap d.symbol
  parameters := d.parameters.map (fun p => { p with sort := sortMap p.sort })
  body := raw sortMap nameMap d.body
  moduleIndex := d.moduleIndex

structure Package where
  base : Signature
  aliases : List Alias

/-- A single independently checkable structural step. Every additional field
is about raw names, declaration identities, ordered lists or source metadata;
there is no successful-checker or semantic-satisfaction premise. -/
structure Step (A B : Package) where
  semantic : A.base ⟶ B.base
  names : String → String
  injective : Function.Injective names
  sortDeclarations : B.base.scope.sorts = A.base.scope.sorts.map
    (fun d => (d.1, semantic.native.sorts d.2))
  symbolDeclarations : B.base.scope.symbols =
    A.base.scope.symbols.map (symbol semantic.native.sorts names)
  /-- The old first-order scope metadata is not consulted by this builtin
  checker; actual general builtin aliases live in Package.aliases. -/
  legacyAliases : B.base.scope.aliases = A.base.scope.aliases
  aliasDeclarations : B.aliases = A.aliases.map (renameAlias semantic.native.sorts names)
  literalPrefix_eq : B.base.literalPrefix = A.base.literalPrefix
  literalDeclarations : B.base.literals = A.base.literals.map
    (fun b => ⟨symbol semantic.native.sorts names b.symbol, b.literal⟩)
  hookDeclarations : B.base.hooks = A.base.hooks.map
    (fun b => ⟨symbol semantic.native.sorts names b.symbol, b.hook⟩)
  literalNames : ∀ b ∈ A.base.literals,
    names b.symbol.declaration.name = b.symbol.declaration.name
  operations : ∀ {n inputs output} (op : A.base.scope.signature.operations n inputs output),
    (semantic.native.operations op).val = symbol semantic.native.sorts names op.val

/-- Paths form the free category of structural steps. Composition retains all
step certificates instead of assuming closure of an unchecked raw invariant. -/
inductive Path : Package → Package → Type where
  | nil (A) : Path A A
  | cons {A B C} : Step A B → Path B C → Path A C

namespace Path
variable {A B C D : Package}

def append {A B C : Package} : Path A B → Path B C → Path A C
  | .nil _, q => q
  | .cons s tail, q => .cons s (append tail q)

theorem append_nil (p : Path A B) : append p (.nil B) = p := by
  induction p with
  | nil => rfl
  | cons s tail ih => exact congrArg (Path.cons s) ih

theorem append_assoc (p : Path A B) (q : Path B C) (r : Path C D) :
    append (append p q) r = append p (append q r) := by
  induction p with
  | nil => rfl
  | cons s tail ih => exact congrArg (Path.cons s) (ih q)

def semantic {A B : Package} : Path A B → (A.base ⟶ B.base)
  | .nil _ => 𝟙 _
  | .cons s tail => s.semantic ≫ semantic tail

theorem semantic_append (p : Path A B) (q : Path B C) :
    semantic (append p q) = semantic p ≫ semantic q := by
  induction p with
  | nil => exact (Category.id_comp _).symm
  | cons s tail ih => simp only [append, semantic, ih, Category.assoc]

def action {A B : Package} : Path A B → RawPattern → RawPattern
  | .nil _, p => p
  | .cons s tail, p => action tail (raw s.semantic.native.sorts s.names p)

theorem action_append (p : Path A B) (q : Path B C) (r : RawPattern) :
    action (append p q) r = action q (action p r) := by
  induction p generalizing r with
  | nil => rfl
  | cons s tail ih => exact ih q (raw s.semantic.native.sorts s.names r)
end Path

instance : Category Package where
  Hom := Path
  id := Path.nil
  comp := Path.append
  id_comp _ := rfl
  comp_id := Path.append_nil
  assoc := Path.append_assoc

def toSemantic : Package ⥤ Signature where
  obj := Package.base
  map := Path.semantic
  map_id _ := rfl
  map_comp := Path.semantic_append

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
