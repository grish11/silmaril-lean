module

public import Silmaril.Logic.Kore.GeneralFixedPoint.HookedSorts.Modules.Defs

/-! Explicit external registrations extend the common reader and reuse the
whole-definition alias checker. Registration names source sorts explicitly;
it neither recognizes a new builtin nor verifies an external implementation. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.HookedSorts.External
open CategoryTheory Silmaril.Logic.Institution

/-- The source sort name and the exact external hook string. -/
structure SortRegistration where
  name : String
  hook : String
  deriving DecidableEq, Repr

/-- A typed profile over the explicitly registered source sort names. -/
structure SymbolRegistration (sorts : List SortRegistration) where
  hook : String
  arguments : List String
  result : String
  arguments_registered : ∀ i : Fin arguments.length, arguments[i] ∈ sorts.map (·.name)
  result_registered : result ∈ sorts.map (·.name)

/-- Deployment-specific source-name bindings and independent mathematical
operation graphs. The graph is fixed before source checking and adequacy. -/
structure Registry where
  sorts : List SortRegistration
  sort_names_unique : (sorts.map (·.name)).Nodup
  sort_hooks_unique : (sorts.map (·.hook)).Nodup
  symbols : List (SymbolRegistration sorts)
  symbol_hooks_unique : (symbols.map (·.hook)).Nodup
  carrier : String → Type
  nonempty : ∀ s ∈ sorts.map (·.name), Nonempty (carrier s)
  operation : (d : SymbolRegistration sorts) → d ∈ symbols →
    (∀ i : Fin d.arguments.length, carrier d.arguments[i]) → Set (carrier d.result)

def Registry.acceptSort (r : Registry) (hook : String) : Bool :=
  r.sorts.any (fun s => s.hook == hook)

def Registry.acceptSymbol (r : Registry) (hook : String)
    (d : Kore.Modules.SymbolDeclaration) : Bool :=
  r.symbols.any (fun s => s.hook == hook && s.arguments == d.arguments && s.result == d.result)

def parse (r : Registry) (text : String) : Option Aliases.SourceDefinition := do
  let ts ← Kore.FixedPoint.Syntax.lex (text.toList.length + 1) text.toList []
  let (_, rest) ← Kore.Modules.Syntax.emptyAttributes ts
  let ms ← Kore.Modules.Syntax.modulesWithAliasAndSorts GeneralFixedPoint.Syntax.pattern
    Aliases.Syntax.declaration (Kore.Modules.Syntax.hookedSymbolWith r.acceptSymbol)
    (Kore.Modules.Syntax.hookedSortWith r.acceptSort) ts.length (ts.length + 1) rest
  if ms.isEmpty then none else some ⟨ms⟩

def sourceSorts (source : Aliases.SourceDefinition) : List SortRegistration :=
  source.modules.flatMap fun m => m.declarations.filterMap fun d =>
    match d.declaration with
    | .hookedSort name hook => some ⟨name, hook⟩
    | _ => none

/-- A successful reader alone does not establish the name-to-hook bindings.
Resolution requires precisely the registered declarations, with no duplicates. -/
def sortsValid (r : Registry) (source : Aliases.SourceDefinition) : Bool :=
  let ds := sourceSorts source
  ds.length == r.sorts.length && ds.all (fun s => r.sorts.contains s) &&
    (ds.map (·.name)).Nodup && (ds.map (·.hook)).Nodup

structure HookBinding where
  symbol : Kore.Modules.NamedSymbol
  hook : String
  deriving DecidableEq, Repr

def hooks (source : Aliases.SourceDefinition) : List HookBinding :=
  source.modules.flatMap fun m => m.declarations.zipIdx.filterMap fun (d, i) =>
    match d.declaration with
    | .hookedSymbol symbol hook => some ⟨⟨⟨m.name, i⟩, symbol⟩, hook⟩
    | _ => none

/-- Metadata erasure preserves the exact named patterns, aliases and origins. -/
def erase (source : Aliases.SourceDefinition) : Aliases.SourceDefinition :=
  ⟨source.modules.map fun m => {m with declarations := m.declarations.map fun item =>
    {item with declaration := match item.declaration with
      | .hookedSort name _ => .sort name
      | .hookedSymbol d _ => .symbol d
      | other => other}}⟩

structure Package (r : Registry) where
  text : String
  source : Aliases.SourceDefinition
  parsed : parse r text = some source
  fuel : Nat
  resolved : sortsValid r source = true
  checked : Aliases.Checking.CheckedDefinition
  unique_hooks : ((hooks source).map (·.hook)).Nodup
  compiled : Aliases.Checking.checkDefinition fuel (erase source) = some checked

def checkText (r : Registry) (fuel : Nat) (text : String) : Option (Package r) := do
  match parsed : parse r text with
  | none => none
  | some source =>
    if resolved : sortsValid r source = true then
      if unique_hooks : ((hooks source).map (·.hook)).Nodup then
        match compiled : Aliases.Checking.checkDefinition fuel (erase source) with
        | none => none
        | some checked => some ⟨text, source, parsed, fuel, resolved, checked, unique_hooks, compiled⟩
      else none
    else none

/-- Carrier agreements are required only for the registered source sorts;
ordinary source sorts remain unrestricted. -/
abbrev Carriers (r : Registry) {scope : Kore.Modules.Scope}
    (M : Matching.GeneralFixedPoint.Model scope.signature) :=
  ∀ s ∈ r.sorts.map (·.name), M.carrier s ≃ r.carrier s

/-- Exact operation graph equality for every actual argument tuple. An external
interpretation is a hypothesis about graphs, never a hypothesis about source
satisfaction or the correctness of compilation. -/
structure Laws (r : Registry) {scope : Kore.Modules.Scope}
    (sourceHooks : List HookBinding) (M : Matching.GeneralFixedPoint.Model scope.signature)
    (C : Carriers r M) : Prop where
  graph : ∀ b ∈ sourceHooks, ∀ d, ∀ hd : d ∈ r.symbols,
    b.hook = d.hook → b.symbol.declaration.arguments = d.arguments →
    b.symbol.declaration.result = d.result →
    ∀ (op : scope.signature.operations d.arguments.length (fun i => d.arguments[i]) d.result),
    op.val = b.symbol → ∀ args,
    M.operation op args = (C d.result d.result_registered).symm ''
      r.operation d hd
        (fun i => C d.arguments[i] (d.arguments_registered i) (args i))

structure Model (r : Registry) (p : Package r) where
  native : Matching.GeneralFixedPoint.Model p.checked.ambient.signature
  carriers : Carriers r native
  laws : Laws r (hooks p.source) native carriers

instance (r : Registry) (p : Package r) : Category (Model r p) where
  Hom M N := M.native ⟶ N.native
  id M := 𝟙 M.native
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

namespace Package
variable {r : Registry} (p : Package r)

def sourceRoom : Room :=
  ⟨Aliases.Sentence p.checked.ambient.signature, Cat.of (Model r p),
    fun M q => q.Satisfies M.native⟩

def nativeRoom : Room :=
  ⟨Matching.GeneralFixedPoint.Sentence p.checked.ambient.signature, Cat.of (Model r p),
    fun M q => Matching.GeneralFixedPoint.Sentence.Satisfies M.native q⟩

def lowering : Corridor p.sourceRoom p.nativeRoom :=
  ⟨Aliases.Sentence.lower, 𝟭 _, fun M q => (q.satisfies_lower M.native).symm⟩

/-- Expansion retains the entire restricted model literally. -/
theorem lowering_modelExpansive : p.lowering.ModelExpansive :=
  fun M => ⟨M, rfl⟩

theorem models_native_iff (H : Set (Aliases.Sentence p.checked.ambient.signature))
    (M : Model r p) :
    (∀ q ∈ H, q.Satisfies M.native) ↔
      (∀ q ∈ Aliases.Sentence.lower '' H,
        Matching.GeneralFixedPoint.Sentence.Satisfies M.native q) :=
  Aliases.models_lower_iff _ H M.native

theorem satisfiable_native_iff (H : Set (Aliases.Sentence p.checked.ambient.signature)) :
    (∃ M : Model r p, ∀ q ∈ H, q.Satisfies M.native) ↔
      (∃ M : Model r p, ∀ q ∈ Aliases.Sentence.lower '' H,
        Matching.GeneralFixedPoint.Sentence.Satisfies M.native q) :=
  exists_congr (p.models_native_iff H)

theorem unsatisfiable_native_iff (H : Set (Aliases.Sentence p.checked.ambient.signature)) :
    (¬ ∃ M : Model r p, ∀ q ∈ H, q.Satisfies M.native) ↔
      (¬ ∃ M : Model r p, ∀ q ∈ Aliases.Sentence.lower '' H,
        Matching.GeneralFixedPoint.Sentence.Satisfies M.native q) :=
  not_congr (p.satisfiable_native_iff H)

theorem consequence_native_iff (H : Set (Aliases.Sentence p.checked.ambient.signature))
    (q : Aliases.Sentence p.checked.ambient.signature) :
    (∀ M : Model r p, (∀ a ∈ H, a.Satisfies M.native) → q.Satisfies M.native) ↔
      (∀ M : Model r p, (∀ a ∈ Aliases.Sentence.lower '' H,
        Matching.GeneralFixedPoint.Sentence.Satisfies M.native a) →
          Matching.GeneralFixedPoint.Sentence.Satisfies M.native q.lower) := by
  simp_rw [← Aliases.Sentence.satisfies_lower, ← p.models_native_iff H]

end Package
end Silmaril.Logic.Kore.GeneralFixedPoint.HookedSorts.External
