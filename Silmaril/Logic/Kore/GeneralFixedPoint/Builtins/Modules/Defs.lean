module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Institution.Defs

/-! The module package compiles original located axioms and claims directly.
The checked lowering retains the independent original-visibility check. Native
presentations here use the direct compiler, whose original-source adequacy is
proved; equality with the auxiliary alias checker's lowered AST is not assumed. -/
-- Configurable builtin names intentionally have a canonical fallback instance.
set_option linter.concreteInstances false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
variable [sorts : SortBindings]
open Silmaril.Logic.Institution

namespace CheckedDefinition

def aliases (d : CheckedDefinition) : List Alias :=
  d.lowered.flatMap fun m => m.aliases.map fun (a, mi) => ⟨a, mi⟩

def literals (d : CheckedDefinition) : List LiteralBinding := d.lowered.flatMap LoweredModule.literals

def hooks (d : CheckedDefinition) : List HookBinding := d.lowered.flatMap LoweredModule.hooks
end CheckedDefinition

structure LocatedSentence (scope : Kore.Modules.Scope) (literals : List LiteralBinding) (literalPrefix : String) where
  location : Kore.Modules.Location
  source : CheckedSentence scope literals literalPrefix

namespace Checking

def checkedSentence (scope : Kore.Modules.Scope) (aliases : List Alias) (literals : List LiteralBinding)
    (literalPrefix : String) (mi fuel : Nat) (raw : RawPattern) :
    Option (CheckedSentence scope literals literalPrefix) := do
  let sets := (GeneralFixedPoint.Checking.freeNames true fuel [] raw).eraseDups
  let objects := (GeneralFixedPoint.Checking.freeNames false fuel [] raw).eraseDups
  let s ← Aliases.Checking.resultSort scope (aliases.map Alias.toDeclaration) raw
  match accepted : elaborate scope aliases literals literalPrefix mi fuel sets objects s raw with
  | none => none
  | some typed => if admitted : typed.admissible = true then
      some ⟨aliases, mi, fuel, sets, objects, s, raw, typed, accepted, admitted⟩ else none

def localSentences (d : CheckedDefinition) (mi : Nat) (m : Aliases.SourceModule) (claims : Bool) :
    Option (List (LocatedSentence d.native.ambient d.literals d.literalPrefix)) :=
  m.declarations.filterMapM fun item =>
    match item.declaration with
    | .ruleAxiom raw => if claims then pure none else do
        let p ← checkedSentence d.native.ambient d.aliases d.literals d.literalPrefix mi d.fuel raw
        pure (some ⟨item.location, p⟩)
    | .claim raw => if claims then do
        let p ← checkedSentence d.native.ambient d.aliases d.literals d.literalPrefix mi d.fuel raw
        pure (some ⟨item.location, p⟩)
      else pure none
    | _ => pure none

structure CheckedModule (d : CheckedDefinition) where
  source : Aliases.SourceModule
  moduleIndex : Nat
  localAxioms : List (LocatedSentence d.native.ambient d.literals d.literalPrefix)
  claims : List (LocatedSentence d.native.ambient d.literals d.literalPrefix)
  inheritedAxioms : List (LocatedSentence d.native.ambient d.literals d.literalPrefix)
  local_checked : localSentences d moduleIndex source false = some localAxioms
  claims_checked : localSentences d moduleIndex source true = some claims

def CheckedModule.axioms {d : CheckedDefinition} (m : CheckedModule d) :=
  m.localAxioms ++ m.inheritedAxioms

/-- Import inheritance follows the actual ordered original import declarations.
All original module names and import visibility were checked independently by
`d.skeleton_checked`, before any literal declarations were injected. -/
def checkModule (d : CheckedDefinition) (earlier : List (CheckedModule d))
    (m : Aliases.SourceModule) (mi : Nat) : Option (CheckedModule d) := do
  let names ← Aliases.Checking.orderedImports m
  let parents ← names.mapM fun name => earlier.find? (fun p => p.source.name == name)
  match localChecked : localSentences d mi m false with
  | none => none
  | some localAxioms =>
    match claimsChecked : localSentences d mi m true with
    | none => none
    | some claims =>
      return ⟨m, mi, localAxioms, claims, parents.flatMap CheckedModule.axioms,
        localChecked, claimsChecked⟩

def compileModules (d : CheckedDefinition) : Option (List (CheckedModule d)) :=
  d.source.modules.zipIdx.foldlM (fun earlier (m, mi) => do
    let checked ← checkModule d earlier m mi
    pure (earlier ++ [checked])) []

/-- Both the lowering and the original-source compilation are tied to actual
successful computations. Clients need not trust an unrelated hand-built list. -/
structure Package where
  input : Aliases.SourceDefinition
  fuel : Nat
  checked : CheckedDefinition
  lowering_checked : Builtins.checkDefinition fuel input = some checked
  source_input : checked.source = input
  fuel_input : checked.fuel = fuel
  modules : List (CheckedModule checked)
  compiled : compileModules checked = some modules

def checkDefinition (fuel : Nat) (source : Aliases.SourceDefinition) : Option Package := do
  match loweringChecked : Builtins.checkDefinition fuel source with
  | none => none
  | some d =>
    match compiled : compileModules d with
    | none => none
    | some ms =>
      let input := Builtins.checkDefinition_input loweringChecked
      some ⟨source, fuel, d, loweringChecked, input.1, input.2, ms, compiled⟩

def checkText (fuel : Nat) (text : String) : Option Package := do
  checkDefinition fuel (← Syntax.parse text)
end Checking

namespace Checking.CheckedModule
variable {d : CheckedDefinition}

def axiomSet (m : CheckedModule d) : Set (CheckedSentence d.native.ambient d.literals d.literalPrefix) :=
  {p | ∃ item ∈ m.axioms, item.source = p}

/-- This is the compiled native presentation of the original source theory,
including imported axioms. Claims remain obligations, not extra premises. -/
def nativeAxiomSet (m : CheckedModule d) :
    Set (Matching.GeneralFixedPoint.Sentence d.native.ambient.signature) :=
  CheckedSentence.lower '' m.axiomSet

theorem models_native_iff (m : CheckedModule d)
    (M : Model d.native.ambient d.literalPrefix d.literals d.hooks) :
    (∀ p ∈ m.axiomSet, p.Satisfies M) ↔
      (∀ q ∈ m.nativeAxiomSet, Matching.GeneralFixedPoint.Sentence.Satisfies M.native q) :=
  models_lower_iff m.axiomSet M

theorem satisfiable_native_iff (m : CheckedModule d) :
    (∃ M : Model d.native.ambient d.literalPrefix d.literals d.hooks, ∀ p ∈ m.axiomSet, p.Satisfies M) ↔
      (∃ M : Model d.native.ambient d.literalPrefix d.literals d.hooks, ∀ q ∈ m.nativeAxiomSet,
        Matching.GeneralFixedPoint.Sentence.Satisfies M.native q) :=
  satisfiable_iff d.hooks m.axiomSet

theorem unsatisfiable_native_iff (m : CheckedModule d) :
    (¬ ∃ M : Model d.native.ambient d.literalPrefix d.literals d.hooks, ∀ p ∈ m.axiomSet, p.Satisfies M) ↔
      (¬ ∃ M : Model d.native.ambient d.literalPrefix d.literals d.hooks, ∀ q ∈ m.nativeAxiomSet,
        Matching.GeneralFixedPoint.Sentence.Satisfies M.native q) :=
  unsatisfiable_iff d.hooks m.axiomSet

theorem proves_native_iff (m : CheckedModule d) (p : CheckedSentence d.native.ambient d.literals d.literalPrefix) :
    (sourceRoom d.native.ambient d.literals d.literalPrefix d.hooks).Entails m.axiomSet p ↔
      (nativeRoom d.native.ambient d.literalPrefix d.literals d.hooks).Entails m.nativeAxiomSet p.lower :=
  entails_iff _ _ _ _ m.axiomSet p
end Checking.CheckedModule
end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
