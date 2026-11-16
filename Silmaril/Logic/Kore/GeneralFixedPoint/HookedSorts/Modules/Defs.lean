module

public import Silmaril.Logic.Kore.GeneralFixedPoint.HookedSorts.Syntax.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.HookedSorts

/-- The retained metadata, selected names, and actual checked compilation are
bound by computation equations. The semantic package uses the selected names. -/
structure Package where
  source : Aliases.SourceDefinition
  fuel : Nat
  bindings : Builtins.SortBindings
  resolved : resolve source = some bindings
  checked : letI := bindings; Builtins.Checking.Package
  checked_input : checked.input = erase source
  checked_fuel : checked.fuel = fuel

def checkDefinition (fuel : Nat) (source : Aliases.SourceDefinition) : Option Package := do
  match resolved : resolve source with
  | none => none
  | some bindings =>
    letI := bindings
    match checked : Builtins.Checking.checkDefinition fuel (erase source) with
    | none => none
    | some package =>
      -- Package input and fuel are retained definitionally by the existing checker.
      have input : package.input = erase source ∧ package.fuel = fuel := by
        unfold Builtins.Checking.checkDefinition at checked
        split at checked
        · contradiction
        · split at checked
          · contradiction
          · cases Option.some.inj checked
            exact ⟨rfl, rfl⟩
      some ⟨source, fuel, bindings, resolved, package, input.1, input.2⟩

def checkText (fuel : Nat) (text : String) : Option Package := do
  checkDefinition fuel (← Syntax.parse text)

namespace Package

/-- The actual checked source modules, using the names selected from metadata. -/
abbrev CheckedModule (p : Package) :=
  letI := p.bindings
  Builtins.Checking.CheckedModule p.checked.checked

abbrev Model (p : Package) :=
  letI := p.bindings
  Builtins.Model p.checked.checked.native.ambient p.checked.checked.literalPrefix
    p.checked.checked.literals p.checked.checked.hooks

/-- Source satisfaction remains the independent raw interpreter. Erasure changes
only a declaration constructor; no original sentence or alias body is rewritten. -/
theorem models_native_iff (p : Package) (m : p.CheckedModule) (M : p.Model) :
    letI := p.bindings
    (∀ q ∈ m.axiomSet, q.Satisfies M) ↔
      (∀ q ∈ m.nativeAxiomSet, Matching.GeneralFixedPoint.Sentence.Satisfies M.native q) := by
  let : Builtins.SortBindings := p.bindings
  exact m.models_native_iff M

theorem satisfiable_native_iff (p : Package) (m : p.CheckedModule) :
    letI := p.bindings
    (∃ M : p.Model, ∀ q ∈ m.axiomSet, q.Satisfies M) ↔
      (∃ M : p.Model, ∀ q ∈ m.nativeAxiomSet,
        Matching.GeneralFixedPoint.Sentence.Satisfies M.native q) := by
  let : Builtins.SortBindings := p.bindings
  exact m.satisfiable_native_iff

theorem unsatisfiable_native_iff (p : Package) (m : p.CheckedModule) :
    letI := p.bindings
    (¬ ∃ M : p.Model, ∀ q ∈ m.axiomSet, q.Satisfies M) ↔
      (¬ ∃ M : p.Model, ∀ q ∈ m.nativeAxiomSet,
        Matching.GeneralFixedPoint.Sentence.Satisfies M.native q) := by
  let : Builtins.SortBindings := p.bindings
  exact m.unsatisfiable_native_iff

end Package
end Silmaril.Logic.Kore.GeneralFixedPoint.HookedSorts
