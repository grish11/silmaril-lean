module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps
open CategoryTheory

/-- Actual literal text parsing commutes in the forward direction on every
successfully parsed literal, including independently named builtin carriers.
No target parser-success or denotation equation is a caller premise. -/
theorem literal_parse_forward {A B : Signature} (f : A ⟶ B)
    (s text : String) (l : Literal)
    (parsed : @Literal.parse A.bindings s text = some l) :
    @Literal.parse B.bindings (f.native.sorts s) text = some l := by
  change (if s = A.bindings.intSort then (decimalInteger text).map Literal.integer
    else if s = A.bindings.boolSort then
      if text = "true" then some (.boolean true)
      else if text = "false" then some (.boolean false) else none
    else none) = some l at parsed
  change (if f.native.sorts s = B.bindings.intSort then (decimalInteger text).map Literal.integer
    else if f.native.sorts s = B.bindings.boolSort then
      if text = "true" then some (.boolean true)
      else if text = "false" then some (.boolean false) else none
    else none) = some l
  by_cases integer : s = A.bindings.intSort
  · rw [ite_eq_left integer] at parsed
    rw [ite_eq_left ((congrArg f.native.sorts integer).trans f.integer)]
    exact parsed
  · by_cases boolean : s = A.bindings.boolSort
    · rw [ite_eq_right integer, ite_eq_left boolean] at parsed
      have mappedBoolean : f.native.sorts s = B.bindings.boolSort :=
        (congrArg f.native.sorts boolean).trans f.boolean
      have mappedNotInteger : f.native.sorts s ≠ B.bindings.intSort := by
        rw [mappedBoolean]
        exact Ne.symm B.bindings.distinct
      rw [ite_eq_right mappedNotInteger, ite_eq_left mappedBoolean]
      exact parsed
    · rw [ite_eq_right integer, ite_eq_right boolean] at parsed
      cases parsed

namespace Surface

/-- First-hit lookup preserves declaration order and name identity, even if
source names have duplicates. This is not an alias-free shadowing assumption. -/
theorem find_symbols_map (sortMap names : String → String) (injective : Function.Injective names)
    (symbols : List Kore.Modules.NamedSymbol) (wanted : String) :
    (symbols.map (symbol sortMap names)).find? (fun d => d.declaration.name == names wanted) =
      (symbols.find? (fun d => d.declaration.name == wanted)).map (symbol sortMap names) := by
  induction symbols with
  | nil => rfl
  | cons d tail ih =>
      by_cases same : d.declaration.name = wanted
      · simp [List.find?, symbol, declaration, same]
      · have mapped : names d.declaration.name ≠ names wanted := fun h => same (injective h)
        have sourceMiss : (d.declaration.name == wanted) = false := beq_eq_false_iff_ne.mpr same
        have targetMiss : (names d.declaration.name == names wanted) = false :=
          beq_eq_false_iff_ne.mpr mapped
        simp [List.find?, symbol, declaration, sourceMiss, targetMiss, ih]

theorem Step.find_symbols {A B : Package} (f : Step A B) (wanted : String) :
    B.base.scope.symbols.find? (fun d => d.declaration.name == f.names wanted) =
      (A.base.scope.symbols.find? (fun d => d.declaration.name == wanted)).map
        (symbol f.semantic.native.sorts f.names) := by
  rw [f.symbolDeclarations]
  exact find_symbols_map _ _ f.injective _ _

end Surface
end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps
