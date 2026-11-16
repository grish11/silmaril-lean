module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Contexts.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface

/-- Erasing the membership witness preserves the actual first selected value. -/
theorem attached_find_val {α : Type} (xs : List α) (p : α → Bool) :
    (xs.attach.find? (fun d => p d.val)).map Subtype.val = xs.find? p := by
  simpa only [List.unattach_attach] using
    (List.find?_subtype (l := xs.attach) (hf := fun _ _ => rfl))

/-- Naming a sort remains possible after identifying ordinary sorts. The
reverse implication would be false and is deliberately not asserted. -/
theorem Step.namedSort_forward {A B : Package} (f : Step A B) (s : String)
    (named : Kore.Modules.Checking.namedSort A.base.scope s = true) :
    Kore.Modules.Checking.namedSort B.base.scope (f.semantic.native.sorts s) = true := by
  rcases List.any_eq_true.mp named with ⟨d, member, same⟩
  apply List.any_eq_true.mpr
  refine ⟨(d.1, f.semantic.native.sorts d.2), ?_, ?_⟩
  · rw [f.sortDeclarations]
    exact List.mem_map_of_mem member
  · have eq : d.2 = s := by simpa using same
    simp [eq]

/-- Printed symbol lookup keeps the first selected declaration, including its
origin. This concerns name lookup, not literal profile lookup. -/
theorem Step.symbol_find {A B : Package} (f : Step A B) (name : String) :
    B.base.scope.symbols.find? (fun d => d.declaration.name == f.names name) =
      (A.base.scope.symbols.find? (fun d => d.declaration.name == name)).map
        (symbol f.semantic.native.sorts f.names) := by
  exact f.find_symbols name

/-- Alias lookup also preserves first-hit order. Symbols still shadow aliases
because symbol lookup is transported independently by `symbol_find`. -/
theorem Step.alias_find {A B : Package} (f : Step A B) (name : String) :
    B.aliases.find? (fun d => d.symbol.name == f.names name) =
      (A.aliases.find? (fun d => d.symbol.name == name)).map
        (renameAlias f.semantic.native.sorts f.names) := by
  rw [f.aliasDeclarations, List.find?_map]
  congr 1
  congr 1
  funext d
  exact mapped_name_test f.names f.injective d.symbol.name name

/-- Successful symbol selection retains its concrete declaration even though
the attached membership witness belongs to the target ordered scope. -/
theorem Step.symbol_attached_some {A B : Package} (f : Step A B) (name : String)
    (d : {d // d ∈ A.base.scope.symbols})
    (source : A.base.scope.symbols.attach.find? (fun d => d.val.declaration.name == name) = some d) :
    ∃ d' : {d // d ∈ B.base.scope.symbols},
      B.base.scope.symbols.attach.find? (fun d => d.val.declaration.name == f.names name) = some d' ∧
      d'.val = symbol f.semantic.native.sorts f.names d.val := by
  have erased := attached_find_val A.base.scope.symbols (fun d => d.declaration.name == name)
  rw [source] at erased
  have target := f.symbol_find name
  rw [← erased] at target
  rw [← attached_find_val B.base.scope.symbols (fun d => d.declaration.name == f.names name)] at target
  cases found : B.base.scope.symbols.attach.find? (fun d => d.val.declaration.name == f.names name) with
  | none => simp [found] at target
  | some d' =>
      refine ⟨d', rfl, ?_⟩
      simpa only [found, Option.map_some, Option.some.injEq] using target

theorem Step.symbol_attached_none {A B : Package} (f : Step A B) (name : String)
    (source : A.base.scope.symbols.attach.find? (fun d => d.val.declaration.name == name) = none) :
    B.base.scope.symbols.attach.find? (fun d => d.val.declaration.name == f.names name) = none := by
  have erased := attached_find_val A.base.scope.symbols (fun d => d.declaration.name == name)
  rw [source] at erased
  have target := f.symbol_find name
  rw [← erased] at target
  rw [← attached_find_val B.base.scope.symbols (fun d => d.declaration.name == f.names name)] at target
  cases found : B.base.scope.symbols.attach.find? (fun d => d.val.declaration.name == f.names name) with
  | none => rfl
  | some d' => simp [found] at target

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
