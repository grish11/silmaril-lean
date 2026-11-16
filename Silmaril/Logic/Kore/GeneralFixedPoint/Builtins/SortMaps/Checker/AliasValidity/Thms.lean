module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Aliases.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface

/-- Alias validity is a finite syntax check. Its profile and formal-identity
conditions survive ordinary sort identifications; named sorts move forward. -/
theorem Step.alias_valid {A B : Package} (f : Step A B) (d : Alias)
    (valid : d.valid A.base.scope = true) :
    (renameAlias f.semantic.native.sorts f.names d).valid B.base.scope = true := by
  simp only [Alias.valid, Aliases.Declaration.valid, Bool.and_eq_true] at valid ⊢
  rcases valid with ⟨⟨⟨profile, distinct⟩, arguments⟩, result⟩
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · have eq : d.parameters.map Aliases.Formal.sort = d.symbol.arguments := by
      simpa only [beq_iff_eq] using profile
    have mapped := congrArg (List.map f.semantic.native.sorts) eq
    simpa only [renameAlias, declaration, List.map_map, Function.comp_def, beq_iff_eq] using mapped
  · simpa only [renameAlias, List.map_map, Function.comp_def, List.length_map] using distinct
  · apply List.all_eq_true.mpr
    intro s member
    change s ∈ d.symbol.arguments.map f.semantic.native.sorts at member
    rcases List.mem_map.mp member with ⟨sourceSort, sourceMember, rfl⟩
    exact f.namedSort_forward sourceSort ((List.all_eq_true.mp arguments) sourceSort sourceMember)
  · exact f.namedSort_forward d.symbol.result result

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
