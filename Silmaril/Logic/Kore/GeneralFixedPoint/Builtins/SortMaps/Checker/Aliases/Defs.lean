module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Checker.Lookup.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface

def mapFormal (sortMap : String → String) (p : Aliases.Formal) : Aliases.Formal :=
  { p with sort := sortMap p.sort }

/-- Formal identity includes namespace and name; neither is changed by a
structural step. This transports each fresh namespace independently. -/
theorem formalNames_map (sortMap : String → String) (ps : List Aliases.Formal)
    (isSet : Bool) :
    (ps.map (mapFormal sortMap)).filterMap
        (fun p => if p.isSet == isSet then some (p.name, p.sort) else none) =
      mapNames sortMap (ps.filterMap
        (fun p => if p.isSet == isSet then some (p.name, p.sort) else none)) := by
  rw [mapNames_eq_map, List.filterMap_map, List.map_filterMap]
  apply List.filterMap_congr
  intro p _
  by_cases same : p.isSet = isSet
  · simp [mapFormal, same]
  · simp [mapFormal, same]

theorem alias_names (sortMap nameMap : String → String) (d : Alias) (isSet : Bool) :
    (renameAlias sortMap nameMap d).names isSet = mapNames sortMap (d.names isSet) := by
  exact formalNames_map sortMap d.parameters isSet

/-- The zip truncation behavior is retained even on malformed arities. No
validity assumption or successful checker receipt is needed for lookup itself. -/
theorem formalArgument_find (sortMap nameMap : String → String)
    (ps : List Aliases.Formal) (args : List RawPattern) (isSet : Bool) (name : String) :
    ((ps.map (mapFormal sortMap)).zip (args.map (raw sortMap nameMap))).find?
        (fun p : Aliases.Formal × RawPattern => p.1.isSet == isSet && p.1.name == name) =
      ((ps.zip args).find? (fun p : Aliases.Formal × RawPattern => p.1.isSet == isSet && p.1.name == name)).map
        (Prod.map (mapFormal sortMap) (raw sortMap nameMap)) := by
  rw [List.zip_map, List.find?_map]
  rfl

/-- Actual raw argument retrieval, including its failure result, commutes with
the source action. Variable names are not passed through the symbol name map. -/
theorem alias_argument (sortMap nameMap : String → String) (d : Alias)
    (args : List RawPattern) (isSet : Bool) (name : String) :
    (renameAlias sortMap nameMap d).argument (args.map (raw sortMap nameMap)) isSet name =
      (d.argument args isSet name).map (raw sortMap nameMap) := by
  unfold Alias.argument Aliases.Declaration.argument
  change (do
    let pair ← ((d.parameters.map (mapFormal sortMap)).zip (args.map (raw sortMap nameMap))).find?
      (fun p : Aliases.Formal × RawPattern => p.1.isSet == isSet && p.1.name == name)
    return pair.2) = _
  rw [formalArgument_find]
  cases found : (d.parameters.zip args).find?
      (fun p : Aliases.Formal × RawPattern => p.1.isSet == isSet && p.1.name == name) <;> rfl

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.SortMaps.Surface
