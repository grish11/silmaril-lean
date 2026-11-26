module

public import Silmaril.Semantics.SQLite.Relational.Schema.Thms

/-! D1 storage values and bounded affinity instantiate the D2 storage boundary. -/

@[expose] public section

namespace Silmaril.SQLite.Relational

/-- Resolve the type name of a column in the selected table mode. The input
is the declaration obtained after parsing SQL. -/
def DeclaredColumnType.resolve :
    (mode : TypingMode) → Option String → Option (DeclaredColumnType Affinity mode)
  | .dynamic, declaration =>
    if declaration.any (fun name => name.toLower == "any") then some .dynamicAny
    else some (.dynamic declaration (Affinity.ofDeclaredType declaration))
  | .strict, declaration => (StrictType.ofDeclaredType declaration).map .strict

/-- Use D1 for writing storage values. D2's admission boundary reports a
failed conversion as absence. Call D1 directly to observe the reason. -/
def ValueModel.sqlValue : ValueModel SqlValue Affinity where
  isNull value := value.storageClass == .null
  asRowId
    | .integer id => some id
    | _ => none
  applyAffinity affinity value := (affinity.apply value).toOption
  numericAffinity := .numeric
  strictMatches declaration value := declaration.accepts value.storageClass
  coerceStrict declaration value := (ColumnType.apply (.strict declaration) value).toOption

end Silmaril.SQLite.Relational
