module

public import Silmaril.Semantics.SQLite.Relational.Schema.Defs
import Silmaril.Proofs.Semantics.SQLite.Relational.Schema.Resolve

/-! Column resolution and write-coercion laws. -/

@[expose] public section

namespace Silmaril.SQLite.Relational

namespace TableSchema

variable {Affinity Expr : Type} (schema : TableSchema Affinity Expr)

@[simp] theorem findColumn_eq_some_iff (name : String) (i : schema.Index) :
    schema.findColumn name = some i ↔ schema.name i = name :=
  Proofs.SQLite.Relational.findColumn_eq_some_iff schema name i

theorem namedPositional_kind (i : schema.Index) :
    schema.namedPositional.positional.kind i = schema.kind i :=
  congrArg schema.kind (schema.namedPositional.column.left_inv i)

end TableSchema

namespace DeclaredColumnType

variable {Value Affinity : Type} (model : ValueModel Value Affinity) (value : Value)

@[simp] theorem store_strictAny :
    (store model (.strict .any) value).map Subtype.val = some value := rfl

@[simp] theorem store_dynamicAny :
    (store model .dynamicAny value).map Subtype.val =
    model.applyAffinity model.numericAffinity value :=
  Proofs.SQLite.Relational.store_dynamicAny model value

end DeclaredColumnType

end Silmaril.SQLite.Relational
