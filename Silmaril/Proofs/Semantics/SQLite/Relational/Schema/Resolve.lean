module

public import Silmaril.Semantics.SQLite.Relational.Schema.Defs

public section

namespace Silmaril.Proofs.SQLite.Relational

open Silmaril.SQLite.Relational

theorem findColumn_eq_some_iff {Affinity Expr : Type} (schema : TableSchema Affinity Expr)
    (name : String) (i : schema.Index) : schema.findColumn name = some i ↔ schema.name i = name := by
  have sound (j : schema.Index) (found : schema.findColumn name = some j) : schema.name j = name :=
    beq_iff_eq.mp (List.find?_some (p := fun k => schema.name k == name) found)
  refine ⟨sound i, fun named => ?_⟩
  cases h : schema.findColumn name with
  | none =>
      exact False.elim ((List.find?_eq_none.mp h) i (by simp) (beq_iff_eq.mpr named))
  | some j =>
      exact congrArg some (schema.uniqueNames ((sound j h).trans named.symm))

theorem store_dynamicAny {Value Affinity : Type} (model : ValueModel Value Affinity) (value : Value) :
    (DeclaredColumnType.store model .dynamicAny value).map Subtype.val =
      model.applyAffinity model.numericAffinity value := by
  unfold DeclaredColumnType.store
  change ((model.applyAffinity model.numericAffinity value).bind _).map _ = _
  cases model.applyAffinity model.numericAffinity value <;> rfl

end Silmaril.Proofs.SQLite.Relational
