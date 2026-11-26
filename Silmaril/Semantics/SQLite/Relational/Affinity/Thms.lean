module

public import Silmaril.Semantics.SQLite.Relational.Affinity.Defs
import Silmaril.Proofs.Semantics.SQLite.Relational.Affinity.StorageClass

/-! Laws at the column-write affinity boundary. -/

public section

namespace Silmaril.SQLite.Relational

@[simp] theorem Affinity.apply_null (affinity : Affinity) :
    affinity.apply .null = .ok .null := by cases affinity <;> rfl

@[simp] theorem Affinity.apply_blob (affinity : Affinity) (bytes : ByteArray) :
    affinity.apply (.blob bytes) = .ok (.blob bytes) := by cases affinity <;> rfl

theorem Affinity.apply_integer_eq_numeric (value : SqlValue) :
    Affinity.integer.apply value = Affinity.numeric.apply value := rfl

@[simp] theorem ColumnType.apply_strict_any (value : SqlValue) :
    ColumnType.apply (.strict .any) value = .ok value := by cases value <;> rfl

@[simp] theorem ColumnType.apply_null (column : ColumnType) :
    column.apply .null = .ok .null := by
  cases column with
  | ordinary affinity => exact affinity.apply_null
  | strict type => simp [ColumnType.apply, StrictType.accepts, SqlValue.storageClass]

theorem ColumnType.strict_apply_eq_ok_iff {type : StrictType} {input output : SqlValue} :
    ColumnType.apply (.strict type) input = .ok output ↔
      type.affinity.apply input = .ok output ∧ type.accepts output.storageClass = true :=
  Proofs.ColumnType.strict_apply_eq_ok_iff

theorem ColumnType.strict_result_accepted {type : StrictType} {input output : SqlValue}
    (h : ColumnType.apply (.strict type) input = .ok output) :
    type.accepts output.storageClass = true := (strict_apply_eq_ok_iff.mp h).2

end Silmaril.SQLite.Relational
