module

public import Silmaril.Semantics.SQLite.Relational.Affinity.Defs

public section

namespace Silmaril.SQLite.Relational.Proofs.ColumnType

theorem strict_apply_eq_ok_iff {type : StrictType} {input output : SqlValue} :
    ColumnType.apply (.strict type) input = .ok output ↔
      type.affinity.apply input = .ok output ∧ type.accepts output.storageClass = true := by
  cases converted : type.affinity.apply input with
  | error err => simp [ColumnType.apply, converted]
  | ok value =>
    by_cases accepted : type.accepts value.storageClass = true
    · simp [ColumnType.apply, converted, accepted]
      exact fun equal => equal ▸ accepted
    · simp [ColumnType.apply, converted, accepted]
      exact fun equal => equal ▸ Bool.eq_false_iff.mpr accepted

end Silmaril.SQLite.Relational.Proofs.ColumnType
