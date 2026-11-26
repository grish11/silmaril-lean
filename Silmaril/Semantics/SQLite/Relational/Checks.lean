module

import Silmaril.Semantics.SQLite.Relational.All

/-! Consumer checks for the Semantics-only public entry point. -/

open Silmaril.SQLite.Relational

#check SqlValue
#check Value.toSql_ofSql
#check Value.forgetPointers_not_injective
#check ColumnType.strict_apply_eq_ok_iff
#check ValueModel.sqlValue
#check TableSchema.findColumn_eq_some_iff
#check CheckedTable.rowsEquivColumns
#check CheckedTable.check_transpose
#check Snapshot.ForeignKeysValid
#check recover_eraseKeepingIdentity
#check Prepared.bindInt64
#check Executor.executeBatch_iff
#check HostRequest.collapse_explicit
#check CatalogExecutor.Target.lookup_iff
#check CatalogExecutor.execute_eq
