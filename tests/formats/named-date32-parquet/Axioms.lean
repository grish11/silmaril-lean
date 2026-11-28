module

import Silmaril.Formats.Relational.NamedTable.Date32.Export.Thms
import Silmaril.Formats.Parquet.Date.FromIpc.Thms
import Silmaril.Formats.Parquet.FlatInt32Writer.Thms

open Silmaril.Formats.Relational.NamedTable.Date32.Export

#print axioms select_eq_ok_iff
#print axioms select_missing
#print axioms select_badIndex
#print axioms select_badField
#print axioms select_badKind
#print axioms select_rowLimit
#print axioms convert_eq_ok_iff
#print axioms convert_selectError
#print axioms convert_writeError
#print axioms convert_readback
#print axioms Silmaril.Formats.Parquet.Date.FromIpc.emitGroup_readback
#print axioms Silmaril.Formats.Parquet.FlatInt32Writer.emitAnnotated_checked
