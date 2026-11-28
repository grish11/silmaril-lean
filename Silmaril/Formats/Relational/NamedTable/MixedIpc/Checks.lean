module

import Silmaril.Formats.Relational.NamedTable.MixedIpc.Thms

open Silmaril.Formats.Relational.NamedTable.MixedIpc

#print axioms descriptor_exact
#print axioms Descriptor.schema_columns
#print axioms Descriptor.schema_injective
#print axioms batchPairs_exact
#print axioms read_exact
#print axioms read_wire
#print axioms importIpc_ok_iff
#print axioms importIpc_eq_of_table
#print axioms importIpc_openFailure
#print axioms importIpc_readFailure
