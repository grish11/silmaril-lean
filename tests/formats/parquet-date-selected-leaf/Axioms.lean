module

import Silmaril.Formats.Parquet.Date.Leaf.Thms
import Silmaril.Formats.Parquet.Date.Leaf.Events.Thms
import Silmaril.Formats.Parquet.FlatScan.Thms

open Silmaril.Formats.Parquet

#print axioms FlatScan.scanColumn_wire
#print axioms Date.Leaf.bind_exact
#print axioms Date.Leaf.open_exact
#print axioms Date.Leaf.selectChunk_exact
#print axioms Date.Leaf.readGroup_exact
#print axioms Date.Leaf.pageWire_exact
#print axioms Date.Leaf.Events.readAll_reference
#print axioms Date.Leaf.Events.readAll_firstError
#print axioms Date.Leaf.Events.toIpc_firstError
#print axioms Date.Leaf.Events.toIpc_readback
#print axioms Date.Leaf.Events.toIpc_openError
