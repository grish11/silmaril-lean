module

import Silmaril.Formats.Parquet.Date.PageLess.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms
import Silmaril.Formats.Parquet.Footer.PageLessInt32.Thms
import Silmaril.Formats.Parquet.Date.Events.ToIpc.Thms

open Silmaril.Formats.Parquet

#print axioms Footer.PageLessInt32.validate_framed
#print axioms Footer.PageLessInt32.pageLess_zero
#print axioms Snapshot.checkPageLessInt32_exact
#print axioms Date.Events.ToIpc.emit_readback
#print axioms Date.PageLess.open_exact
#print axioms Date.PageLess.readGroup_framed
#print axioms Date.PageLess.readGroup_pageLess
#print axioms Date.PageLess.readAll_eof
#print axioms Date.PageLess.readAll_noGroups
#print axioms Date.PageLess.readAll_oneEmpty
#print axioms Date.PageLess.toIpc_readback
