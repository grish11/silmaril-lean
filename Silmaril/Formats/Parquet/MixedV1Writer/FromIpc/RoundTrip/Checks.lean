module

import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip.Thms
import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Thms

open Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.File

#print axioms read_roundTrip
#print axioms openFile_projection

#print axioms read_roundTripOrdered
#print axioms Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.prepareOrdered_exact
#print axioms Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.convertOrdered_ok_iff
#print axioms Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.emit_indexed_of_plan
#print axioms Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.convertOrdered_schema_only
#print axioms Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.convertOrdered_ok_iff
#print axioms Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.convertOrdered_readback
