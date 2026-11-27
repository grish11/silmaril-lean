module

import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.File.Thms

open Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip
open Silmaril.Formats.Parquet.Int32ByteArrayGroup.File

#print axioms read_roundTrip
#print axioms openFile_projection
