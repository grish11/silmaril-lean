module

import Silmaril.Formats.Arrow.MixedFlat.File.Window.Thms
import Silmaril.Formats.Arrow.MixedFlat.File.Thms

open Silmaril.Formats.Arrow.MixedFlat.File
open Silmaril.Formats.Arrow.MixedFlat.File.Window

#print axioms readRecord_witness
#print axioms Window.readIndex_exact
#print axioms Window.Index.footer_range
#print axioms Window.Index.footer_bytes_exact
#print axioms Window.Index.block_ranges
#print axioms Window.Index.block_order
#print axioms Window.Index.readAt_exact
