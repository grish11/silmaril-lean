module

public import Silmaril.Formats.Arrow.MixedFlat.File.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Events.Defs
import Silmaril.Formats.Arrow.MixedFlat.File.Thms
import Silmaril.Formats.Arrow.MixedFlat.Events.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Events

open Silmaril.Formats.Arrow

theorem readRecord_shape {limits : MixedFlat.Limits} {input : KBytes}
    {fields : List MixedFlat.Field} {block : FileBlock} {observed : MixedFlat.Observed}
    (read : MixedFlat.File.readRecord limits input fields block = .ok observed) :
    observed.columns.map Prod.fst = fields ∧
      ∀ pair ∈ observed.columns, (MixedFlat.Events.cells pair.2).length = observed.rowCount := by
  obtain ⟨_, _, _, _, _, parsed⟩ := MixedFlat.File.readRecord_witness read
  exact MixedFlat.Events.readParsed_shape parsed

end Silmaril.Proofs.Formats.Arrow.MixedFlat.File.Events
