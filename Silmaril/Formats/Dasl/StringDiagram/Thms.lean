module

public import Silmaril.Formats.Dasl.StringDiagram.Defs
import Silmaril.Proofs.Formats.Dasl.StringDiagram.Inputs

public section

namespace Silmaril.Formats.Dasl.StringDiagram

theorem splitInputs_flatten {α : Type} (groups : List (List α)) :
    splitInputs? (groups.map List.length) groups.flatten = some groups :=
  Proofs.Formats.Dasl.StringDiagram.splitInputs_flatten groups

theorem splitInputs_spec {α : Type} {widths : List Nat} {entries : List α}
    {groups : List (List α)} (hit : splitInputs? widths entries = some groups) :
    groups.map List.length = widths ∧ groups.flatten = entries :=
  Proofs.Formats.Dasl.StringDiagram.splitInputs_spec hit

end Silmaril.Formats.Dasl.StringDiagram
