module

public import Silmaril.Formats.Dasl.StringDiagram.Defs

public section

open Silmaril.Formats.Dasl.StringDiagram

namespace Silmaril.Proofs.Formats.Dasl.StringDiagram

theorem splitInputs_flatten {α : Type} (groups : List (List α)) :
    splitInputs? (groups.map List.length) groups.flatten = some groups := by
  induction groups with
  | nil => rfl
  | cons first rest ih =>
    simp [splitInputs?, List.splitAt_eq, ih]

theorem splitInputs_spec {α : Type} {widths : List Nat} {entries : List α}
    {groups : List (List α)} (hit : splitInputs? widths entries = some groups) :
    groups.map List.length = widths ∧ groups.flatten = entries := by
  induction widths generalizing entries groups with
  | nil => cases entries <;> simp_all [splitInputs?]
  | cons width widths ih =>
    simp only [splitInputs?, List.splitAt_eq] at hit
    split at hit
    next size =>
      obtain ⟨rest, next, same⟩ := Option.bind_eq_some_iff.mp hit
      cases Option.some.inj same
      obtain ⟨lengths, contents⟩ := ih next
      simp [size, lengths, contents]
    next => contradiction

end Silmaril.Proofs.Formats.Dasl.StringDiagram
