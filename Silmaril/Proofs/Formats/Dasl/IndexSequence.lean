module

public import Silmaril.Formats.Dasl.IndexSequence.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.IndexSequence

open Silmaril.Formats.Dasl.IndexSequence

theorem zip_eq_some_iff {Name : Type} {columns : Columns Name} {entries : Entries Name} :
    columns.zip? = some entries ↔ unzip entries = columns := by
  constructor
  · unfold Columns.zip?
    split
    · rename_i width
      rintro ⟨rfl⟩
      cases columns
      unfold unzip
      rw [List.unzip_zip width]
    · simp
  · rintro rfl
    exact columnsCodec.recovers entries

end Silmaril.Proofs.Formats.Dasl.IndexSequence
