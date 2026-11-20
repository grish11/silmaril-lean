module

public import Silmaril.Formats.Dasl.IndexSequence.Defs
import Silmaril.Proofs.Formats.Dasl.IndexSequence

public section

namespace Silmaril.Formats.Dasl.IndexSequence

variable {Name Cas Item : Type}

theorem zip_unzip (entries : Entries Name) : (unzip entries).zip? = some entries :=
  columnsCodec.recovers entries

theorem zip_eq_some_iff {columns : Columns Name} {entries : Entries Name} :
    columns.zip? = some entries ↔ unzip entries = columns :=
  Proofs.Formats.Dasl.IndexSequence.zip_eq_some_iff

theorem parallel_accepts (names : SequenceCodec Name Cas) (indices : SequenceCodec Nat Cas)
    {input : Shallow Cas} {entries : Entries Name} :
    (parallel names indices).decode? input = some entries ↔
      (rawColumns names indices).decode? input = some (unzip entries) := by
  simp [parallel, columnsCodec, Encode.TotalCodec.then, Option.bind_eq_some_iff, zip_eq_some_iff]

theorem checked_accepts {profile : Profile} {raw : SequenceCodec (Name × Nat) Cas}
    {input : Shallow Cas} {output : Checked profile Name} :
    (checked profile raw).decode? input = some output ↔ raw.decode? input = some output.val := by
  simp [checked, Encode.TotalCodec.then, check?, Option.bind_eq_some_iff, Subtype.ext_iff, output.property]

theorem parent_descends {data : Checked .orderedParent Name} (row : Fin data.val.length)
    (notRoot : (data.val.get row).2 ≠ row.val) : (data.val.get row).2 < row.val :=
  Nat.lt_of_le_of_ne (data.property row) notRoot

theorem paged_agrees {width : { size : Nat // 0 < size }}
    (item : Encode.TotalCodec Item (Shallow Cas)) (items : List Item) :
    (paged width item).decode? ((paged width item).encode items) =
      (flat item).decode? ((flat item).encode items) := by
  rw [(paged width item).recovers, (flat item).recovers]

end Silmaril.Formats.Dasl.IndexSequence
