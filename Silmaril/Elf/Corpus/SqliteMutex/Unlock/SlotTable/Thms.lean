module

public import Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding.Defs
import Silmaril.Proofs.Elf.Corpus.SqliteMutex.Unlock.SlotTable

public section

namespace Silmaril.Elf.Corpus.SqliteMutex.Unlock.SlotTable

open Silmaril.Elf.Link
open Silmaril.Elf.Link.DynElf
open Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding (absoluteReloc)

local notation "Sqlite" => Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.F

/-- Any successfully decoded `DT_RELA` table of the pinned SQLite file contains this row. -/
theorem absolute_relocation_mem {dynamic : Elf.DynInfo} {regular : List Elf.Rela}
    (headers : Dyn.finfo Sqlite = some dynamic)
    (parsed : Dyn.frun Sqlite (Elf.relaTable dynamic Elf.DT_RELA
      ((dynamic.tag Elf.DT_RELASZ).getD 0 / 24)) = some regular) :
    absoluteReloc ∈ regular :=
  Proofs.Elf.Corpus.SqliteMutex.Unlock.SlotTable.absolute_relocation_mem headers parsed

end Silmaril.Elf.Corpus.SqliteMutex.Unlock.SlotTable
