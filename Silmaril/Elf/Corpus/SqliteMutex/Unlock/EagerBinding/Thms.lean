module

public import Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding.Defs
import Silmaril.Proofs.Elf.Corpus.SqliteMutex.Unlock.EagerBinding

public section

namespace Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding

open Silmaril.Elf
open Silmaril.Elf.Link
open Silmaril.Elf.Link.DynElf
open Silmaril.Elf.Corpus.SqliteMutex.Unlock
open Silmaril.X86.Link (Blob)
open Silmaril.X86 (Word)

local notation "Sqlite" => Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.F
local notation "Glibc" => Silmaril.Elf.Staged.Pinned.GlibcLibc.F

/-- The supplied scope skips SQLite's undefined reference and selects the pinned glibc definition. -/
theorem resolve_unlock (tail : List Silmaril.X86.Link.Blob) :
    Dyn.resolve (scope tail) unlockRef true =
      some (some (1, glibcDefinition)) :=
  Proofs.Elf.Corpus.SqliteMutex.Unlock.EagerBinding.resolve_unlock tail

/-- The SQLite relocation computes an address relative to the supplied glibc object. -/
theorem eager_slot_value (tail : List Silmaril.X86.Link.Blob) :
    ∃ d, Dyn.finfo Sqlite = some d ∧
      Dyn.relocVal (Dyn.resolve (scope tail)) Sqlite d jumpSlot =
        some (.addr 1 0xa1b50) :=
  Proofs.Elf.Corpus.SqliteMutex.Unlock.EagerBinding.eager_slot_value tail

/-- With the two objects' bases supplied, the relocation word is the glibc base plus the symbol offset. -/
theorem unlock_word (tail : List Blob) (sqliteBase glibcBase : Word) (otherBases : List Word)
    (ifunc : Word → Option Word) (resolver : Word) :
    ∃ d, Dyn.finfo Sqlite = some d ∧
      (Dyn.relocVal (Dyn.resolve (scope tail)) Sqlite d jumpSlot).bind
        (Dyn.Val.word (sqliteBase :: glibcBase :: otherBases) ifunc resolver) =
          some (some (glibcBase + 0xa1b50#64)) :=
  Proofs.Elf.Corpus.SqliteMutex.Unlock.EagerBinding.unlock_word tail sqliteBase glibcBase otherBases ifunc resolver

/-- The pinned DT_RELA table contains the indicated absolute symbol relocation. -/
theorem absolute_relocation :
    readAbsoluteReloc.run
      (blobRead Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.F) = some absoluteReloc :=
  Proofs.Elf.Corpus.SqliteMutex.Unlock.EagerBinding.absolute_relocation

end Silmaril.Elf.Corpus.SqliteMutex.Unlock.EagerBinding
