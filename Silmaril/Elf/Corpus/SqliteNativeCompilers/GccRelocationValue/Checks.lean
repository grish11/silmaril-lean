module

import Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationValue.Thms
import Silmaril.Elf.Link.ElfBind.Defs
import Silmaril.Formats.ELF.Reader

open Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationValue
open Silmaril.Elf.Link.Dyn (finfo frun)
open Silmaril.Elf.Link.DynElf.Elf (Rela relas)
open Silmaril.Elf.Link.ElfBind (leBytes)
open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So (F)
open Silmaril.Formats.ELF (signed64)

example :
    signed64 0xfffffffffffffffc = -4 ∧
      signed64 0x8000000000000000 = -(2 ^ 63) ∧
      signed64 0x7fffffffffffffff = 2 ^ 63 - 1 := by decide +kernel

example : abs64 0x1020 4 = 0x1024 := by decide +kernel
example : abs64 0x1020 (signed64 0xfffffffffffffffc) = 0x101c := by decide +kernel
example : abs64 0xffffffffffffffff 1 = 0 := by decide +kernel
example : abs64 0 (signed64 0xffffffffffffffff) = 0xffffffffffffffff := by decide +kernel
example : abs64 1 (signed64 0x8000000000000000) = 0x8000000000000001 := by decide +kernel
example : abs64 1 (signed64 0x7fffffffffffffff) = 0x8000000000000000 := by decide +kernel

-- Supply a hypothetical address for symbol 195 and check the word bytes.
example :
    let row : Rela := ⟨0x10e520, 1, 195, 0⟩
    ∃ info main plt, finfo F = some info ∧ frun F (relas info) = some (main, plt) ∧
      row ∈ main ∧ leBytes (abs64 0x00007f23000374e0 row.addend).toNat 8 =
        [0xe0, 0x74, 0x03, 0x00, 0x23, 0x7f, 0x00, 0x00] := by
  obtain ⟨info, main, plt, hinfo, htables, hrow, hval⟩ := pinned_value 0x00007f23000374e0
  exact ⟨info, main, plt, hinfo, htables, hrow, by rw [hval]; decide +kernel⟩
