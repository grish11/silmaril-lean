module

public import Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationValue.Defs
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Bytes
public import Silmaril.Elf.Link.Dyn.Loader.Defs
import Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage.Thms

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationValue

open Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage (relocation_spans)
open Silmaril.Elf.Link.Dyn (finfo frun)
open Silmaril.Elf.Link.DynElf.Elf (Rela relas)
open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So (F)
open Silmaril.X86 (Word)

/-- Unsigned representative of the integer sum reduced modulo 2^64. -/
theorem abs64_toNat (resolved : Word) (addend : Int) :
    (abs64 resolved addend).toNat = (((resolved.toNat : Int) + addend) % (2 ^ 64 : Nat)).toNat := by
  have sum : BitVec.ofInt 64 ((resolved.toNat : Int) + addend) = abs64 resolved addend := by
    simp [abs64, BitVec.ofInt_add]
  rw [← sum, BitVec.toNat_ofInt]

/-- The actual pinned row has addend zero, so its value is the supplied
symbol word for any hypothetical resolution. -/
theorem pinned_value (resolved : Word) :
    let row : Rela := ⟨0x10e520, 1, 195, 0⟩
    ∃ info main plt, finfo F = some info ∧ frun F (relas info) = some (main, plt) ∧
      row ∈ main ∧ abs64 resolved row.addend = resolved := by
  obtain ⟨info, main, plt, hinfo, htables, _, _, _, hrow, _⟩ := relocation_spans
  exact ⟨info, main, plt, hinfo, htables, hrow, by simp [abs64]⟩

end Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationValue
