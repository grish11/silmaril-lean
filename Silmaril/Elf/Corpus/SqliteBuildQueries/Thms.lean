module
public import Silmaril.Elf.Corpus.SqliteBuildQueries.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.SqliteBuildQueries
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So
theorem version_at : Silmaril.Elf.CodeAt F Getter.versionNumber.address Getter.versionNumber.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem version_symbol : s3_311.name = (Getter.versionNumber.name.toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_311.raw.value = Getter.versionNumber.address ∧ s3_311.raw.size = 6 ∧ s3_311.kind = 2 := by decide +kernel
theorem threadsafe_at : Silmaril.Elf.CodeAt F Getter.threadsafe.address Getter.threadsafe.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem threadsafe_symbol : s3_334.name = (Getter.threadsafe.name.toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_334.raw.value = Getter.threadsafe.address ∧ s3_334.raw.size = 6 ∧ s3_334.kind = 2 := by decide +kernel
end Silmaril.Elf.Corpus.SqliteBuildQueries
