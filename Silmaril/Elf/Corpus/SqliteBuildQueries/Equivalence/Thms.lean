module
public import Silmaril.Elf.Corpus.SqliteBuildQueries.Equivalence.Defs
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O0.Unstripped.Libsqlite3So.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Stripped.Libsqlite3So.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O0.Unstripped.Libsqlite3So.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O2.Unstripped.Libsqlite3So.Thms
public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3504.Default.X8664.O0.Unstripped.Libsqlite3So.Thms

@[expose] public section
namespace Silmaril.Elf.Corpus.SqliteBuildQueries.Equivalence
open Silmaril.Elf.Staged.Reader

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O0.Unstripped.Libsqlite3So in
theorem defaultO0Version_at : Silmaril.Elf.CodeAt F defaultO0Version.base.toNat defaultO0Version.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O0.Unstripped.Libsqlite3So in
theorem defaultO0Threadsafe_at : Silmaril.Elf.CodeAt F defaultO0Threadsafe.base.toNat defaultO0Threadsafe.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So in
theorem defaultO2Version_at : Silmaril.Elf.CodeAt F defaultO2Version.base.toNat defaultO2Version.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So in
theorem defaultO2Threadsafe_at : Silmaril.Elf.CodeAt F defaultO2Threadsafe.base.toNat defaultO2Threadsafe.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Stripped.Libsqlite3So in
theorem defaultStrippedVersion_at : Silmaril.Elf.CodeAt F defaultStrippedVersion.base.toNat defaultStrippedVersion.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Stripped.Libsqlite3So in
theorem defaultStrippedThreadsafe_at : Silmaril.Elf.CodeAt F defaultStrippedThreadsafe.base.toNat defaultStrippedThreadsafe.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O0.Unstripped.Libsqlite3So in
theorem smallO0Version_at : Silmaril.Elf.CodeAt F smallO0Version.base.toNat smallO0Version.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O0.Unstripped.Libsqlite3So in
theorem smallO0Threadsafe_at : Silmaril.Elf.CodeAt F smallO0Threadsafe.base.toNat smallO0Threadsafe.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O2.Unstripped.Libsqlite3So in
theorem smallO2Version_at : Silmaril.Elf.CodeAt F smallO2Version.base.toNat smallO2Version.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O2.Unstripped.Libsqlite3So in
theorem smallO2Threadsafe_at : Silmaril.Elf.CodeAt F smallO2Threadsafe.base.toNat smallO2Threadsafe.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3504.Default.X8664.O0.Unstripped.Libsqlite3So in
theorem priorO0Version_at : Silmaril.Elf.CodeAt F priorO0Version.base.toNat priorO0Version.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3504.Default.X8664.O0.Unstripped.Libsqlite3So in
theorem priorO0Threadsafe_at : Silmaril.Elf.CodeAt F priorO0Threadsafe.base.toNat priorO0Threadsafe.code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)



open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O0.Unstripped.Libsqlite3So in
theorem defaultO0Version_symbol :
    s3_311.name = ("sqlite3_libversion_number".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_311.raw.value = 958625 ∧ s3_311.raw.size = 11 ∧ s3_311.kind = 2 := by
  decide +kernel

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O0.Unstripped.Libsqlite3So in
theorem defaultO0Threadsafe_symbol :
    s3_334.name = ("sqlite3_threadsafe".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_334.raw.value = 958636 ∧ s3_334.raw.size = 11 ∧ s3_334.kind = 2 := by
  decide +kernel

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So in
theorem defaultO2Version_symbol :
    s3_311.name = ("sqlite3_libversion_number".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_311.raw.value = 79904 ∧ s3_311.raw.size = 6 ∧ s3_311.kind = 2 := by
  decide +kernel

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So in
theorem defaultO2Threadsafe_symbol :
    s3_334.name = ("sqlite3_threadsafe".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_334.raw.value = 79920 ∧ s3_334.raw.size = 6 ∧ s3_334.kind = 2 := by
  decide +kernel

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Stripped.Libsqlite3So in
theorem defaultStrippedVersion_symbol :
    s3_311.name = ("sqlite3_libversion_number".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_311.raw.value = 79904 ∧ s3_311.raw.size = 6 ∧ s3_311.kind = 2 := by
  decide +kernel

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Stripped.Libsqlite3So in
theorem defaultStrippedThreadsafe_symbol :
    s3_334.name = ("sqlite3_threadsafe".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_334.raw.value = 79920 ∧ s3_334.raw.size = 6 ∧ s3_334.kind = 2 := by
  decide +kernel

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O0.Unstripped.Libsqlite3So in
theorem smallO0Version_symbol :
    s3_294.name = ("sqlite3_libversion_number".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_294.raw.value = 934561 ∧ s3_294.raw.size = 11 ∧ s3_294.kind = 2 := by
  decide +kernel

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O0.Unstripped.Libsqlite3So in
theorem smallO0Threadsafe_symbol :
    s3_315.name = ("sqlite3_threadsafe".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_315.raw.value = 934572 ∧ s3_315.raw.size = 11 ∧ s3_315.kind = 2 := by
  decide +kernel

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O2.Unstripped.Libsqlite3So in
theorem smallO2Version_symbol :
    s3_294.name = ("sqlite3_libversion_number".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_294.raw.value = 160048 ∧ s3_294.raw.size = 6 ∧ s3_294.kind = 2 := by
  decide +kernel

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Small.X8664.O2.Unstripped.Libsqlite3So in
theorem smallO2Threadsafe_symbol :
    s3_315.name = ("sqlite3_threadsafe".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_315.raw.value = 160064 ∧ s3_315.raw.size = 3 ∧ s3_315.kind = 2 := by
  decide +kernel

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3504.Default.X8664.O0.Unstripped.Libsqlite3So in
theorem priorO0Version_symbol :
    s3_305.name = ("sqlite3_libversion_number".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_305.raw.value = 921142 ∧ s3_305.raw.size = 11 ∧ s3_305.kind = 2 := by
  decide +kernel

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3504.Default.X8664.O0.Unstripped.Libsqlite3So in
theorem priorO0Threadsafe_symbol :
    s3_328.name = ("sqlite3_threadsafe".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_328.raw.value = 921153 ∧ s3_328.raw.size = 11 ∧ s3_328.kind = 2 := by
  decide +kernel

end Silmaril.Elf.Corpus.SqliteBuildQueries.Equivalence
