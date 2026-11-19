module
public import Silmaril.Elf.Corpus.SqliteGlobalVersion.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.SqliteGlobalVersion
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So
theorem function_at : Silmaril.Elf.CodeAt F functionAddress functionCode :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem function_symbol :
    s3_191.name = ("sqlite3_libversion".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_191.raw.value = functionAddress ∧ s3_191.raw.size = 8 ∧ s3_191.kind = 2 := by decide +kernel
theorem global_symbol :
    s3_233.name = ("sqlite3_version".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat) ∧
    s3_233.raw.value = globalAddress ∧ s3_233.raw.size = 7 ∧ s3_233.kind = 1 := by decide +kernel
/-- Raw read-only data evidence, separate from executable `CodeAt`. -/
theorem global_file_bytes : PartIs F [⟨972146, 7⟩]
    (Silmaril.Elf.Link.DynElf.Rd.read 972146 7 .pure) 54074514157107 :=
  partIs_of_kbytes K.wf_true K.toByteArray_eq (by decide +kernel)
/-- The actual ELF64 RELA record: GOT offset, symbol 233/type 6, zero addend.
This is file evidence, not a theorem about dynamic-loader resolution or interposition. -/
theorem relocation_file_bytes : PartIs F [⟨53296, 24⟩]
    (Silmaril.Elf.Link.DynElf.Rd.read 53296 24 .pure) 18460161865934271123737998847944 :=
  partIs_of_kbytes K.wf_true K.toByteArray_eq (by decide +kernel)
end Silmaril.Elf.Corpus.SqliteGlobalVersion
