module

public import Silmaril.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile.Defs
import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Thms
import Silmaril.Elf.BindEq.Thms

public section

namespace Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile

open Silmaril.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile (slice)
open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So
open Silmaril.Elf.Staged.Reader
open Silmaril.Process (Access Memory)
open Silmaril.X86 (Word)

theorem file_codeAt : Silmaril.Elf.CodeAt F 0x10060 slice :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

theorem file_placement_zero : Silmaril.Elf.Placement F 0 := by
  refine ⟨_, parses, .inr ⟨rfl, rfl⟩, ?_⟩
  decide +kernel

/-- Abstract memory for the eleven file-backed bytes. The pinned segment has
read and execute permissions. The witness maps just the selected span. -/
private def sliceMemory (executable : Bool) : Memory :=
  ⟨[⟨0x10060, slice.length, ⟨true, false, executable⟩⟩], Memory.install ∅ 0x10060 slice⟩

private theorem slice_read (access : Access)
    (permitted : (sliceMemory true).Permitted access 0x10060 slice.length) :
    (sliceMemory true).readWith access 0x10060 slice.length = some slice :=
  Memory.readWith_eq _ _ _ _ permitted (fun index bound => Memory.install_get _ _ _ index bound)

theorem file_slice_has_executable_mapping :
    Silmaril.Elf.CodeAt F 0x10060 slice ∧
      ∃ memory : Memory, Silmaril.X86.Ext.Loaded memory 0x10060 slice ∧
        memory.readBytes 0x10060 slice.length = some slice :=
  ⟨file_codeAt, sliceMemory true, slice_read .execute (by decide +kernel),
    slice_read .read (by decide +kernel)⟩

-- Backing and read permission alone cannot supply the x86 fetch premise.
example : (sliceMemory false).fetchBytes 0x10060 slice.length = none := by
  have denied : (sliceMemory false).checkSpan .execute 0x10060 slice.length = false := by
    decide +kernel
  simp [Memory.fetchBytes, Memory.readWith, denied]

/-- Use the existing read-only mapping relation for a consumer-supplied
image at a general load bias. The file fact is established above. -/
theorem fetch_of_readOnly_image {base : Word} {memory : Memory}
    (placement : Silmaril.Elf.Placement F base.toNat)
    (image : Silmaril.Elf.Link.ElfBind.RoLoaded F base memory) :
    Silmaril.X86.Ext.Loaded memory (base + 0x10060) slice ∧
      (base + 0x10060).toNat = base.toNat + 0x10060 :=
  Silmaril.Proofs.Elf.BindEq.directCall_of_roLoaded' parses rfl rfl file_codeAt placement image

end Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile
