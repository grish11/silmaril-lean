module

public import Silmaril.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile.Defs
import Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile.Run

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile

open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So (F)
open Silmaril.Process (Memory)
open Silmaril.X86 (Word)

/-- Exact file bytes in the pinned read-only executable `PT_LOAD`. -/
theorem file_codeAt : Silmaril.Elf.CodeAt F 0x10060 slice :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile.file_codeAt

/-- Zero is a valid placement in the ELF file model. -/
theorem file_placement_zero : Silmaril.Elf.Placement F 0 :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile.file_placement_zero

/-- The checked file span can be backed by readable and executable abstract memory. -/
theorem file_slice_has_executable_mapping :
    Silmaril.Elf.CodeAt F 0x10060 slice ∧
      ∃ memory : Memory, Silmaril.X86.Ext.Loaded memory 0x10060 slice ∧
        memory.readBytes 0x10060 slice.length = some slice :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile.file_slice_has_executable_mapping

/-- The checked slice is fetchable at every valid placement with an independently
supplied read-only mapping. The runtime address is non-wrapping. -/
theorem fetch_of_readOnly_image {base : Word} {memory : Memory}
    (placement : Silmaril.Elf.Placement F base.toNat)
    (image : Silmaril.Elf.Link.ElfBind.RoLoaded F base memory) :
    Silmaril.X86.Ext.Loaded memory (base + 0x10060) slice ∧
      (base + 0x10060).toNat = base.toNat + 0x10060 :=
  Silmaril.Proofs.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile.fetch_of_readOnly_image placement image

end Silmaril.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile
