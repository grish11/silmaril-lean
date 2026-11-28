module

public import Silmaril.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile.Thms
public import Silmaril.Machine.Region.X86.SqliteStrLength.Thms
import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Thms

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile.CFG

open Silmaril.Elf.Link.ElfBind (RoLoaded)
open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So
open Silmaril.Machine.Region.X86.SqliteStrLength
open Silmaril.X86

/-- The pinned dynamic symbol is a defined global function, and its entire
extent is the executable file span used by the CFG proof. -/
theorem symbol_code_at :
    ∃ s, SymbolAt F .dynsym 288 s ∧
      s.name = "sqlite3_str_length".toUTF8.data.toList.map UInt8.toBitVec ∧
      s.binding = 1 ∧ s.kind = 2 ∧ s.raw.sectionIndex ≠ 0 ∧
      s.raw.value = 0x10060 ∧ s.raw.size = code.length ∧ CodeAt F s.raw.value code :=
  ⟨s3_288, ⟨_, parses, by decide +kernel⟩, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, rfl, rfl, file_codeAt⟩

/-- At the pinned function's relocated entry, a read-only image and the
return-slot and guarded field-read premises suffice for a first return
whose branch, payload, and memory agree with the CFG. -/
theorem firstReturn_of_readOnly_image {base : Word} {entry : MState}
    (placement : Placement F base.toNat) (image : RoLoaded F base entry.memory)
    (atEntry : entry.core.rip = base + 0x10060) (saved : ReturnSlot entry) (ready : DataReady entry) :
    ∃ final, FnContract.FirstReturn Open.isa entry final ∧ Bridge entry final :=
  bridge_exists (atEntry.symm ▸ (fetch_of_readOnly_image placement image).1) saved ready

/-- Every modeled first return from the same admitted entry agrees with the CFG. -/
theorem agrees_of_firstReturn {base : Word} {entry final : MState}
    (placement : Placement F base.toNat) (image : RoLoaded F base entry.memory)
    (atEntry : entry.core.rip = base + 0x10060) (saved : ReturnSlot entry) (ready : DataReady entry)
    (actual : FnContract.FirstReturn Open.isa entry final) : Bridge entry final :=
  bridge_of_firstReturn (atEntry.symm ▸ (fetch_of_readOnly_image placement image).1) saved ready actual

end Silmaril.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile.CFG
