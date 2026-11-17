module

public import Silmaril.Machine.Region.Defs
public import Silmaril.Formats.ELF.Reader

/-! # ELF layout adapter

Uses the existing ELF64 record readers. Mapping is structural; its connection
to execution requires a loader/placement and code-preservation proof. ET_REL
section offsets are not VAs. No relocations or function boundaries are guessed.
-/

@[expose] public section
namespace Silmaril.Elf.Region
open Silmaril.Machine.Region
open Silmaril.Formats.ELF

/-- Only file-backed bytes of executable PT_LOAD segments. Zero-filled tails
belong to the loader's memory model, not to file code ranges. -/
def executableMapping (header : ProgramHeader) : Option Mapping :=
  if header.kind = 1 ∧ header.flags % 2 = 1 then
    some ⟨⟨.virtual, ⟨header.virtualAddress, header.virtualAddress + header.fileSize,
      Nat.le_add_right _ _⟩⟩, header.offset⟩
  else none

/-- Section-relative code mapping, including ET_REL. SHT_NOBITS is excluded. -/
def sectionMapping (index : Nat) (header : SectionHeader) : Option Mapping :=
  if header.flags / 4 % 2 = 1 ∧ header.kind ≠ 8 then
    some ⟨⟨.section index, ⟨0, header.size, Nat.zero_le _⟩⟩, header.offset⟩
  else none

/-- Parsed metadata alone is not certified to describe bytes; callers cite the
reader/parser theorem or existing `Elf.Parses`/`Staged.LayoutIs` certificate. -/
def object (source : ByteSource) (headers : List ProgramHeader) : BinaryObject :=
  ⟨source, headers.filterMap executableMapping⟩

end Silmaril.Elf.Region
