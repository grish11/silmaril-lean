module

public import Silmaril.Elf.Region.Defs
public import Silmaril.Machine.Region.X86.Thms
public import Silmaril.Process.LPS.ELFImage
public import Silmaril.X86.Link.FnSpec.Defs

/-! # Placing x86 region listings in checked ELF loader images

Uses the existing byte-exact `ELFImage` and `ImageLoaded` contract. Loading is
an explicit premise, not inferred from parsed headers. The window may include
loader-established zero fill; the file-only mapping in `Elf.Region` continues
to exclude it. Decoding and code preservation remain separate obligations.
-/

@[expose] public section
namespace Silmaril.Elf.Region.X86

/-- A half-open window of the existing loader segment, in virtual addresses. -/
def window (segment : Silmaril.Process.LPS.Segment) (offset length : Nat) :
    Silmaril.X86.Decompile.Region :=
  ⟨segment.base + offset, (segment.bytes.drop offset).take length⟩

end Silmaril.Elf.Region.X86
