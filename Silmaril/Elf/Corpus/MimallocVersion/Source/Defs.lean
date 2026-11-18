module

public import Silmaril.Elf.Staged.Reader.Thms
public import Silmaril.Data.IncludeBytes.Kernel

/-! Exact source bytes from pinned canonical-ELF preprocessing. The theorem binds the
closed definition's byte span; it does not verify the external preprocessor or claim that
the entire translation unit is supported by the Cerberus frontend. -/

@[expose] public section

namespace Silmaril.Elf.Corpus.MimallocVersion.Source

noncomputable def translationUnit : ByteArray := include_bytes "../../../../../corpus/mimalloc/semantic-inputs/2.1.9/default/x86_64/O2/mi_version/options.i"
kbytes_def TU of_include translationUnit

def cText : String := "int mi_version(void) {\n  return 219;\n}\n"

/-- The exact closed definition is present in the actual preprocessed translation unit. -/
theorem projection_bytes : Silmaril.Elf.Staged.Reader.kread TU 296176 39 =
    some (Silmaril.X86.Link.Blob.valueLE (cText.toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat)) := by
  decide +kernel

end Silmaril.Elf.Corpus.MimallocVersion.Source
