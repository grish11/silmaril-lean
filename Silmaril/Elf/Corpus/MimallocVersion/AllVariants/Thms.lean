module

public import Silmaril.Elf.Corpus.MimallocVersion.AllVariants.Defs

@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocVersion.AllVariants

open Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O0.Stripped.LibmimallocSo21 in
theorem codeO0Stripped_at : Silmaril.Elf.CodeAt F 0x11e2f codeO0Stripped :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O0.Unstripped.LibmimallocSo21 in
theorem codeO0Unstripped_at : Silmaril.Elf.CodeAt F 0x11e2f codeO0Unstripped :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O1.Stripped.LibmimallocSo21 in
theorem codeO1Stripped_at : Silmaril.Elf.CodeAt F 0xd5b6 codeO1Stripped :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O1.Unstripped.LibmimallocSo21 in
theorem codeO1Unstripped_at : Silmaril.Elf.CodeAt F 0xd5b6 codeO1Unstripped :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O3.Stripped.LibmimallocSo21 in
theorem codeO3Stripped_at : Silmaril.Elf.CodeAt F 0xfaf0 codeO3Stripped :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.O3.Unstripped.LibmimallocSo21 in
theorem codeO3Unstripped_at : Silmaril.Elf.CodeAt F 0xfaf0 codeO3Unstripped :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.Og.Stripped.LibmimallocSo21 in
theorem codeOgStripped_at : Silmaril.Elf.CodeAt F 0xd08b codeOgStripped :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

open Silmaril.Elf.Staged.CorpusVariants.Mimalloc.N219.Default.X8664.Og.Unstripped.LibmimallocSo21 in
theorem codeOgUnstripped_at : Silmaril.Elf.CodeAt F 0xd08b codeOgUnstripped :=
  Silmaril.Elf.Staged.Reader.codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)

end Silmaril.Elf.Corpus.MimallocVersion.AllVariants
