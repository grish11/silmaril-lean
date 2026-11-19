module
public import Silmaril.Elf.Corpus.CjsonInsert.Defs
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonInsert
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.CorpusVariants.Cjson.N1719.Default.X8664.O0.Unstripped.LibcjsonSo1
/-- The actual caller excerpt is real ELF code; helper identities remain separate. -/
theorem caller_code_at : Silmaril.Elf.CodeAt F address code :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem helper0_code_at : Silmaril.Elf.CodeAt F excerpts[0]!.1 excerpts[0]!.2 :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem helper1_code_at : Silmaril.Elf.CodeAt F excerpts[1]!.1 excerpts[1]!.2 :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
theorem helper2_code_at : Silmaril.Elf.CodeAt F excerpts[2]!.1 excerpts[2]!.2 :=
  codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
    (by decide +kernel) (by decide +kernel)
end Silmaril.Elf.Corpus.CjsonInsert
