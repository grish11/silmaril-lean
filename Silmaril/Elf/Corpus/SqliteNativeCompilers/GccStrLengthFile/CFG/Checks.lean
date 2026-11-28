module

import Silmaril.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile.CFG.Thms
import Silmaril.Elf.Facts.Thms
import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Thms

open Silmaril.Elf
open Silmaril.Elf.Staged.Reader
open Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So
open Silmaril.Machine.Region.X86

-- Moving the start by one, while keeping the span length, cannot certify
-- the original CFG code against this artifact.
example : ¬ CodeAt F 0x10061 SqliteStrLength.code := by
  let shifted : List (BitVec 8) := [0xc0, 0x48, 0x85, 0xff, 0x74, 0x03, 0x8b, 0x47, 0x18, 0xc3, 0x0f]
  have actual : CodeAt F 0x10061 shifted :=
    codeAt_of_kbytes K.wf_true K.toByteArray_eq parses (ph := ph1)
      (by decide +kernel) (by decide +kernel)
  intro claimed
  have different : SqliteStrLength.code ≠ shifted := by decide +kernel
  exact different (claimed.unique actual rfl)
