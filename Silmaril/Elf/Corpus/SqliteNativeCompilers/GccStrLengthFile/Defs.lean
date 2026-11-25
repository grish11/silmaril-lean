module

public import Silmaril.Elf.Staged.CorpusVariants.Sqlite.N3541.Default.X8664.O2.Unstripped.Libsqlite3So.Bytes
public import Silmaril.Elf.Link.ElfBind.Defs
public import Silmaril.Elf.Facts.Defs
public import Silmaril.X86.Ext.SymExec

@[expose] public section

namespace Silmaril.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile

/-- The pinned GCC 14, O2 SQLite `sqlite3_str_length` body at virtual address `0x10060`. -/
def slice : List (BitVec 8) := [0x31, 0xc0, 0x48, 0x85, 0xff, 0x74, 0x03, 0x8b, 0x47, 0x18, 0xc3]

end Silmaril.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile
