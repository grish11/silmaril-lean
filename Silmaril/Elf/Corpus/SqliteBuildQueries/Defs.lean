module
public import Silmaril.Elf.Staged.Corpus.Sqlite.X8664.Libsqlite3So.Thms
@[expose] public section
namespace Silmaril.Elf.Corpus.SqliteBuildQueries
inductive Getter where
  | versionNumber | threadsafe
  deriving DecidableEq, Repr
def Getter.name : Getter → String
  | .versionNumber => "sqlite3_libversion_number"
  | .threadsafe => "sqlite3_threadsafe"
def Getter.address : Getter → Nat
  | .versionNumber => 79904
  | .threadsafe => 79920
def Getter.code : Getter → List (BitVec 8)
  | .versionNumber => [0xb8, 0xb1, 0x99, 0x2e, 0, 0xc3]
  | .threadsafe => [0xb8, 1, 0, 0, 0, 0xc3]
end Silmaril.Elf.Corpus.SqliteBuildQueries
