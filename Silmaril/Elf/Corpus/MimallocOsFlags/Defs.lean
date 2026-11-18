module
public import Silmaril.Elf.Staged.Corpus.Mimalloc.X8664.LibmimallocSo21.Thms
@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocOsFlags
inductive Getter where
  | overcommit | virtualReserve
  deriving DecidableEq, Repr

def Getter.name : Getter → String
  | .overcommit => "_mi_os_has_overcommit"
  | .virtualReserve => "_mi_os_has_virtual_reserve"
def Getter.address : Getter → Nat
  | .overcommit => 61968
  | .virtualReserve => 61984
def Getter.code : Getter → List (BitVec 8)
  | .overcommit => [0x0f, 0xb6, 0x05, 0xf1, 0x38, 0x01, 0x00, 0xc3]
  | .virtualReserve => [0x0f, 0xb6, 0x05, 0xe3, 0x38, 0x01, 0x00, 0xc3]
def globalAddress : Nat := 142048
end Silmaril.Elf.Corpus.MimallocOsFlags
