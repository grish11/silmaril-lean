module
public import Silmaril.Elf.Staged.Corpus.Mimalloc.X8664.LibmimallocSo21.Thms
@[expose] public section
namespace Silmaril.Elf.Corpus.MimallocOsGlobals
inductive Getter where
  | page | largePage
  deriving DecidableEq, Repr

def Getter.name : Getter → String
  | .page => "_mi_os_page_size"
  | .largePage => "_mi_os_large_page_size"
def Getter.address : Getter → Nat
  | .page => 62000
  | .largePage => 62016

def globalAddress : Nat := 142048
def pageCode : List (BitVec 8) := [0x48, 0x8b, 0x5, 0xa9, 0x38, 0x1, 0x0, 0xc3]
def largePageCode : List (BitVec 8) := [0x48, 0x8b, 0x5, 0xa1, 0x38, 0x1, 0x0, 0x48, 0x85, 0xc0, 0x48, 0xf, 0x44, 0x5, 0x8e, 0x38, 0x1, 0x0, 0xc3]
def Getter.code : Getter → List (BitVec 8)
  | .page => pageCode
  | .largePage => largePageCode
end Silmaril.Elf.Corpus.MimallocOsGlobals
