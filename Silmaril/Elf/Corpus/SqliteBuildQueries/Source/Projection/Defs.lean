module
public import Silmaril.Elf.Corpus.SqliteBuildQueries.Source.Defs
public import Silmaril.Data.IncludeBytes.Kernel
public import Silmaril.Elf.Staged.Reader.Thms

/-! Exact byte projection only. This does not prove the GCC preprocessing pass
or the semantic adequacy of selecting a declaration closure from a full TU. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.SqliteBuildQueries.Source.Projection
noncomputable def translationUnit : ByteArray := include_bytes "../../../../../../corpus/sqlite/semantic-inputs/3.54.1/default/x86_64/O2/build-queries/translation-unit.i"
kbytes_def TU of_include translationUnit

/-- Byte spans and their little-endian values, in closure order. -/
def pieces : List (Nat × Nat × Nat) := [
  (3240508, 54, 5420824996144520074012019130918658243481609710628745875057600348334548730011188620067856895549484347869296226624148916884798205545),
  (3240569, 41, 267267307086117117058587664041132228405027009882734459054740024435770635498571293048633683449507433)
]
noncomputable def contextBytes : ByteArray := include_bytes "../../../../../../corpus/sqlite/semantic-inputs/3.54.1/default/x86_64/O2/build-queries/context.c"
kbytes_def Closure of_include contextBytes

/-- Concatenate each selected byte span and a newline, without string encoding. -/
def joined : Nat × Nat := pieces.foldl (fun (size, value) (_, len, bytes) =>
  (size + len + 1, value + bytes * 256^size + 10 * 256^(size + len))) (0, 0)

def exact : Prop :=
  (pieces.all fun (offset, len, bytes) =>
    Silmaril.Elf.Staged.Reader.kread TU offset len == some bytes) = true ∧
  Silmaril.Elf.Staged.Reader.kread Closure 0 joined.1 = some joined.2
end Silmaril.Elf.Corpus.SqliteBuildQueries.Source.Projection
