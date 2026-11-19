module
public import Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Source.Defs
public import Silmaril.Data.IncludeBytes.Kernel
public import Silmaril.Elf.Staged.Reader.Thms
@[expose] public section
namespace Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Source.Projection
noncomputable def tu : ByteArray := include_bytes "../../../../../../corpus/darkhttpd/semantic-inputs/1.17/default/x86_64/O0/needs-logencoding/translation-unit.i"
kbytes_def TU of_include tu
noncomputable def original : ByteArray := include_bytes "../../../../../../corpus/darkhttpd/upstream/darkhttpd-1.17/darkhttpd.c"
kbytes_def Original of_include original
noncomputable def closure : ByteArray := include_bytes "../../../../../../corpus/darkhttpd/semantic-inputs/1.17/default/x86_64/O0/needs-logencoding/context.c"
kbytes_def Closure of_include closure
def exact : Prop :=
  Silmaril.Elf.Staged.Reader.kread TU 175434 110 = some 3937359440334897771536440393708149289570249704514333021773434955360689784272495245190100185776770112473930682318015440510180331464878879943881599316783570625487606710253287980289112255787820146651878362786249383172724006994469857383796255453321029807122234445231219 ∧
  Silmaril.Elf.Staged.Reader.kread Original 42815 110 = some 3937359440334897771536440393708149289570249704514333021773434955360689784272495245190100185776770112473930682318015440510180331464878879943881599316783570625487606710253287980289112255787820146651878362786249383172724006994469857383796255453321029807122234445231219 ∧
  Silmaril.Elf.Staged.Reader.kread Closure 0 111 = some 84548707575049443418560943707385610001064287490787758639443220878620257435139935960890975412775242386441581285537181803865030728117510340095636204184785825402768289693499913372246436119988632074908749839258903863786131644438250640287604375992724789037093331383972979
end Silmaril.Elf.Corpus.DarkhttpdLogEncoding.Source.Projection
