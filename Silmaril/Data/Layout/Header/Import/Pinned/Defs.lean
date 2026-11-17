module

public import Silmaril.Data.Layout.Header.Import.Defs

/-!
# The pinned clang imports

Each artifact of `examples/headers/clang/` (produced and checked byte for byte by
`examples/headers/recipe.sh --check`) with its provenance file, imported by
`Imported.ofJson`. The JSON is the output of the pinned clang 18.1.8
(`silkeh/clang@sha256:3914c93a…`, see each `.prov`), filtered to the declarations of the
header's own files; the import normalizes it and does not assume clang correct.

| value | header | flags (see the `.prov`) | kept files |
| --- | --- | --- | --- |
| `arith` | `elf-ladder/01-leaf-arith/arith.h` | the ladder's: `-ffreestanding -fno-builtin -I../common` | `arith.h`, `../common/rt.h` |
| `probe` | `headers/probe/probe.h` | `-ffreestanding -fno-builtin` | `probe.h` |
| `zlibSolo` | zlib 1.3.1 `zlib.h` | rung 03's: `-ffreestanding -fno-builtin -DZ_SOLO` | `zlib.h`, `./zconf.h` |
| `zlibHosted` | zlib 1.3.1 `zlib.h` | hosted (the image's glibc) | `zlib.h`, `./zconf.h` |
| `glibcString` | glibc `/usr/include/string.h` | hosted | `/usr/include/string.h` |

All use `-std=gnu11`. The target is `x86_64-unknown-linux-gnu` throughout.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Import.Pinned

def arithJson : String :=
  include_str "../../../../../../examples/headers/clang/arith.json"
def arithProv : String :=
  include_str "../../../../../../examples/headers/clang/arith.prov"
def probeJson : String :=
  include_str "../../../../../../examples/headers/clang/probe.json"
def probeProv : String :=
  include_str "../../../../../../examples/headers/clang/probe.prov"
def zlibSoloJson : String :=
  include_str "../../../../../../examples/headers/clang/zlib-solo.json"
def zlibSoloProv : String :=
  include_str "../../../../../../examples/headers/clang/zlib-solo.prov"
def zlibHostedJson : String :=
  include_str "../../../../../../examples/headers/clang/zlib-hosted.json"
def zlibHostedProv : String :=
  include_str "../../../../../../examples/headers/clang/zlib-hosted.prov"
def glibcStringJson : String :=
  include_str "../../../../../../examples/headers/clang/glibc-string.json"
def glibcStringProv : String :=
  include_str "../../../../../../examples/headers/clang/glibc-string.prov"

/-- `arith.h` and the `rt.h` it includes, as clang reads them. -/
def arith : Imported := .ofJson (.parse arithProv) arithJson
/-- The probe header. -/
def probe : Imported := .ofJson (.parse probeProv) probeJson
/-- zlib 1.3.1's `zlib.h` under `-DZ_SOLO`. -/
def zlibSolo : Imported := .ofJson (.parse zlibSoloProv) zlibSoloJson
/-- zlib 1.3.1's `zlib.h`, hosted. -/
def zlibHosted : Imported := .ofJson (.parse zlibHostedProv) zlibHostedJson
/-- glibc's `string.h`, hosted. -/
def glibcString : Imported := .ofJson (.parse glibcStringProv) glibcStringJson

/-! ## The same headers as text, for the subset reader -/

/-- `examples/elf-ladder/common/rt.h`. -/
def rtH : String :=
  include_str "../../../../../../examples/elf-ladder/common/rt.h"
/-- `examples/elf-ladder/01-leaf-arith/arith.h`. -/
def arithH : String :=
  include_str "../../../../../../examples/elf-ladder/01-leaf-arith/arith.h"
/-- The files of `arith.h`, as the subset reader takes them. -/
def arithFiles : List (String × String) := [("rt.h", rtH), ("arith.h", arithH)]

end Silmaril.Data.Layout.Header.Import.Pinned

end
