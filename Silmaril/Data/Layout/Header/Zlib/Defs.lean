module

public import Silmaril.Machine.Abi.Conformance.Defs

/-!
# zlib 1.3.1's checksum API, for the subset reader

`examples/headers/zlib-1.3.1/zlib.h` is a verbatim excerpt of zlib 1.3.1's `zlib.h` (generated
and checked by `examples/headers/recipe.sh` from the release tarball, SHA-256
`9a93b2b7…df23`): the declarations of `zlibVersion`, `zlibCompileFlags`, `adler32`,
`adler32_z`, `adler32_combine`, `crc32`, `crc32_z`, `crc32_combine`, `crc32_combine_gen`,
`crc32_combine_op` and `get_crc_table`, with their `ZEXTERN`/`ZEXPORT` lines, the original
line numbers and the zlib licence. The real `zlib.h` and `zconf.h` use `#if` expressions,
which the subset reader refuses; the excerpt includes `"zconf.h"`, which is one of two resolved
configurations: `zconf-solo.h` (`-DZ_SOLO`: `z_size_t` is `unsigned long`, `z_crc_t` is
`unsigned long`) or `zconf-hosted.h` (`z_size_t` is `size_t`, `z_crc_t` is `unsigned`).
Each configuration line cites the `zconf.h` line it resolves.

The clang route reads the real files (`Header.Import.Pinned.zlibSolo`, `zlibHosted`);
`Header.Import.Thms` compares the two.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Header.Zlib

/-- The excerpt of `zlib.h`. -/
def zlibH : String := include_str "../../../../../examples/headers/zlib-1.3.1/zlib.h"
/-- `zconf.h` resolved under `-DZ_SOLO`. -/
def zconfSolo : String := include_str "../../../../../examples/headers/zlib-1.3.1/zconf-solo.h"
/-- `zconf.h` resolved for a hosted build. -/
def zconfHosted : String := include_str "../../../../../examples/headers/zlib-1.3.1/zconf-hosted.h"

/-- The files of the excerpt under `-DZ_SOLO`. -/
def soloFiles : List (String × String) := [("zconf.h", zconfSolo), ("zlib.h", zlibH)]
/-- The files of the excerpt, hosted. -/
def hostedFiles : List (String × String) := [("zconf.h", zconfHosted), ("zlib.h", zlibH)]

/-- The checksum API of `zlib.h` under `-DZ_SOLO`, for `Declares`. -/
def solo : Silmaril.Machine.Abi.Conformance.HeaderSrc := ⟨soloFiles, "zlib.h"⟩
/-- The checksum API of `zlib.h`, hosted, for `Declares`. -/
def hosted : Silmaril.Machine.Abi.Conformance.HeaderSrc := ⟨hostedFiles, "zlib.h"⟩

/-- The functions the excerpt declares, in order. -/
def checksumApi : List String :=
  ["zlibVersion", "zlibCompileFlags", "adler32", "adler32_z", "crc32", "crc32_z",
    "crc32_combine_op", "adler32_combine", "crc32_combine", "crc32_combine_gen", "get_crc_table"]

open Silmaril.Data.Layout (CTy IntKind)

/-- `uLong`. -/
def uLong : CTy := .typedef "uLong" (.int .long .unsigned)

/-- `const Bytef *` (qualifiers dropped). -/
def bytefPtr : CTy := .ptr (.typedef "Bytef" (.typedef "Byte" (.int .char .unsigned)))

/-- `uLong f(uLong, const Bytef *, z_size_t)` (`adler32_z`, `crc32_z`) with
`typedef size_t z_size_t;` and `size_t` of integer kind `k`. -/
def sizedProto (k : IntKind) : Silmaril.Data.Layout.Header.CProto :=
  ⟨uLong, [uLong, bytefPtr, .typedef "z_size_t" (.typedef "size_t" (.int k .unsigned))], false⟩

end Silmaril.Data.Layout.Header.Zlib

end
