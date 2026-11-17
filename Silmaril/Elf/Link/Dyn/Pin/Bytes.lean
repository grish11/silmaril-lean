module

public import Silmaril.Data.IncludeBytes
public import Silmaril.Formats.Bytes

/-! # The pinned executables of the dynamic-linking proofs, as bytes

Each file of `examples/dyn/pinned/` (built by `examples/dyn/pin.sh` from the C sources beside it,
sha256 in `examples/dyn/pins.txt`) as `include_bytes`, and the GNU `sha256sum` of
`examples/elf/pinned/` (see `examples/elf/README.md`). The proofs read them through `blob_of%`
(`Silmaril.Elf.Link.Dyn.Pin.Defs`). -/

@[expose] public section

namespace Silmaril.Elf.Link.Dyn.PinBytes

/-- `examples/dyn/hello/hello.c`, gcc. -/
noncomputable def helloGcc : Silmaril.Formats.Bytes := ⟨include_bytes "../../../../../examples/dyn/pinned/hello-gcc"⟩
/-- `examples/dyn/hello/hello.c`, clang. -/
noncomputable def helloClang : Silmaril.Formats.Bytes := ⟨include_bytes "../../../../../examples/dyn/pinned/hello-clang"⟩
/-- `examples/dyn/ret0/ret0.c`, gcc. -/
noncomputable def ret0Gcc : Silmaril.Formats.Bytes := ⟨include_bytes "../../../../../examples/dyn/pinned/ret0-gcc"⟩
/-- `examples/dyn/ret0/ret0.c`, clang. -/
noncomputable def ret0Clang : Silmaril.Formats.Bytes := ⟨include_bytes "../../../../../examples/dyn/pinned/ret0-clang"⟩
/-- `examples/dyn/ret42/ret42.c`, gcc. -/
noncomputable def ret42Gcc : Silmaril.Formats.Bytes := ⟨include_bytes "../../../../../examples/dyn/pinned/ret42-gcc"⟩
/-- `examples/dyn/ret42/ret42.c`, clang. -/
noncomputable def ret42Clang : Silmaril.Formats.Bytes := ⟨include_bytes "../../../../../examples/dyn/pinned/ret42-clang"⟩
/-- `examples/dyn/adder/adder.c`, gcc. -/
noncomputable def adderGcc : Silmaril.Formats.Bytes := ⟨include_bytes "../../../../../examples/dyn/pinned/adder-gcc"⟩
/-- `examples/dyn/adder/adder.c`, clang. -/
noncomputable def adderClang : Silmaril.Formats.Bytes := ⟨include_bytes "../../../../../examples/dyn/pinned/adder-clang"⟩
/-- `examples/dyn/ladder/cat-stdin.c`, gcc. -/
noncomputable def catStdinGcc : Silmaril.Formats.Bytes := ⟨include_bytes "../../../../../examples/dyn/pinned/cat-stdin-gcc"⟩
/-- `examples/dyn/ladder/cat-file.c`, gcc. -/
noncomputable def catFileGcc : Silmaril.Formats.Bytes := ⟨include_bytes "../../../../../examples/dyn/pinned/cat-file-gcc"⟩
/-- `examples/elf/pinned/gnu-sha256sum`: GNU coreutils 9.4 `sha256sum` (Ubuntu `coreutils`
9.4-3ubuntu6.3, amd64, unmodified; 39336 bytes, sha256
`4d2db56c867e5324e0084c9e897f6360d37517de77ac96f2bd31494223d69a60`). GPL-3.0-or-later; its notice
and corresponding source are in `examples/elf/README.md` and `NOTICES/effects-examples`. -/
noncomputable def sha256sum : Silmaril.Formats.Bytes := ⟨include_bytes "../../../../../examples/elf/pinned/gnu-sha256sum"⟩

end Silmaril.Elf.Link.Dyn.PinBytes
