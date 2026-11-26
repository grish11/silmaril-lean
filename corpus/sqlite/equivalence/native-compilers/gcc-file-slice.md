# GCC SQLite length-query file evidence

The SQLite 3.54.1 build uses Debian GCC 14.2.0-19 at `-O2`, System V AMD64,
and the default configuration (`SQLITE_THREADSAFE=1`). The public file is
`corpus/variants/sqlite/3.54.1/default/x86_64/O2/unstripped/libsqlite3.so`
with SHA-256
`fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8`.
The staged symbol theorem `sym_3_288` identifies the dynamic
`sqlite3_str_length` row. The read-only executable `PT_LOAD` has
both file offset and virtual address `0xf000`. The function occupies
`[0x10060, 0x1006b)` in the file and in the ELF virtual address space.
Its bytes are `31 c0 48 85 ff 74 03 8b 47 18 c3`.

`GccStrLengthFile.file_codeAt` checks the segment selection and reads the
exact bytes against the staged kernel copy of the pinned ELF.
`file_placement_zero` verifies the abstract ELF placement at bias zero.
`file_slice_has_executable_mapping` constructs a readable and executable
abstract memory containing the checked span at that placement. The
negative check verifies that the same backing with read permission
alone fails instruction fetch.

At a general bias, `fetch_of_readOnly_image` takes independently supplied
`Elf.Placement` and `ElfBind.RoLoaded` evidence for this file. It proves
exact fetchability and the non-wrapping runtime address. The abstract
memory witness covers the eleven-byte span, and the placement proof
concerns the file model. Complete host loading is outside this scope.

## First return and CFG agreement

`GccStrLengthFile.CFG.symbol_code_at` connects the actual parsed `.dynsym`
entry 288 to the complete executable span used by the CFG proof. For a
valid placement of this file, `firstReturn_of_readOnly_image` derives
instruction fetch from `RoLoaded` and requires entry RIP at bias + `0x10060`,
a readable saved return word, and a successful four-byte read at `RDI + 24`
if RDI is nonzero. `agrees_of_firstReturn` covers every modeled first return
from the same entry. The CFG and the open x86 semantics agree on the selected
branch and the returned RAX payload. The CFG exits at the common RET, the
machine executes RET to the saved address, and machine memory is preserved.
The Lean regression rules out attaching the original CFG bytes to the
same-length span starting at `0x10061` in this ELF.

The kernel checks the symbol, bytes and conditional trace result in the
repository's ELF reader and `X86.Open` semantics. The build provenance and
SHA-256 are recorded in the [native compiler manifest](manifest.json).
The supplied `RoLoaded` image, caller state and data memory are assumptions.
The guarded read uses the modeled effective address. C object lifetime,
source-to-machine refinement and live loader adequacy are separate obligations.
The pinned ELF's `.rela.dyn` has 290 `R_X86_64_64` entries, including one
at target `0x10e520`. The current loader rejects type 1, so its eager image
relation cannot supply the image premise for this file at the head of scope.
[Relocation coverage](gcc-relocation-coverage.md)
[#2176](https://github.com/hiloopai/silmaril-lean/pull/2176)

```sh
root=Silmaril.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile.CFG
lake build --wfail +"$root".Checks
make check CHECK_TARGETS="+$root.Checks"
```
