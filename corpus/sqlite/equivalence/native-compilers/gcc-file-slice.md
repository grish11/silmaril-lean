# GCC SQLite length-query file evidence

The GCC 14 O2 SQLite 3.54.1 build is the public file
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

The dynamic loader relation is deliberately outside this proof. The
pinned ELF's `.rela.dyn` has 290 `R_X86_64_64` entries, including one
at target `0x10e520`. The current loader's `relocVal` rejects type 1.
[#2176](https://github.com/hiloopai/silmaril-lean/pull/2176)

```sh
lake build --wfail Silmaril.Elf.Corpus.SqliteNativeCompilers.GccStrLengthFile.Thms
```
