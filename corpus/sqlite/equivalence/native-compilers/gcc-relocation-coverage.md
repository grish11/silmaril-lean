# GCC SQLite relocation coverage in the eager model

The pinned GCC 14 SQLite 3.54.1 O2 shared object is
`corpus/variants/sqlite/3.54.1/default/x86_64/O2/unstripped/libsqlite3.so`,
SHA-256 `fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8`.
The kernel checks the actual dynamic tables through the staged byte reader.

`relocation_spans` witnesses successfully read `DT_RELA` and `DT_JMPREL`
tables, with 1,468 and 174 entries respectively. It proves that the
eight-byte targets of all 1,642 records miss every read-only `PT_LOAD`.
The main table has 290 type-1 records, including
`(r_offset = 0x10e520, type = R_X86_64_64, r_sym = 195, addend = 0)`.

`eager_slots_unsupported` proves that the current eager evaluator rejects
this exact file for every resolver. The type-1 record occurs in the real
table and causes the full traversal to fail. `no_eager_image` therefore
rules out `ExeLoaded (F :: scope) (base :: bases) ifunc false resolver memory`
for all those arguments. These conclusions refer to the current modeled
loader. The file-byte evidence for the length query is a separate result.
[#2176 review target](https://github.com/hiloopai/silmaril-lean/pull/2176)

The AMD64 type-1 relocation writes the 64-bit sum `S + A`. The eventual
type-1 semantics needs symbol binding and the signed addend, then a
witnessed eager image for this exact artifact. The span check here is a
fact about target addresses. It requires no slot table or loaded image.

```sh
lake build --wfail Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage.Thms
```
