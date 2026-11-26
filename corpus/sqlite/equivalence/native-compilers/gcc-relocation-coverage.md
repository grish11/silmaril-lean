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

`relocVal` evaluates named, default-visible global and weak type-1
references of the supported symbol types using the existing scope lookup.
It writes `S + A` modulo 2^64, where `A` is the signed `Elf64_Rela`
addend. An unresolved weak reference contributes `S = 0`. An unresolved
strong reference or a lookup failure stops slot evaluation. The addend
for a modeled IFUNC is applied to the resolver's returned address.
[AMD64 psABI relocation table](https://gitlab.com/x86-psABIs/x86-64-ABI/-/blob/e1ce098331da5dbd66e1ffc74162380bcc213236/x86-64-ABI/object-files.tex#L440)
[glibc 2.39 relocation implementation](https://github.com/bminor/glibc/blob/glibc-2.39/sysdeps/x86_64/dl-machine.h)

`pinned_absolute_slot` runs the modeled symbol lookup on the pinned file in
the singleton scope `[F]`. The row at `0x10e520` resolves to
`sqlite3_aggregate_context` at object 0, offset `0x374e0`, so its slot word
is the supplied base plus `0x374e0`. Another real type-1 row at `0x112580`
requests `close@GLIBC_2.2.5`. The same scope has no definition for that
strong reference. `eager_slots_without_dependencies` and
`no_eager_image_without_dependencies` check this failure for `[F]`.

A complete image witness still requires a concrete dependency scope,
successful resolution of every slot, and a memory satisfying `ImageOk`.
The checks cover the modeled lookup and slots. They make no claim about a
host loader or which libc it selects for this build.

```sh
make check CHECK_TARGETS=+Silmaril.Elf.Corpus.SqliteNativeCompilers.GccRelocationCoverage.Checks
```
