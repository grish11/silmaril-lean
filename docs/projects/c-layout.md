# C aggregate layout: bit-fields, two ABIs, checked against compilers

`Silmaril.Data.Layout` lays out C structs and unions for five System V and ILP32 data models,
and rejects bit-fields. `Silmaril.Data.Layout.Bitfield` places aggregates **with** bit-fields at
bit granularity under a policy:

| policy | ABI | rule (module doc) |
|---|---|---|
| `sysv` | System V psABIs as gcc implements them (x86-64, i386, AArch64, RISC-V) | a bit-field stays in the storage unit of its declared type that holds the current bit, otherwise it moves to the next aligned unit; zero-width aligns; only named bit-fields add alignment; types share units |
| `ms` | Microsoft x64, as clang's MSVC-compatible layout computes it | one storage unit per declared type; a new unit when the type size changes or the field does not fit; zero-width closes the unit; every bit-field type aligns a struct; in a union a bit-field covers its unit and adds no alignment |

`msX64` is the Microsoft x64 data model (LLP64: `long` is 4 bytes, `long double` 8, `wchar_t` an
unsigned 2-byte type).

**Proved** (standard axioms):
- `bitLayout_wf`: every slot lies inside the record, and a struct's slots are pairwise disjoint and in increasing order.
- `bitfieldLayout`: the previously open `Task.bitfieldLayout`.
- `msX64_wf`: the Microsoft data model is well formed.
- `Examples.cases_agree`: on 25 aggregates (`examples/layout/cases.h`), the layout agrees with gcc 13.3 (System V) and clang 18.1 (Microsoft x64) on every reported size, alignment, bit offset and width.
- Named `sizeof`, `_Alignof`, `offsetof` and padding examples, including ones where the ABIs differ.

**Queries:**
- `bitShapeOf` gives `sizeof` and `_Alignof`.
- `offsetOf` gives a byte offset, and refuses a bit-field that is not on a byte boundary.
- `paddingBits` counts the bits of the record that no member covers.

**Refused rather than approximated:**
- a bit-field wider than its type;
- a named zero-width bit-field;
- a bit-field that is not an integer, `_Bool` or enum;
- `_Alignas` on a bit-field;
- aggregates nested inside a declaration that themselves contain bit-fields (`layoutTy` refuses them);
- `#pragma pack`, `packed`, `ms_struct`.

**Not claimed:** that clang's MSVC layout is `cl.exe`'s; layouts for other compilers or flags.
