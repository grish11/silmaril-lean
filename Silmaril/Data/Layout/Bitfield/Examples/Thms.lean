module

public import Silmaril.Data.Layout.Bitfield.Examples.Defs

/-! # Bit-field layouts against real compilers: the checks

PROVED (`decide +kernel`, standard axioms):

* `cases_agree`: **on all 25 cases of `examples/layout/cases.h`** (structs and unions with
  bit-fields of every integer width, `_Bool` and enum bit-fields, zero-width and unnamed bit-fields,
  straddling, `_Alignas`, `long`, `long double`, pointers and arrays), `bitLayout` agrees with gcc
  13.3's x86-64 System V layout (`sysv`, `sysvX86_64`) and with clang 18.1's MSVC record layout
  (`ms`, `msX64`) on every size, alignment, member bit offset and width they report;
* named examples of `sizeof`, `_Alignof`, `offsetof` and padding, and where the two ABIs differ.
-/

@[expose] public section

namespace Silmaril.Data.Layout.Examples

open Silmaril.Data.Layout

/-- **Every case agrees with both compilers.** -/
theorem cases_agree :
    cases.all (fun (d, g, m) => agrees g (bitLayout .sysv sysvX86_64 [] d) &&
      agrees m (bitLayout .ms msX64 [] d)) = true := by decide +kernel

/-- `struct { char a : 4; int b : 4; }`: 4 bytes under System V (both in one `int` unit), 8 under
Microsoft x64 (a `char` unit, then an `int` unit). -/
theorem c03_sizes :
    (bitShapeOf .sysv sysvX86_64 [c03] .struct "c03").toOption = some ⟨4, 4⟩ ∧
    (bitShapeOf .ms msX64 [c03] .struct "c03").toOption = some ⟨8, 4⟩ := by decide +kernel

/-- `struct { long a; int b : 5; }`: `long` is 8 bytes under LP64 (16 in all), 4 under LLP64
(8 in all). -/
theorem c16_sizes :
    (bitShapeOf .sysv sysvX86_64 [c16] .struct "c16").toOption = some ⟨16, 8⟩ ∧
    (bitShapeOf .ms msX64 [c16] .struct "c16").toOption = some ⟨8, 4⟩ := by decide +kernel

/-- `offsetof(struct c13, c)` (after `int a; char b : 2;`) is 5 under both ABIs. -/
theorem c13_offsetof :
    (offsetOf .sysv sysvX86_64 [c13] .struct "c13" "c").toOption = some 5 ∧
    (offsetOf .ms msX64 [c13] .struct "c13" "c").toOption = some 5 := by decide +kernel

/-- `offsetof` of a bit-field not on a byte boundary is refused (ill-formed in C). -/
theorem c02_offsetof_bitfield :
    (offsetOf .sysv sysvX86_64 [c02] .struct "c02" "b").toOption = some 1 ∧
    (offsetOf .sysv sysvX86_64 [c03] .struct "c03" "b").toOption = none := by decide +kernel

/-- `struct { char a; long long : 3; }`: the unnamed `long long` bit-field adds no alignment under
System V (2 bytes, 13 of them padding bits) but a whole aligned unit under Microsoft (16 bytes). -/
theorem c05_padding :
    (bitLayout .sysv sysvX86_64 [] c05).toOption.map (fun (ss, sh) => (sh, paddingBits ss sh)) =
      some (⟨2, 1⟩, 5) ∧
    (bitShapeOf .ms msX64 [c05] .struct "c05").toOption = some ⟨16, 8⟩ := by decide +kernel

end Silmaril.Data.Layout.Examples
