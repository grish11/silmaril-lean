/-
Print the functions of the pinned `math.h` import that `sysvScalar` can claim, one per line, in
the import's order.

    lake env lean scripts/libm-rows/claimable.lean

`scripts/libm-rows/gen.py` reads this list. Nothing here is trusted: the theorem
`Silmaril.Elf.Abi.Libm.classes_names` checks in the kernel that the generated classification
lists exactly `claimable sysvScalar sysvCcs glibcMath`, in this order.
-/
import Silmaril.Machine.Abi.Conformance.Import.Defs
import Silmaril.Machine.Abi.Conformance.SysvScalar.Defs
import Silmaril.Data.Layout.Header.Import.Pinned.GlibcMath.Defs

open Silmaril.Machine.Abi.Conformance Silmaril.Data.Layout.Header.Import
open Silmaril.Data.Layout.Header.Import.Pinned

-- The import's literal (`Pinned.import_glibcMath` proves `glibcMath` equal to it).
#eval do
  for f in claimable sysvScalar sysvCcs ⟨.parse glibcMathProv, GlibcMath.entries, none⟩ do
    IO.println f
