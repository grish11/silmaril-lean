module

public import Silmaril.Proofs.Elf.Abi.Libm.Common
public import Silmaril.Machine.Abi.Conformance.Import.Defs
public import Silmaril.Machine.Abi.Conformance.SysvScalar.Defs
public import Silmaril.Data.Layout.Header.Import.Pinned.GlibcMath.Thms

/-! # glibc `libm.so.6` rows: the classification, checked

* `classes_names`: the classified names are `claimable sysvScalar sysvCcs glibcMath`, in order
  (rewriting with `Pinned.import_glibcMath`, then a kernel computation on the import's literal);
* `classes_check`: every class is what the file's parse says (one kernel computation: 288
  versioned lookups and symbol scans on `A0`), hence `classes_holds`;
* `classes_counts`: 121 plain, 25 IFUNC, 142 absent; 18 with a later default version.
-/

set_option maxRecDepth 100000

@[expose] public section

namespace Silmaril.Proofs.Elf.Abi.Libm

open Silmaril.Elf Silmaril.Elf.Abi Silmaril.Elf.Abi.Libm
open Silmaril.Machine.Abi.Conformance
open Silmaril.Data.Layout.Header.Import.Pinned

theorem classes_names :
    claimable sysvScalar sysvCcs glibcMath = classes.map (·.1) := by
  rw [import_glibcMath]; decide +kernel

set_option maxHeartbeats 1000000 in
theorem classes_check : classes.all (fun (f, c) => c.check A0 f) = true := by
  decide +kernel

theorem classes_holds : ∀ f c, (f, c) ∈ classes → c.Holds F f := fun f c h =>
  holds_of_check (by simpa using List.all_eq_true.mp classes_check (f, c) h)

theorem classes_counts :
    classes.length = 288 ∧ (classes.filter (·.2.isPlain)).length = 121 ∧
      (classes.filter (·.2.isIfunc)).length = 25 ∧ (classes.filter (·.2.isAbsent)).length = 142 ∧
      (classes.filter (·.2.laterVersion)).length = 18 := by
  decide +kernel

end Silmaril.Proofs.Elf.Abi.Libm

end
