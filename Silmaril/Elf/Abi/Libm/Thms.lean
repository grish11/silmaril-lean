module

public import Silmaril.Elf.Abi.Libm.Defs
public import Silmaril.Machine.Abi.Conformance.Import.Thms
public import Silmaril.Machine.Abi.Conformance.Sse.Lrint.Thms
import Silmaril.Proofs.Elf.Abi.Libm.Classes
import Silmaril.Proofs.Elf.Abi.Libm.Rows

/-! # glibc's `libm.so.6` against the pinned `math.h`: theorems

PROVED (standard axioms), proofs in `Silmaril.Proofs.Elf.Abi.Libm.{Common,Classes,Rows}`.

**Classification** of the 288 `sysvScalar`-claimable functions of `Pinned.glibcMath`:

| theorem | statement |
|---|---|
| `classes_names` | the classified names are `claimable sysvScalar sysvCcs glibcMath`, in order |
| `classes_holds` | every class holds of the file: plain (`Lookup` of the default version, `STT_FUNC` entry), IFUNC (`¬ CodeOf` for every code), absent (`Absent`) |
| `classes_counts` | 121 plain, 25 IFUNC, 142 absent; 18 with a default version later than `GLIBC_2.2.5` |

**The file**: `irelative` (x86-64; 21 `R_X86_64_IRELATIVE` dynamic relocations), hence
`not_untouched` and **`not_abiConforms`: the `abi_conforms` shape is false for every function of
this file**, whatever the machine and spec. `placement_zero`: it admits the load base `0`.

**Rows** (`Defs`): `*_code` (`CodeOf` of the code with the versioned binding of
`GLIBC_2.2.5`), `*_declared` (`Declares` through `hdr`), `hdr_agrees` and `declares_iff` (every
row prototype is the import's; `Declares abi hdr` is `DeclaresImport abi sysvCcs glibcMath`), and

* **`lrint_conforms`, `llrint_conforms`: PROVED.** At every load base the file admits, the code
  of `lrint` (and of `llrint`, the same six bytes) conforms on `Mach.str9L
  FeatureSet.baseline64 Features.sseExts` to `sysvScalar.defaultEnv` as the `math.h`
  declaration, total, frame 0, with the result `Lrint.toLong` of the entry MXCSR
  (`Numeric.Float`'s x86 SSE `toInt`). On the model only: `Faithful` is not proved.
* the other rows are **open** (`Task.libm_*` in `Defs`), with their file facts proved here.
-/

@[expose] public section

namespace Silmaril.Elf.Abi.Libm

open Silmaril.Elf
open Silmaril.Machine.Abi.Conformance
open Silmaril.Data.Layout.Header.Import.Pinned (glibcMath)

/-! ## Classification -/

theorem classes_names : claimable sysvScalar sysvCcs glibcMath = classes.map (·.1) :=
  Silmaril.Proofs.Elf.Abi.Libm.classes_names

theorem classes_holds : ∀ f c, (f, c) ∈ classes → c.Holds F f :=
  Silmaril.Proofs.Elf.Abi.Libm.classes_holds

theorem classes_counts :
    classes.length = 288 ∧ (classes.filter (·.2.isPlain)).length = 121 ∧
      (classes.filter (·.2.isIfunc)).length = 25 ∧ (classes.filter (·.2.isAbsent)).length = 142 ∧
      (classes.filter (·.2.laterVersion)).length = 18 :=
  Silmaril.Proofs.Elf.Abi.Libm.classes_counts

/-! ## The file -/

theorem irelative : A0.header.machine = EM_X86_64 ∧
    ((A0.relocs .dynamic).filter (·.kind == 37)).length = 21 ∧
    (A0.relocs .dynamic).any (·.kind == 37) = true :=
  Silmaril.Proofs.Elf.Abi.Libm.irelative

theorem not_untouched (c : Code) : ¬ Untouched F c :=
  Silmaril.Proofs.Elf.Abi.Libm.not_untouched c

/-- **No function of this file has an `abi_conforms` row**: `Untouched` is refused. -/
theorem not_abiConforms {A : AbiDef} {M : Mach} {mode : Mode} {hdr : HeaderSrc} {f : String}
    {p : A.V.Proto} {b : Binding} {c : Code} {frame : Nat} {S : CallSpec A.V p} :
    ¬ AbiConforms A M mode hdr f p F b c frame S := fun h => not_untouched c h.2.1

theorem placement_zero : Placement F 0 := Silmaril.Proofs.Elf.Abi.Libm.placement_zero

/-! ## Code -/

theorem lrint_code : CodeOf F (.dynsym (some v2_2_5)) "lrint" lrintCode :=
  Silmaril.Proofs.Elf.Abi.Libm.lrint_code
theorem llrint_code : CodeOf F (.dynsym (some v2_2_5)) "llrint" llrintCode :=
  Silmaril.Proofs.Elf.Abi.Libm.llrint_code
theorem lrintf_code : CodeOf F (.dynsym (some v2_2_5)) "lrintf" lrintfCode :=
  Silmaril.Proofs.Elf.Abi.Libm.lrintf_code
theorem llrintf_code : CodeOf F (.dynsym (some v2_2_5)) "llrintf" llrintfCode :=
  Silmaril.Proofs.Elf.Abi.Libm.llrintf_code
theorem round_code : CodeOf F (.dynsym (some v2_2_5)) "round" roundCode :=
  Silmaril.Proofs.Elf.Abi.Libm.round_code
theorem fmax_code : CodeOf F (.dynsym (some v2_2_5)) "fmax" fmaxCode :=
  Silmaril.Proofs.Elf.Abi.Libm.fmax_code
theorem fmin_code : CodeOf F (.dynsym (some v2_2_5)) "fmin" fminCode :=
  Silmaril.Proofs.Elf.Abi.Libm.fmin_code
theorem fpclassify_code : CodeOf F (.dynsym (some v2_2_5)) "__fpclassify" fpclassifyCode :=
  Silmaril.Proofs.Elf.Abi.Libm.fpclassify_code
theorem signbit_code : CodeOf F (.dynsym (some v2_2_5)) "__signbit" signbitCode :=
  Silmaril.Proofs.Elf.Abi.Libm.signbit_code
theorem finiteInternal_code : CodeOf F (.dynsym (some v2_2_5)) "__finite" finiteInternalCode :=
  Silmaril.Proofs.Elf.Abi.Libm.finiteInternal_code
theorem finite_code : CodeOf F (.dynsym (some v2_2_5)) "finite" finiteCode :=
  Silmaril.Proofs.Elf.Abi.Libm.finite_code

/-! ## Declarations -/

theorem hdr_agrees : rowNames.all (fun f => hdr.proto? f == glibcMath.proto? f &&
    (glibcMath.fn? f).any (fun x => sysvCcs.contains x.2.cc)) = true :=
  Silmaril.Proofs.Elf.Abi.Libm.hdr_agrees

theorem declares_iff : ∀ f ∈ rowNames, ∀ p : abi.V.Proto,
    Declares abi hdr f p ↔ DeclaresImport abi sysvCcs glibcMath f p :=
  Silmaril.Proofs.Elf.Abi.Libm.declares_iff

theorem lrint_declared : Declares abi hdr "lrint" Silmaril.Machine.Abi.Conformance.Sse.Lrint.proto :=
  Silmaril.Proofs.Elf.Abi.Libm.lrint_declared
theorem llrint_declared :
    Declares abi hdr "llrint" Silmaril.Machine.Abi.Conformance.Sse.Lrint.proto :=
  Silmaril.Proofs.Elf.Abi.Libm.llrint_declared
theorem lrintf_declared : Declares abi hdr "lrintf" fLong :=
  Silmaril.Proofs.Elf.Abi.Libm.lrintf_declared
theorem llrintf_declared : Declares abi hdr "llrintf" fLong :=
  Silmaril.Proofs.Elf.Abi.Libm.llrintf_declared
theorem round_declared : Declares abi hdr "round" dDouble :=
  Silmaril.Proofs.Elf.Abi.Libm.round_declared
theorem fmax_declared : Declares abi hdr "fmax" ddDouble :=
  Silmaril.Proofs.Elf.Abi.Libm.fmax_declared
theorem fmin_declared : Declares abi hdr "fmin" ddDouble :=
  Silmaril.Proofs.Elf.Abi.Libm.fmin_declared
theorem fpclassify_declared : Declares abi hdr "__fpclassify" dInt :=
  Silmaril.Proofs.Elf.Abi.Libm.fpclassify_declared
theorem signbit_declared : Declares abi hdr "__signbit" dInt :=
  Silmaril.Proofs.Elf.Abi.Libm.signbit_declared
theorem finiteInternal_declared : Declares abi hdr "__finite" dInt :=
  Silmaril.Proofs.Elf.Abi.Libm.finiteInternal_declared
theorem finite_declared : Declares abi hdr "finite" dInt :=
  Silmaril.Proofs.Elf.Abi.Libm.finite_declared

/-! ## The proved rows -/

theorem lrint_conforms : ∀ base, Placement F base →
    Conforms abi mach .total hdr "lrint" Silmaril.Machine.Abi.Conformance.Sse.Lrint.proto
      (lrintCode.rebase base) 0 Silmaril.Machine.Abi.Conformance.Sse.Lrint.spec :=
  Silmaril.Proofs.Elf.Abi.Libm.lrint_conforms

theorem llrint_conforms : ∀ base, Placement F base →
    Conforms abi mach .total hdr "llrint" Silmaril.Machine.Abi.Conformance.Sse.Lrint.proto
      (llrintCode.rebase base) 0 Silmaril.Machine.Abi.Conformance.Sse.Lrint.spec :=
  Silmaril.Proofs.Elf.Abi.Libm.llrint_conforms

end Silmaril.Elf.Abi.Libm

end
