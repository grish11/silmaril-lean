module

public import Silmaril.Wasm.Auto2.Kernel.Thms
public import Silmaril.Wasm.Auto2.Valid2.Thms
public import tests.wasm.auto.FrontBenchX.Defs
public import Silmaril.Wasm.Auto.Bridge.Thms
public import Silmaril.Wasm.Auto.Front.Thms

/-!
# The memory cases of the front-end benchmark, kernel-checked

Round 3 left `adlersum8-O2` and `adlersum8-mutant` (modules with a one-page memory and a 24-byte
data segment) to the compiled checker: their kernel instantiation did not finish in 44 GB. With
the closed-form data segments and the validation-free instance of `Silmaril.Wasm.Auto2.Kernel`,
both are kernel-checked here (pass 3 of the kernel track: validated by `validG?`, the structural
validator with globals and memory): Binaryen's `-O2` output of the Adler-32 8-way step is equivalent
to it at every profile, and the mutant (one byte read twice) does not refine it.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.KernelBench

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Front Silmaril.Wasm.Auto.FrontBenchX Silmaril.Wasm.Auto2.Kernel
open Silmaril.Proofs.Wasm.Auto2.Kernel
open Silmaril.Wasm.SingleThreaded (profile)
open Silmaril.Wasm.Numerics (Profile)

theorem adlerSum8_valid : (validate? adlerSum8).isSome = true := by
  rw [← Silmaril.Proofs.Wasm.Auto2.Valid2.validG?_eq]
  decide +kernel

theorem adlerSum8O2_valid : (validate? adlerSum8O2).isSome = true := by
  rw [← Silmaril.Proofs.Wasm.Auto2.Valid2.validG?_eq]
  decide +kernel

theorem adlerSum8Mutant_valid : (validate? adlerSum8Mutant).isSome = true := by
  rw [← Silmaril.Proofs.Wasm.Auto2.Valid2.validG?_eq]
  decide +kernel

/-- **The Adler-32 8-way step is equivalent to its Binaryen `-O2` output**, at every profile
(memory `0` and two globals; the summaries of `Silmaril.Wasm.Auto.Bridge`). -/
theorem adlerSum8O2_equiv (R : Rel) (P : Profile) :
    ModEquiv R.toProp P adlerSum8O2 adlerSum8 0 :=
  Silmaril.Wasm.Auto.Bridge.modEquiv_of_checkAmong (js := [0]) (i := 0)
    (Silmaril.Wasm.Auto.Bridge.rel_refl _) rfl
    (by rw [checkAmongX_eq_K adlerSum8O2_valid adlerSum8_valid]; decide +kernel)

/-- **The mutant does not refine the Adler-32 8-way step**: on address `0` it reads the first
byte twice. -/
theorem adlerSum8Mutant_not_refines :
    ¬ ModRefines Rel.eq.toProp (profile Silmaril.Wasm.Verify.refOracle) adlerSum8Mutant adlerSum8 0 :=
  refutes_of_cexK (vs := [Val.i32 0]) (by
    rw [cexK, cexWith_eq_K adlerSum8Mutant_valid adlerSum8_valid]
    decide +kernel)

end Silmaril.Proofs.Wasm.Auto2.KernelBench
