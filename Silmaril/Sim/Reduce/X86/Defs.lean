module

public import Silmaril.Sim.Reduce.Core.Defs
public import Silmaril.Machine.X86.FnContract.Defs

/-!
# Reducing ISA problems to Wasm problems: x86-64 System V contracts (definitions)

The x86-64 instance of the reduction (`Silmaril.Sim.Reduce.Core`): a System V contract
`FnContract.Spec.Total I S` on a segment-VC machine `I` (for example `Open9.isa`) is the
reachability problem of

* `specPre I S`: live, System V entry (`AbiEntry`), the spec's `entry`;
* `specPost I S`: `Spec.Result`;

and its Wasm problem for a sound simulator `K` of `I` is `specWasm I S K Init` (the contract's
pre- and postcondition pulled back along the simulator's representation). `Thms` proves
`spec_total_iff`, `specReduction` and `specExact`.
-/

@[expose] public section

namespace Silmaril.Sim.Reduce

variable {W : Type}

section X86

open Silmaril.Machine.X86.FnContract (Spec AbiEntry)
open Silmaril.X86.SegVC (Isa)

variable {τ : Type}

/-- The precondition of `Spec.Total`: live, System V entry, the spec's `entry`. -/
def specPre (I : Isa τ) (S : Spec τ) : τ → Prop :=
  fun s => I.live s ∧ AbiEntry (I.core s) (I.mem s) ∧ S.entry s

/-- The postcondition of `Spec.Total`: `Spec.Result`. -/
def specPost (I : Isa τ) (S : Spec τ) : τ → τ → Prop := S.Result I

/-- **The Wasm problem of an x86 contract**: the contract's pre- and postcondition pulled back
along the simulator's representation relation. -/
def specWasm (I : Isa τ) (S : Spec τ) (K : SoundSim τ W) (Init : W → Prop) : Prop :=
  WasmTotal K Init (pullPre K (specPre I S)) (pullPost K (specPost I S))

end X86

end Silmaril.Sim.Reduce
