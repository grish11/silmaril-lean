module

public import Silmaril.Sim.Reduce.X86.Defs
public import Silmaril.Sim.Reduce.Core.Thms

/-!
# Reducing ISA problems to Wasm problems: x86-64 System V contracts, proofs

The header is `Silmaril/Sim/Reduce/X86/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Sim.Reduce

variable {W : Type}

section X86

open Silmaril.X86.FnContract (Spec AbiEntry)
open Silmaril.X86.SegVC (Isa)

variable {τ : Type}

/-- `Spec.Total` is the reachability problem of `specPre` and `specPost`. -/
theorem spec_total_iff (I : Isa τ) (S : Spec τ) :
    S.Total I ↔ IsaReach I.step (specPre I S) (specPost I S) := by
  constructor
  · intro h s ⟨hl, ha, he⟩
    exact h s hl ha he
  · intro h s hl ha he
    exact h s ⟨hl, ha, he⟩

/-- **The x86 contract reduction**: the System V contract `S` on the machine `I` (for example
`Open9.isa`) is solved by the Wasm problem `specWasm I S K Init` of a sound simulator `K` of
`I`, when every entry state of `S` can be loaded into the simulator. -/
def specReduction (I : Isa τ) (S : Spec τ) (K : SoundSim τ W) (hstep : K.step = I.step)
    (Init : W → Prop) (henc : Encodes K Init (specPre I S)) : Reduction where
  src := S.Total I
  tgt := specWasm I S K Init
  sound h := (spec_total_iff I S).2 (hstep ▸ isaReach_of_wasmTotal K henc h)

/-- The exact x86 contract reduction, given completeness on the fragment. -/
def specExact (I : Isa τ) (S : Spec τ) (K : SoundSim τ W) (hstep : K.step = I.step)
    (Init : W → Prop) (henc : Encodes K Init (specPre I S))
    (hc : Complete K Init (specPre I S) (specPost I S)) : Reduction.Exact where
  toReduction := specReduction I S K hstep Init henc
  complete h := wasmTotal_of_isaReach K hc (hstep ▸ (spec_total_iff I S).1 h)

end X86

end Silmaril.Sim.Reduce
