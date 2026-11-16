module

public import Silmaril.Sim.Reduce.Wasm.Defs
public import Silmaril.Sim.Reduce.X86.Thms
public import Silmaril.Wasm.Logic.Core.Thms

/-!
# Reducing ISA problems to Wasm problems: the call-level Wasm problem, proofs

The header is `Silmaril/Sim/Reduce/Wasm/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Sim.Reduce.Wasm

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Logic.Core
open Silmaril.Sim (Machine PState)

variable {L V H S : Type}

/-- The call-level Wasm problem gives the run-level one. -/
theorem wasmTotal_of_runSpec {step : S → Option S} {view : S → PState L V}
    {K : Silmaril.Sim.Wasm.ExportSim Unit L V H} (Ct : K.Cert (Machine.ofStep step view))
    {Init Pre : Store H → Prop} {Post : Store H → Store H → Prop} (h : runSpec K Init Pre Post) :
    WasmTotal (SoundSim.ofExportCert Ct) Init Pre Post := by
  intro w hi hp
  obtain ⟨s', res, hs, hok, hq⟩ := h.invoke ⟨rfl, hi, hp⟩
  exact ⟨s', SoundSim.ofExportCert_run_of_call Ct ⟨{}, res, hok, hs⟩, hq⟩

section X86

open Silmaril.X86.FnContract (Spec)
open Silmaril.X86.SegVC (Isa)

/-- **The x86 contract reduction to a call-level Wasm problem**: the System V contract `S` on
`I` is solved by the `FuncSpec` of the simulator's export with the contract pulled back along
the certificate's relation. -/
def specRunReduction {τ : Type} (I : Isa τ) (S : Spec τ) {view : τ → PState L V}
    {K : Silmaril.Sim.Wasm.ExportSim Unit L V H} (Ct : K.Cert (Machine.ofStep I.step view))
    (Init : Store H → Prop) (henc : Encodes (SoundSim.ofExportCert Ct) Init (specPre I S)) :
    Reduction where
  src := S.Total I
  tgt := runSpec K Init (pullPre (SoundSim.ofExportCert Ct) (specPre I S))
    (pullPost (SoundSim.ofExportCert Ct) (specPost I S))
  sound h := (specReduction I S (SoundSim.ofExportCert Ct) rfl Init henc).sound
    (wasmTotal_of_runSpec Ct h)

end X86

end Silmaril.Sim.Reduce.Wasm
