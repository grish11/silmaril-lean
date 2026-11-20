module

public import Silmaril.Wasm.Component.DecoderBridge.InstExport.Defs
public import Silmaril.Wasm.Component.InstRef.Defs
public import Silmaril.Wasm.Component.Reference.Thms
public import Silmaril.Wasm.Verify.Kernel.Defs

/-!
# An exported instance: the two readings name different exports (proofs)

* `parse_instExport`, `decodeRef_instExport`: the two readings of `instexport.wasm` (one
  definitional check by the kernel each, `kernel_rfl`);
* `instExport_valid`: the reference validator accepts the REF reading (`decide +kernel` on
  `check? Features.p2`, then `check?_sound`);
* `instExport_run`: under the logging host from `hostConfigX`, the reference machine's executable
  instantiation driver (`Embedder.instantiateRun`, first scheduling oracle, fuel `400`) finishes
  and reports **no function export** (`decide +kernel`), so `instantiateRun_mem` gives an
  instantiation behaviour with the export list `[]`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance Silmaril.Wasm.Component.DecoderBridge
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

theorem parse_instExport : Binary.parseComponent instExportBytes = .ok instExportComp := by
  kernel_rfl

theorem decodeRef_instExport : decodeRef instExportBytes = .ok instExportRef := by kernel_rfl

theorem instExport_valid : ∃ ct, Valid Features.p2 instExportRef ct := by
  have h : (check? Features.p2 instExportRef).isOk = true := by decide +kernel
  cases e : check? Features.p2 instExportRef with
  | error _ => rw [e] at h; cases h
  | ok ct => exact ⟨ct, check?_sound e⟩

theorem instExport_summary :
    ((embL.instantiateRun first 400 instExportRef (importArgs hostI) hostConfigX).map
      (·.2.2)) = some [] := by
  decide +kernel

theorem instExport_run : ∃ m inst,
    InstResult.instance m inst [] ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX instExportRef (importArgs hostI) := by
  obtain ⟨⟨r, inst, es⟩, h, he⟩ := Option.map_eq_some_iff.1 instExport_summary
  simp only at he
  subst he
  exact ⟨r.config, inst, instantiateRun_mem embL first h⟩

end Silmaril.Proofs.Wasm.Component.DecoderBridge
