module

public import Silmaril.Wasm.Component.DecoderBridge.InstExport.Defs
public import Silmaril.Wasm.Component.InstRef.Defs
public import Silmaril.Wasm.Component.Reference.Defs
public import Silmaril.Wasm.Component.RefValid.Defs
import Silmaril.Proofs.Wasm.Component.DecoderBridge.InstExport

/-!
# An exported instance: the two readings name different exports (regression)

All proved by the kernel; proofs in `Silmaril.Proofs.Wasm.Component.DecoderBridge.InstExport`.

* `parse_instExport`: the IR reading of `instexport.wasm` is `instExportComp`, whose imports are
  `f: func(u32)` (`hostI`) and whose only export is named `"i#get"` (`instExport_ir_exports`);
* `decodeRef_instExport`, `instExport_valid`: the REF reading is the valid `instExportRef`, which
  is not in the fragment of `DecoderBridge.Wire` (`instExport_not_inFrag`);
* `instExport_ref_run`: under the logging host (`InstRef.embL`, `InstTestsRef.hostConfigX`), the
  reference machine instantiates it (one executed run, first scheduling oracle) and reports no
  function export, so the lookup of the IR's export name `"i#get"` fails on that run.

This is a demonstrated mismatch between the two readings' export names, not a disproof of
`Task.startAdequacy` as first stated: the IR's answer to `i#get` and the absence of `i#get` from
**every** reference run are not proved.
-/

public section

namespace Silmaril.Wasm.Component.DecoderBridge

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.Conformance
open Silmaril.Wasm.Component.InstRef Silmaril.Wasm.Component.InstLitmus
open Silmaril.Wasm.Component.InstTestsRef
open Silmaril.Wasm.Component.Reference.Core3Adder (first)

/-- **The IR reading of `instexport.wasm`.** -/
theorem parse_instExport : Binary.parseComponent instExportBytes = .ok instExportComp :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.parse_instExport

/-- The IR reading imports `f: func(u32)` and exports one function, named `i#get`. -/
theorem instExport_ir_exports :
    instExportComp.imports = hostI ∧ instExportComp.exports.map (·.name) = ["i#get"] :=
  ⟨rfl, rfl⟩

/-- **The REF reading of `instexport.wasm`.** -/
theorem decodeRef_instExport : decodeRef instExportBytes = .ok instExportRef :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.decodeRef_instExport

/-- The REF reading is valid. -/
theorem instExport_valid : ∃ ct, Valid Features.p2 instExportRef ct :=
  Silmaril.Proofs.Wasm.Component.DecoderBridge.instExport_valid

/-- The REF reading is not in the fragment (it exports an instance). -/
theorem instExport_not_inFrag : ¬ InFrag instExportRef := by decide +kernel

/-- **On an executed reference run, the instance has no function export**, so in particular
none named `i#get`. -/
theorem instExport_ref_run : ∃ m inst es,
    InstResult.instance m inst es ∈
      instBehaviours first.prof (Host.ofEmbedder embL) hostConfigX instExportRef (importArgs hostI) ∧
    es = [] ∧ es.lookup "i#get" = none := by
  obtain ⟨m, inst, h⟩ := Silmaril.Proofs.Wasm.Component.DecoderBridge.instExport_run
  exact ⟨m, inst, [], h, rfl, rfl⟩

end Silmaril.Wasm.Component.DecoderBridge
