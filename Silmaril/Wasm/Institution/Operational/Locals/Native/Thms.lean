module

public import Silmaril.Wasm.Institution.Operational.Locals.Native.Defs
public import Silmaril.Wasm.Versions.Lime1.Runtime.Defs
public import Silmaril.Wasm.SingleThreaded.Determinism.HeadDet
import Silmaril.Proofs.Wasm.Institution.Operational.Locals.Core
import Silmaril.Proofs.Wasm.Institution.Operational.Locals.V1
import Silmaril.Proofs.Wasm.Institution.Operational.Locals.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.Locals.Transport

/-!
# Exact native readback for flat local instructions

The step equivalences allow any native successor of the rendered source.
The path equivalences preserve the typed guard and reconstruct the whole
native endpoint, including its fixed store and module instance. Core takes
its own store and module parameters and uses the empty host relation.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Locals

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (ModuleInst)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

section V1
variable {H : Type} {host : Wasm.V1.Execution.HostSemantics H}
variable {s : Wasm.V1.Execution.Store H} {m : ModuleInst}

theorem v1_sound {a b : State} (edge : Edge a b) :
    Wasm.V1.Execution.Step host (v1Config s m a) (v1Config s m b) :=
  Proofs.V1.sound s m edge

theorem v1_step_iff {a : State} {b : Wasm.V1.Execution.Config H} :
    Wasm.V1.Execution.Step host (v1Config s m a) b ↔
      ∃ out, Edge a out ∧ b = v1Config s m out := by
  constructor
  · intro step
    simpa only [v1Config, Codec.decode_encode] using Proofs.V1.readback step (v1Codec.supports_encode a.code)
  · rintro ⟨out, edge, rfl⟩
    exact v1_sound edge

theorem v1_run_iff {types result : List NumType} {a : State} {b : Wasm.V1.Execution.Config H}
    (guard : Admitted types result a) :
    Relation.ReflTransGen (Wasm.V1.Execution.Step host) (v1Config s m a) b ↔
      ∃ out, Runs a out ∧ Admitted types result out ∧ b = v1Config s m out :=
  Proofs.run_iff (v1Config s m) _ (fun h => v1_sound h) (fun h => v1_step_iff.mp h) guard

end V1

section Lime1
variable {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H}
variable {s : Wasm.Lime1.Execution.Store H} {m : ModuleInst}

theorem lime_sound {a b : State} (edge : Edge a b) :
    Wasm.Lime1.Execution.Step host (limeConfig s m a) (limeConfig s m b) :=
  Proofs.Lime1.sound s m edge

theorem lime_step_iff {a : State} {b : Wasm.Lime1.Execution.Config H} :
    Wasm.Lime1.Execution.Step host (limeConfig s m a) b ↔
      ∃ out, Edge a out ∧ b = limeConfig s m out := by
  constructor
  · intro step
    simpa only [limeConfig, Codec.decode_encode] using Proofs.Lime1.readback step (limeCodec.supports_encode a.code)
  · rintro ⟨out, edge, rfl⟩
    exact lime_sound edge

theorem lime_run_iff {types result : List NumType} {a : State} {b : Wasm.Lime1.Execution.Config H}
    (guard : Admitted types result a) :
    Relation.ReflTransGen (Wasm.Lime1.Execution.Step host) (limeConfig s m a) b ↔
      ∃ out, Runs a out ∧ Admitted types result out ∧ b = limeConfig s m out :=
  Proofs.run_iff (limeConfig s m) _ (fun h => lime_sound h) (fun h => lime_step_iff.mp h) guard

end Lime1

section Core
variable {H : Type} {P : Wasm.Numerics.Profile}
variable {s : Core.Store H} {m : Core.ModuleInst}

theorem core_sound {a b : State} (edge : Edge a b) :
    Core.Step P noHost (coreConfig s m a) (coreConfig s m b) :=
  Proofs.core_sound s m edge

theorem core_step_iff {a : State} {b : Core.Config H} :
    Core.Step P noHost (coreConfig s m a) b ↔
      ∃ out, Edge a out ∧ b = coreConfig s m out := by
  constructor
  · intro step
    exact Proofs.core_readback step
  · rintro ⟨out, edge, rfl⟩
    exact core_sound edge

theorem core_run_iff {types result : List NumType} {a : State} {b : Core.Config H}
    (guard : Admitted types result a) :
    Relation.ReflTransGen (Core.Step P noHost) (coreConfig s m a) b ↔
      ∃ out, Runs a out ∧ Admitted types result out ∧ b = coreConfig s m out :=
  Proofs.run_iff (coreConfig s m) _ (fun h => core_sound h) (fun h => core_step_iff.mp h) guard

end Core

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H)
    (m : ModuleInst) (a : State) :
    (v1Config s m a).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) m a :=
  Proofs.v1_to_lime s m a

theorem v1_code_to_core (ops : List Op) :
    LegacyDivision.emitCode Wasm.V1.Instr.toCore (v1Codec.encode ops) = coreCodec.encode ops :=
  Proofs.emit_core _ _ _ _ ops

theorem lime_code_to_core (ops : List Op) :
    LegacyDivision.emitCode Wasm.Lime1.Instr.toCore (limeCodec.encode ops) = coreCodec.encode ops :=
  Proofs.emit_core _ _ _ _ ops

/-- The existing runtime translation agrees on the store, frame, and code. -/
theorem lime_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H)
    (m : Wasm.Execution.Runtime.ModuleInst) (a : State) :
    (limeConfig s m a).toCore = coreConfig s.toCore m.toCore a :=
  Proofs.lime_to_core s m a

end Silmaril.Wasm.Institution.Operational.Locals
