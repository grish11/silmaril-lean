module

public import Silmaril.Wasm.Institution.Operational.Blocks.Native.Defs
public import Silmaril.Wasm.Institution.Operational.Blocks.Thms
public import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Core
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.V1
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Runs
import Silmaril.Proofs.Wasm.Institution.Operational.Blocks.Transport

/-!
# Native readback for an isolated scalar block

Block entry, administrative label reduction, and normal exit preserve the
surrounding store and module. The path equivalences reconstruct arbitrary
native endpoints and retain the block result and local types.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Blocks

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
      ∃ out, Edge a out ∧ b = v1Config s m out :=
  ⟨Proofs.V1.readback, fun ⟨_, edge, eq⟩ => eq.symm ▸ v1_sound edge⟩

theorem v1_run_iff {types : List NumType} {result : Option NumType} {a : State}
    {b : Wasm.V1.Execution.Config H} (guard : Admitted types result a) :
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
      ∃ out, Edge a out ∧ b = limeConfig s m out :=
  ⟨Proofs.Lime1.readback, fun ⟨_, edge, eq⟩ => eq.symm ▸ lime_sound edge⟩

theorem lime_run_iff {types : List NumType} {result : Option NumType} {a : State}
    {b : Wasm.Lime1.Execution.Config H} (guard : Admitted types result a) :
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
      ∃ out, Edge a out ∧ b = coreConfig s m out :=
  ⟨Proofs.core_readback, fun ⟨_, edge, eq⟩ => eq.symm ▸ core_sound edge⟩

theorem core_run_iff {types : List NumType} {result : Option NumType} {a : State}
    {b : Core.Config H} (guard : Admitted types result a) :
    Relation.ReflTransGen (Core.Step P noHost) (coreConfig s m a) b ↔
      ∃ out, Runs a out ∧ Admitted types result out ∧ b = coreConfig s m out :=
  Proofs.run_iff (coreConfig s m) _ (fun h => core_sound h) (fun h => core_step_iff.mp h) guard

end Core

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (m : ModuleInst) (a : State) :
    (v1Config s m a).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) m a :=
  Proofs.v1_to_lime s m a

theorem lime_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (m : ModuleInst) (a : State) :
    (limeConfig s m a).toCore = coreConfig s.toCore m.toCore a :=
  Proofs.lime_to_core s m a

end Silmaril.Wasm.Institution.Operational.Blocks
