module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Native.Defs
public import Silmaril.Wasm.Institution.Operational.CallResolution.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.V1
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Lime1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

theorem v1_step_iff {H : Type} {host : Wasm.V1.Execution.HostSemantics H}
    {s : Wasm.V1.Execution.Store H} {f : Frame} {i : FuncIdx} {dst : Wasm.V1.Execution.Config H} :
    Wasm.V1.Execution.Step host (v1Config s f (.call i)) dst ↔
      ∃ a, Edge f.module.funcs (.call i) (.invoke a) ∧ dst = v1Config s f (.invoke a) :=
  Proofs.V1.step_iff

theorem lime_step_iff {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H}
    {s : Wasm.Lime1.Execution.Store H} {f : Frame} {i : FuncIdx} {dst : Wasm.Lime1.Execution.Config H} :
    Wasm.Lime1.Execution.Step host (limeConfig s f (.call i)) dst ↔
      ∃ a, Edge f.module.funcs (.call i) (.invoke a) ∧ dst = limeConfig s f (.invoke a) :=
  Proofs.Lime1.step_iff

theorem core_sound {H : Type} {P : Wasm.Numerics.Profile} {s : Wasm.Lime1.Execution.Store H}
    {f : Frame} {i : FuncIdx} (guard : Allocated s f i) {a : Runtime.FuncAddr}
    (edge : Edge f.module.funcs (.call i) (.invoke a)) :
    Core.Step P noHost (limeConfig s f (.call i)).toCore (limeConfig s f (.invoke a)).toCore :=
  Proofs.core_sound guard edge

theorem core_readback {H : Type} {P : Wasm.Numerics.Profile} {s : Wasm.Lime1.Execution.Store H}
    {f : Frame} {i : FuncIdx} {dst : Core.Config H}
    (step : Core.Step P noHost (limeConfig s f (.call i)).toCore dst) :
    ∃ a, Edge f.module.funcs (.call i) (.invoke a) ∧ (s.funcs[a.value]?).isSome ∧
      dst = (limeConfig s f (.invoke a)).toCore :=
  Proofs.core_readback step

theorem core_step_iff {H : Type} {P : Wasm.Numerics.Profile} {s : Wasm.Lime1.Execution.Store H}
    {f : Frame} {i : FuncIdx} (guard : Allocated s f i) {dst : Core.Config H} :
    Core.Step P noHost (limeConfig s f (.call i)).toCore dst ↔
      ∃ a, Edge f.module.funcs (.call i) (.invoke a) ∧ dst = (limeConfig s f (.invoke a)).toCore :=
  ⟨fun h => let ⟨a, edge, _, eq⟩ := core_readback h; ⟨a, edge, eq⟩,
    fun ⟨_, edge, eq⟩ => eq.symm ▸ core_sound guard edge⟩

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (f : Frame) (q : State) :
    (v1Config s f q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) f q := by
  cases q <;> rfl

end Silmaril.Wasm.Institution.Operational.CallResolution
