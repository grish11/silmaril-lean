module

public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms
public import Silmaril.Wasm.SingleThreaded.Determinism.Head
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryQuery.Core
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryQuery.V1
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryQuery.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryQuery.Transport

/-! Exact native successor and finite endpoint readback for memory32 queries.
The selected memory must resolve at index zero. Core uses the empty host. -/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryQuery

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame MemAddr MemInst)
open Silmaril.Wasm.SingleThreaded.Det (noHost)

section V1
variable {H : Type} {host : Wasm.V1.Execution.HostSemantics H} {s : Wasm.V1.Execution.Store H} {f : Frame}
variable {a : MemAddr} {m : MemInst}

theorem v1_sound (lookup : Wasm.V1.Execution.frameMemory s f = some (a, m))
    {query out : State} (edge : Edge m.data query out) :
    Wasm.V1.Execution.Step host (v1Config s f query) (v1Config s f out) :=
  Proofs.V1.sound lookup edge

theorem v1_readback (lookup : Wasm.V1.Execution.frameMemory s f = some (a, m))
    {query : State} {target : Wasm.V1.Execution.Config H} (step : Wasm.V1.Execution.Step host (v1Config s f query) target) :
    ∃ out, Edge m.data query out ∧ target = v1Config s f out := by
  obtain ⟨out, _, edge, eq⟩ := Proofs.V1.readback step query (List.Sublist.refl _) lookup
  exact ⟨out, edge, eq⟩

theorem v1_run_iff (lookup : Wasm.V1.Execution.frameMemory s f = some (a, m))
    {query : State} {target : Wasm.V1.Execution.Config H} :
    Relation.ReflTransGen (Wasm.V1.Execution.Step host) (v1Config s f query) target ↔
      ∃ out, Relation.ReflTransGen (Edge m.data) query out ∧ target = v1Config s f out :=
  Proofs.run_iff (v1Config s f) _ _ (fun h => v1_sound lookup h)
    (fun h => v1_readback lookup h)

end V1

section Lime1
variable {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H} {s : Wasm.Lime1.Execution.Store H} {f : Frame}
variable {a : MemAddr} {m : MemInst}

theorem lime_sound (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m))
    {query out : State} (edge : Edge m.data query out) :
    Wasm.Lime1.Execution.Step host (limeConfig s f query) (limeConfig s f out) :=
  Proofs.Lime1.sound lookup edge

theorem lime_readback (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m))
    {query : State} {target : Wasm.Lime1.Execution.Config H} (step : Wasm.Lime1.Execution.Step host (limeConfig s f query) target) :
    ∃ out, Edge m.data query out ∧ target = limeConfig s f out := by
  obtain ⟨out, _, edge, eq⟩ := Proofs.Lime1.readback step query (List.Sublist.refl _) lookup
  exact ⟨out, edge, eq⟩

theorem lime_run_iff (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m))
    {query : State} {target : Wasm.Lime1.Execution.Config H} :
    Relation.ReflTransGen (Wasm.Lime1.Execution.Step host) (limeConfig s f query) target ↔
      ∃ out, Relation.ReflTransGen (Edge m.data) query out ∧ target = limeConfig s f out :=
  Proofs.run_iff (limeConfig s f) _ _ (fun h => lime_sound lookup h)
    (fun h => lime_readback lookup h)

end Lime1

section Core
variable {H : Type} {P : Wasm.Numerics.Profile} {s : Core.Store H} {f : Core.Frame}
variable {a : Nat} {m : Core.MemInst}

theorem core_sound (lookup : s.mem? f index = some (a, m)) (is32 : m.type.address = .i32)
    {query out : State} (edge : Edge m.bytes query out) :
    Core.Step P noHost (coreConfig s f query) (coreConfig s f out) :=
  Proofs.core_sound lookup is32 edge

theorem core_readback (lookup : s.mem? f index = some (a, m)) (is32 : m.type.address = .i32)
    {query : State} {target : Core.Config H} (step : Core.Step P noHost (coreConfig s f query) target) :
    ∃ out, Edge m.bytes query out ∧ target = coreConfig s f out := Proofs.core_readback lookup is32 step

theorem core_run_iff (lookup : s.mem? f index = some (a, m)) (is32 : m.type.address = .i32)
    {query : State} {target : Core.Config H} :
    Relation.ReflTransGen (Core.Step P noHost) (coreConfig s f query) target ↔
      ∃ out, Relation.ReflTransGen (Edge m.bytes) query out ∧ target = coreConfig s f out :=
  Proofs.run_iff (coreConfig s f) _ _ (fun h => core_sound lookup is32 h)
    (fun h => core_readback lookup is32 h)

end Core

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (f : Frame) (query : State) :
    (v1Config s f query).toLime =
      limeConfig (s.mapCode Wasm.V1.Func.toLime) f query := by
  cases query <;> rfl

theorem lime_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Frame) (query : State) :
    (limeConfig s f query).toCore =
      coreConfig s.toCore f.toCore query := by
  cases query <;> rfl

theorem memory_toCore {H : Type} {s : Wasm.Lime1.Execution.Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m)) :
    s.toCore.mem? f.toCore index = some (a.value, m.toCore) :=
  Proofs.memory_toCore lookup

end Silmaril.Wasm.Institution.Operational.MemoryQuery
