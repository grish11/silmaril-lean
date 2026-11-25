module

public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryQuery.Proofs

open Silmaril.Wasm.Execution
open Silmaril.Wasm.Execution.Runtime (Frame MemAddr MemInst)

theorem run_iff {C : Type} (emit : State → C) (native : C → C → Prop) (bytes : ByteArray)
    (sound : ∀ {a b}, Edge bytes a b → native (emit a) (emit b))
    (readback : ∀ {a b}, native (emit a) b → ∃ out, Edge bytes a out ∧ b = emit out)
    {a : State} {b : C} :
    Relation.ReflTransGen native (emit a) b ↔
      ∃ out, Relation.ReflTransGen (Edge bytes) a out ∧ b = emit out := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨a, .refl, rfl⟩
    | tail _ step ih =>
      obtain ⟨middle, path, rfl⟩ := ih
      obtain ⟨out, edge, rfl⟩ := readback step
      exact ⟨out, path.tail edge, rfl⟩
  · rintro ⟨out, path, rfl⟩
    exact Relation.ReflTransGen.lift emit (fun _ _ h => sound h) _ _ path

theorem memory_toCore {H : Type} {s : Wasm.Lime1.Execution.Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m)) :
    s.toCore.mem? f.toCore index = some (a.value, m.toCore) := by
  unfold Wasm.Lime1.Execution.frameMemory at lookup
  cases fmem : f.module.memories[0]? with
  | none => simp [fmem] at lookup
  | some addr =>
    cases smem : s.memories[addr.value]? with
    | none => simp [fmem, smem] at lookup
    | some inst =>
      simp [fmem, smem] at lookup
      obtain ⟨rfl, rfl⟩ := lookup
      simp [Core.Store.mem?, index, Runtime.Frame.toCore, Runtime.ModuleInst.toCore,
        Runtime.Store.toCore, List.getElem?_map, Idx.toNat, fmem, smem]

end Silmaril.Wasm.Institution.Operational.MemoryQuery.Proofs
