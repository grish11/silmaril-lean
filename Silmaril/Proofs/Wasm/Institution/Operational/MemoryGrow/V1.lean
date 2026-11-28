module

public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Thms
import Silmaril.Wasm.Versions.Lime1.Execution.Thms
import Silmaril.Wasm.RuntimeMap.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryGrow.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryGrow.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryGrow.Proofs.V1

open Execution
open Execution.Runtime
open Wasm.V1.Execution

theorem sound {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (lookup : frameMemory s f = some (a, m)) {q b : State} (edge : Edge m q b) :
    Step host (v1Config s f a m q) (v1Config s f a m b) := by
  cases invert edge with
  | grow delta bytes grown => exact .memoryGrow s f a m delta _ bytes lookup (.success bytes grown)
  | fail delta =>
    have reset : setMemory s a m = s := by simp [setMemory, set_current s.memories f lookup]
    have step := Step.memoryGrow (host := host) s f a m delta (-1) m.data lookup .failure
    cases m
    simp only [reset] at step
    exact step

private theorem config_injective (H : Type) : Function.Injective (Config.toLime (H := H)) := by
  rintro ⟨s, f, xs⟩ ⟨t, g, ys⟩ eq
  have stores := RuntimeMap.store_mapCode_injective Wasm.V1.Func.toLime_injective
    (congrArg (fun c : Wasm.Lime1.Execution.Config H => c.store) eq)
  have frames : f = g := congrArg (fun c : Wasm.Lime1.Execution.Config H => c.frame) eq
  have codes := RuntimeMap.adminInstr_mapList_injective Wasm.V1.Instr.toLime_injective xs ys
    (congrArg (fun c : Wasm.Lime1.Execution.Config H => c.code) eq)
  cases stores
  cases frames
  cases codes
  rfl

theorem readback {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {a : MemAddr} {m : MemInst}
    (lookup : frameMemory s f = some (a, m)) {q : State} {b : Config H}
    (step : Step host (v1Config s f a m q) b) :
    ∃ out, Edge m q out ∧ b = v1Config s f a m out := by
  have translated := step.toLime (Runtime.HostSemantics.compatible_mapCode Wasm.V1.Func.toLime host)
  rw [Proofs.v1_to_lime] at translated
  have mapped := (map_frameMemory s f).trans lookup
  obtain ⟨out, edge, eq⟩ := Proofs.Lime1.readback mapped translated
  exact ⟨out, edge, config_injective H (eq.trans (Proofs.v1_to_lime s f a m out).symm)⟩

theorem request_cases_iff {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {a : MemAddr}
    {m : MemInst} {delta : BitVec 32} {dst : Config H} (lookup : frameMemory s f = some (a, m)) :
    Step host (v1Config s f a m (.request delta)) dst ↔
      dst = v1Config s f a m .failed ∨
      (SizeAllows m delta.toNat ∧ dst = v1Config s f a m
        (.grown (m.data ++ ⟨Array.replicate (delta.toNat * Memory.pageSize) 0⟩))) := by
  constructor
  · intro step
    obtain ⟨out, edge, eq⟩ := readback lookup step
    cases invert edge with
    | fail => exact .inl eq
    | grow _ bytes grew =>
      obtain ⟨limits, rfl⟩ := grow_eq_some_iff.mp grew
      exact .inr ⟨limits, eq⟩
  · rintro (rfl | ⟨limits, rfl⟩)
    · exact sound lookup (fact (.fail delta))
    · exact sound lookup (fact (.grow delta _ (grow_eq_some_iff.mpr ⟨limits, rfl⟩)))

theorem size_cases_iff {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame} {a : MemAddr}
    {m : MemInst} {dst : Config H} (lookup : frameMemory s f = some (a, m)) :
    Step host ⟨s, f, [.source .memorySize]⟩ dst ↔
      dst = ⟨s, f, values [Value.int .i32 (BitVec.ofNat 32 (Memory.size m.data))]⟩ := by
  constructor
  · intro step
    obtain ⟨out, edge, eq⟩ := MemoryQuery.v1_readback lookup (query := .size) step
    cases MemoryQuery.invert edge
    exact eq
  · rintro rfl
    exact .memorySize _ _ _ _ lookup

end Silmaril.Wasm.Institution.Operational.MemoryGrow.Proofs.V1
