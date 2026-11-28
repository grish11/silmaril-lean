module

public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Native.Defs
public import Silmaril.Wasm.Institution.Operational.MemoryGrow.Thms
public import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
public import Silmaril.Wasm.Execution.Core.Step
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryGrow.V1
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryGrow.Lime1
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryGrow.Core
import Silmaril.Proofs.Wasm.Institution.Operational.MemoryGrow.Transport

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryGrow

open Execution
open Execution.Runtime (Frame MemAddr MemInst Value)

section v1
variable {H : Type} {host : Wasm.V1.Execution.HostSemantics H}
  {s : Wasm.V1.Execution.Store H} {f : Frame} {a : MemAddr} {m : MemInst}

theorem v1_sound
    (lookup : Wasm.V1.Execution.frameMemory s f = some (a, m)) {q b : State} (edge : Edge m q b) :
    Wasm.V1.Execution.Step host (v1Config s f a m q) (v1Config s f a m b) :=
  Proofs.V1.sound lookup edge

theorem v1_step_iff
    (lookup : Wasm.V1.Execution.frameMemory s f = some (a, m)) {q : State} {b : Wasm.V1.Execution.Config H} :
    Wasm.V1.Execution.Step host (v1Config s f a m q) b ↔
      ∃ out, Edge m q out ∧ b = v1Config s f a m out :=
  ⟨Proofs.V1.readback lookup, fun ⟨_, edge, eq⟩ => eq.symm ▸ v1_sound lookup edge⟩

/-- Failure returns all ones with the same store. Success requires alignment
and the page limits, extends by zero-filled pages, and returns the old size. -/
theorem v1_request_cases_iff {delta : BitVec 32} {dst : Wasm.V1.Execution.Config H}
    (lookup : Wasm.V1.Execution.frameMemory s f = some (a, m)) :
    Wasm.V1.Execution.Step host (v1Config s f a m (.request delta)) dst ↔
      dst = v1Config s f a m .failed ∨
      (SizeAllows m delta.toNat ∧ dst = v1Config s f a m
        (.grown (m.data ++ ⟨Array.replicate (delta.toNat * Memory.pageSize) 0⟩))) :=
  Proofs.V1.request_cases_iff lookup

open Wasm.V1.Execution in
/-- The current page count is read from the selected memory, preserving the store and frame. -/
theorem v1_size_cases_iff {dst : Config H} (lookup : frameMemory s f = some (a, m)) :
    Step host ⟨s, f, [.source .memorySize]⟩ dst ↔
      dst = ⟨s, f, values [Value.int .i32 (BitVec.ofNat 32 (Memory.size m.data))]⟩ :=
  Proofs.V1.size_cases_iff lookup

theorem v1_run_iff
    (lookup : Wasm.V1.Execution.frameMemory s f = some (a, m)) {q : State} {b : Wasm.V1.Execution.Config H} :
    Relation.ReflTransGen (Wasm.V1.Execution.Step host) (v1Config s f a m q) b ↔
      ∃ out, Runs m q out ∧ b = v1Config s f a m out :=
  Proofs.run_iff (v1Config s f a m) _ (fun e => v1_sound lookup e)
    (fun step => (v1_step_iff lookup).mp step)

end v1

section lime
variable {H : Type} {host : Wasm.Lime1.Execution.HostSemantics H}
  {s : Wasm.Lime1.Execution.Store H} {f : Frame} {a : MemAddr} {m : MemInst}

theorem lime_sound
    (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m)) {q b : State} (edge : Edge m q b) :
    Wasm.Lime1.Execution.Step host (limeConfig s f a m q) (limeConfig s f a m b) :=
  Proofs.Lime1.sound lookup edge

theorem lime_step_iff
    (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m)) {q : State} {b : Wasm.Lime1.Execution.Config H} :
    Wasm.Lime1.Execution.Step host (limeConfig s f a m q) b ↔
      ∃ out, Edge m q out ∧ b = limeConfig s f a m out :=
  ⟨Proofs.Lime1.readback lookup, fun ⟨_, edge, eq⟩ => eq.symm ▸ lime_sound lookup edge⟩

theorem lime_run_iff
    (lookup : Wasm.Lime1.Execution.frameMemory s f = some (a, m)) {q : State} {b : Wasm.Lime1.Execution.Config H} :
    Relation.ReflTransGen (Wasm.Lime1.Execution.Step host) (limeConfig s f a m q) b ↔
      ∃ out, Runs m q out ∧ b = limeConfig s f a m out :=
  Proofs.run_iff (limeConfig s f a m) _ (fun e => lime_sound lookup e)
    (fun step => (lime_step_iff lookup).mp step)

end lime

section core
variable {H : Type} {host : Core.HostSemantics H}
  {s : Core.Store H} {f : Core.Frame} {a : Nat} {m : MemInst}

theorem core_sound (guard : Admitted m)
    (lookup : s.mem? f MemoryQuery.index = some (a, m.toCore)) {q b : State} (edge : Edge m q b) :
    Core.Step Numerics.Profile.spec host (coreConfig s f a m q) (coreConfig s f a m b) :=
  Proofs.core_sound guard lookup edge

theorem core_step_iff (guard : Admitted m)
    (lookup : s.mem? f MemoryQuery.index = some (a, m.toCore)) {q : State} {b : Core.Config H} :
    Core.Step Numerics.Profile.spec host (coreConfig s f a m q) b ↔
      ∃ out, Edge m q out ∧ b = coreConfig s f a m out :=
  ⟨Proofs.core_readback guard lookup, fun ⟨_, edge, eq⟩ => eq.symm ▸ core_sound guard lookup edge⟩

theorem core_run_iff (guard : Admitted m)
    (lookup : s.mem? f MemoryQuery.index = some (a, m.toCore)) {q : State} {b : Core.Config H} :
    Relation.ReflTransGen (Core.Step Numerics.Profile.spec host) (coreConfig s f a m q) b ↔
      ∃ out, Runs m q out ∧ b = coreConfig s f a m out :=
  Proofs.run_iff (coreConfig s f a m) _ (fun e => core_sound guard lookup e)
    (fun step => (core_step_iff guard lookup).mp step)

end core

theorem v1_to_lime {H : Type} (s : Wasm.V1.Execution.Store H) (f : Frame)
    (a : MemAddr) (m : MemInst) (q : State) :
    (v1Config s f a m q).toLime = limeConfig (s.mapCode Wasm.V1.Func.toLime) f a m q :=
  Proofs.v1_to_lime s f a m q

theorem lime_to_core {H : Type} (s : Wasm.Lime1.Execution.Store H) (f : Frame)
    (a : MemAddr) (m : MemInst) (q : State) :
    (limeConfig s f a m q).toCore = coreConfig s.toCore f.toCore a.value m q :=
  Proofs.lime_to_core s f a m q

theorem grow_toCore {m : MemInst} (guard : Admitted m) (delta : Nat) :
    m.toCore.grow? delta = (Memory.grow? m.data m.max delta).map
      (fun bytes => ({ m with data := bytes } : MemInst).toCore) :=
  Proofs.grow_toCore guard delta

end Silmaril.Wasm.Institution.Operational.MemoryGrow
