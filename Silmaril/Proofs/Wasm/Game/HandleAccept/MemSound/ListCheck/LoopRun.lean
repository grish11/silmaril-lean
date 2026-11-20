module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Thms
public import Silmaril.Wasm.Logic.Core.Thms
import Silmaril.Wasm.Logic.Arith.Thms
import Silmaril.Wasm.Logic.Memory.Thms

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Game.HandleAccept.MemSound (itemsList)
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop

def locals (inst : ModuleInst) (root index base offset : BitVec 32) : Frame :=
  ⟨[some (.i32 root), some (.i32 index), some (.i32 base), some (.i32 offset)], inst⟩

private abbrev slice (start size : Nat) : List Instr := (iteration.drop start).take size

private theorem straight {profile : Profile} {host : HostSemantics Nat}
    {store : Store Nat} {frame next : Frame} {before after : List Val}
    {instrs : List Instr} {tail : List Admin}
    (run : exec store frame before.reverse instrs = some (store, next, after.reverse)) :
    Steps profile host ⟨store, frame, vals before ++ expression instrs ++ tail⟩
      ⟨store, next, vals after ++ tail⟩ := by
  simpa only [List.reverse_reverse] using exec_sound (P := profile) (host := host) tail run

private theorem skip_if {profile : Profile} {host : HostSemantics Nat}
    {store : Store Nat} {frame : Frame} {branch : List Instr} {tail : List Admin} :
    Steps profile host
      ⟨store, frame, (Val.i32 0).toAdmin :: .plain (.if_ .empty branch []) :: tail⟩
      ⟨store, frame, tail⟩ := by
  refine (Relation.ReflTransGen.single (Step.ctx [] tail (Step.ifFalse (b₁ := branch) (b₂ := [])))).trans ?_
  refine (Relation.ReflTransGen.single
    (Step.ctx [] tail (Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl))).trans ?_
  exact .single (Step.ctx [] tail (Step.labelVals (n := 0) (cont := []) (vs := [])))

private theorem compare_count {store : Store Nat} {inst : ModuleInst} {memory : MemInst}
    (memoryAddr : inst.mems[0]? = some 0) (atMemory : store.mems[0]? = some memory)
    {root index base offset count : BitVec 32} (read : Memory.load memory.bytes 4 4 = some count) :
    exec store (locals inst root index base offset) [] (slice 3 4) =
      some (store, locals inst root index base offset, [.i32 (bool32 (index == count))]) := by
  change exec store _ [] [.localGet ⟨1⟩, .intConst .i32 0, .intLoad .i32 none ⟨0⟩ ⟨0, 4⟩,
    .intRelOp .i32 .eq] = _
  simp [exec, exec1, popInt, localVal?, Frame.local?, locals, Val.i32, Store.mem?,
    Idx.toNat, IntType.width, memoryAddr, atMemory, effAddr, read]

private theorem compare_index {store : Store Nat} {inst : ModuleInst}
    {root index base offset : BitVec 32} (bound : index.toNat ≤ 1073741823) :
    exec store (locals inst root index base offset) [] (slice 8 3) =
      some (store, locals inst root index base offset, [.i32 0]) := by
  have compared : intRelOp .i32 (.gt .unsigned) index (1073741823 : BitVec 32) = 0 := by
    refine (intRelOp_i32_gtU index 1073741823).trans ?_
    change bool32 (decide (index.toNat > 1073741823)) = 0
    simp [bool32, Nat.not_lt.mpr bound]
  exact congrArg (fun value => some (store, locals inst root index base offset, [Val.i32 value])) compared

private theorem compare_base {store : Store Nat} {inst : ModuleInst} {memory : MemInst}
    (memoryAddr : inst.mems[0]? = some 0) (atMemory : store.mems[0]? = some memory)
    {root index oldBase oldOffset base : BitVec 32} (read : Memory.load memory.bytes 0 4 = some base)
    (guard : Addressable base index) :
    exec store (locals inst root index oldBase oldOffset) [] (slice 12 12) =
      some (store, locals inst root index base (index * 4), [.i32 0]) := by
  have offsetNat : (index * 4).toNat = 4 * index.toNat := by
    rw [BitVec.toNat_mul]
    change (index.toNat * 4) % 2 ^ 32 = 4 * index.toNat
    obtain ⟨bound, _⟩ := guard
    rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm index.toNat 4]
  have limit : ((4294967292 : BitVec 32) - index * 4).toNat = 4294967292 - 4 * index.toNat := by
    have order : index * 4 ≤ (4294967292 : BitVec 32) := by
      rw [BitVec.le_def, offsetNat]
      exact Nat.mul_le_mul_left 4 guard.1
    rw [BitVec.toNat_sub_of_le order, offsetNat]
    rfl
  let threshold : BitVec 32 := 4294967292 - index * 4
  have compared : intRelOp .i32 (.gt .unsigned) base threshold = 0 := by
    refine (intRelOp_i32_gtU base threshold).trans ?_
    change bool32 (decide (base.toNat > ((4294967292 : BitVec 32) - index * (4 : BitVec 32)).toNat)) = 0
    rw [limit]
    simp [bool32, Nat.not_lt.mpr guard.2]
  change exec store _ [] [.localGet ⟨1⟩, .intConst .i32 4, .intBinOp .i32 .mul, .localSet ⟨3⟩,
    .intConst .i32 0, .intLoad .i32 none ⟨0⟩ ⟨0, 0⟩, .localSet ⟨2⟩, .localGet ⟨2⟩,
    .intConst .i32 4294967292, .localGet ⟨3⟩, .intBinOp .i32 .sub, .intRelOp .i32 (.gt .unsigned)] = _
  simp [exec, exec1, popInt, popV, localVal?, Frame.local?, Frame.setLocal, locals, Val.i32,
    Store.mem?, Idx.toNat, IntType.width, memoryAddr, atMemory, effAddr, read, -intRelOp_i32_gtU]
  congr 1

private theorem load_child {store : Store Nat} {inst : ModuleInst} {memory : MemInst}
    (memoryAddr : inst.mems[0]? = some 0) (atMemory : store.mems[0]? = some memory)
    {root index base handle : BitVec 32}
    (read : Memory.load memory.bytes (base + index * 4).toNat 4 = some handle) :
    exec store (locals inst root index base (index * 4)) [] (slice 25 5) =
      some (store, locals inst root index base (index * 4), [.i32 0, .i32 handle]) := by
  change exec store _ [] [.localGet ⟨2⟩, .localGet ⟨3⟩, .intBinOp .i32 .add,
    .intLoad .i32 none ⟨0⟩ ⟨0, 0⟩, .intConst .i32 0] = _
  simp at read
  simp [exec, exec1, popInt, localVal?, Frame.local?, locals, Val.i32, Store.mem?,
    Idx.toNat, IntType.width, memoryAddr, atMemory, effAddr, read]

/-- From a decoded, guarded reply, the actual guest reaches the next child call,
with the handle from the corresponding vector entry. -/
theorem to_child {profile : Profile} {host : HostSemantics Nat}
    {store : Store Nat} {inst : ModuleInst} {memory : MemInst}
    (memoryAddr : inst.mems[0]? = some 0) (atMemory : store.mems[0]? = some memory)
    {handles : List (BitVec 32)} (decoded : itemsList memory.bytes 0 = some handles)
    {root index oldBase oldOffset : BitVec 32} (before : index.toNat < handles.length)
    (width : memory.bytes.size ≤ 2 ^ 32) :
    ∃ base, Addressable base index ∧
      Steps profile host ⟨store, locals inst root index oldBase oldOffset, expression (iteration.drop 3)⟩
        ⟨store, locals inst root index base (index * 4),
          vals [.i32 handles[index.toNat], .i32 0] ++ expression (iteration.drop 30)⟩ := by
  obtain ⟨base, headerFits, baseWord, countLen, storage, childWord⟩ := items_loads decoded
  let count := BitVec.ofNat 32 (leNat (bytesAt memory.bytes ⟨4, 4⟩))
  have readCount : Memory.load memory.bytes 4 4 = some count := load_eq headerFits
  have readBase : Memory.load memory.bytes 0 4 = some base := by rw [baseWord]; exact load_eq (by omega)
  have guard : Addressable base index := addressable_iff.mpr (by omega)
  have readChild : Memory.load memory.bytes (base + index * 4).toNat 4 = some handles[index.toNat] := by
    rw [address_eq guard, childWord index.toNat before]
    exact load_eq (by omega)
  have different : (index == count) = false := by
    apply Bool.eq_false_iff.mpr
    intro equal
    have same : index = count := beq_iff_eq.mp equal
    rw [same, ← countLen] at before
    exact Nat.lt_irrefl _ before
  have countRun := compare_count (root := root) (index := index) (base := oldBase) (offset := oldOffset)
    memoryAddr atMemory readCount
  rw [different] at countRun
  have start := straight (profile := profile) (host := host) (before := []) (after := [.i32 0])
    (tail := expression (iteration.drop 7)) countRun
  have testIndex := straight (profile := profile) (host := host) (before := []) (after := [.i32 0])
    (tail := expression (iteration.drop 11)) (compare_index (store := store) (inst := inst)
      (root := root) (index := index) (base := oldBase) (offset := oldOffset) guard.1)
  have testBase := straight (profile := profile) (host := host) (before := []) (after := [.i32 0])
    (tail := expression (iteration.drop 24)) (compare_base (root := root) (index := index)
      (oldBase := oldBase) (oldOffset := oldOffset) memoryAddr atMemory readBase guard)
  have finish := straight (profile := profile) (host := host) (before := [])
    (after := [.i32 handles[index.toNat], .i32 0]) (tail := expression (iteration.drop 30))
    (load_child (root := root) (index := index) (base := base) memoryAddr atMemory readChild)
  refine ⟨base, guard, ?_⟩
  exact start.trans ((skip_if (branch := [.localGet ⟨0⟩, .call ⟨2⟩, .return_])
    (tail := expression (iteration.drop 8))).trans (testIndex.trans
    ((skip_if (branch := [.unreachable]) (tail := expression (iteration.drop 12))).trans
      (testBase.trans ((skip_if (branch := [.unreachable])
        (tail := expression (iteration.drop 25))).trans finish)))))

/-- At the exact list length the guest takes the accepting branch before trying any load
of a child, including when the vector is empty. -/
theorem to_accept {profile : Profile} {host : HostSemantics Nat}
    {store : Store Nat} {inst : ModuleInst} {memory : MemInst}
    (memoryAddr : inst.mems[0]? = some 0) (atMemory : store.mems[0]? = some memory)
    {handles : List (BitVec 32)} (decoded : itemsList memory.bytes 0 = some handles)
    {root index base offset : BitVec 32} (finished : index.toNat = handles.length) :
    Steps profile host ⟨store, locals inst root index base offset, expression (iteration.drop 3)⟩
      ⟨store, locals inst root index base offset,
        .label 0 [] (vals [.i32 root] ++ expression [.call ⟨2⟩, .return_]) ::
          expression (iteration.drop 8)⟩ := by
  obtain ⟨_, headerFits, _, countLen, _, _⟩ := items_loads decoded
  have readCount : Memory.load memory.bytes 4 4 = some index := by
    have equal := BitVec.eq_of_toNat_eq (finished.trans countLen)
    rw [equal]
    exact load_eq headerFits
  have countRun := compare_count (root := root) (index := index) (base := base) (offset := offset)
    memoryAddr atMemory readCount
  have run := straight (profile := profile) (host := host) (before := []) (after := [.i32 1])
    (tail := expression (iteration.drop 7)) (by simpa [bool32] using countRun)
  let branch : List Instr := [.localGet ⟨0⟩, .call ⟨2⟩, .return_]
  let tail := expression (iteration.drop 8)
  let frame := locals inst root index base offset
  have enterBranch : Step profile host
      ⟨store, frame, (Val.i32 1).toAdmin :: .plain (.if_ .empty branch []) :: tail⟩
      ⟨store, frame, .plain (.block .empty branch) :: tail⟩ :=
    Step.ctx [] tail (Step.ifTrue (by decide))
  have enterBlock : Step profile host ⟨store, frame, .plain (.block .empty branch) :: tail⟩
      ⟨store, frame, .label 0 [] (expression branch) :: tail⟩ :=
    Step.ctx [] tail (Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl)
  have argument : Steps profile host ⟨store, frame, expression branch⟩
      ⟨store, frame, vals [.i32 root] ++ expression [.call ⟨2⟩, .return_]⟩ :=
    straight (before := []) (after := [.i32 root]) (instrs := [.localGet ⟨0⟩]) rfl
  exact run.trans (enterBranch.steps.trans (enterBlock.steps.trans (Steps.append tail argument.label)))

/-- Resuming a child reply increments the index once and branches to another `items` call. -/
theorem back_edge {profile : Profile} {host : HostSemantics Nat}
    {store : Store Nat} {inst : ModuleInst} {root index base offset : BitVec 32} :
    Steps profile host ⟨store, locals inst root index base offset,
      [.label 0 body (expression (iteration.drop 31))]⟩
      ⟨store, locals inst root (index + 1) base offset,
        [.label 0 body (expression iteration)]⟩ := by
  have bump : Steps profile host
      ⟨store, locals inst root index base offset, expression (iteration.drop 31)⟩
      ⟨store, locals inst root (index + 1) base offset, [.plain (.br ⟨0⟩)]⟩ :=
    straight (before := []) (after := []) (instrs := slice 31 4) rfl
  have jump : Step profile host
      ⟨store, locals inst root (index + 1) base offset, [.label 0 body [.plain (.br ⟨0⟩)]]⟩
      ⟨store, locals inst root (index + 1) base offset, expression body⟩ :=
    Step.brLabelZero (vs' := []) (vs := []) (l := ⟨0⟩) (rest := []) rfl rfl
  have restart : Step profile host ⟨store, locals inst root (index + 1) base offset, expression body⟩
      ⟨store, locals inst root (index + 1) base offset, [.label 0 body (expression iteration)]⟩ :=
    Step.loop (vs := []) (t₁ := []) (t₂ := []) rfl rfl
  exact bump.label.trans (jump.steps.trans restart.steps)

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun
