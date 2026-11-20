module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing.Defs
public import Silmaril.Wasm.Execution.Core.Properties
import Silmaril.Wasm.Logic.Core.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.ReserveReplay

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing (reserve)
open Silmaril.Wasm.Logic.Core (Step.ctx Steps.append)

private theorem measure {profile : Profile} {host : HostSemantics Nat}
    {store : Store Nat} {frame : Frame} {requested : BitVec 32} {memory : MemInst} {tail : List Admin}
    (requestLocal : frame.local? ⟨1⟩ = some (some (.i32 requested)))
    (lookup : store.mem? frame ⟨0⟩ = some (0, memory)) (width : memory.type.address = .i32) :
    Steps profile host ⟨store, frame, expression [.localGet ⟨1⟩, .memorySize ⟨0⟩] ++ tail⟩
      ⟨store, frame, vals [.i32 requested, .i32 (BitVec.ofNat 32 memory.pages)] ++ tail⟩ := by
  have asI32 : aconst memory.type.address (BitVec.ofNat _ memory.pages) =
      constI32 (BitVec.ofNat 32 memory.pages) := by
    obtain ⟨⟨_, _⟩, _⟩ := memory
    cases width
    rfl
  have size : Step profile host ⟨store, frame, [.plain (.memorySize ⟨0⟩)]⟩
      ⟨store, frame, [aconst memory.type.address (BitVec.ofNat _ memory.pages)]⟩ := .memory (.size lookup)
  rw [asI32] at size
  exact (Step.ctx [] _ (.variable (.localGet requestLocal))).steps.trans
    (Step.ctx [.i32 requested] tail size).steps

private theorem skip_if {profile : Profile} {host : HostSemantics Nat} {store : Store Nat}
    {frame : Frame} {branch : List Instr} {tail : List Admin} :
    Steps profile host ⟨store, frame, constI32 0 :: .plain (.if_ .empty branch []) :: tail⟩
      ⟨store, frame, tail⟩ := by
  refine (Step.ctx [] tail (Step.ifFalse (b₁ := branch) (b₂ := []))).steps.trans ?_
  refine (Step.ctx [] tail (Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl)).steps.trans ?_
  exact (Step.ctx [] tail (Step.labelVals (n := 0) (cont := []) (vs := []))).steps

private theorem take_if {profile : Profile} {host : HostSemantics Nat} {store next : Store Nat}
    {frame : Frame} {branch : List Instr} {tail : List Admin} {test : BitVec 32} (taken : test ≠ 0)
    (runs : Steps profile host ⟨store, frame, expression branch⟩ ⟨next, frame, []⟩) :
    Steps profile host ⟨store, frame, constI32 test :: .plain (.if_ .empty branch []) :: tail⟩
      ⟨next, frame, tail⟩ := by
  refine (Step.ctx [] tail (Step.ifTrue taken)).steps.trans ?_
  refine (Step.ctx [] tail (Step.block (vs := []) (t₁ := []) (t₂ := []) rfl rfl)).steps.trans ?_
  exact (Steps.append tail (runs.label (n := 0) (cont := []))).trans
    (Step.ctx [] tail (Step.labelVals (n := 0) (cont := []) (vs := []))).steps

@[expose] def Succeeds (profile : Profile) (store reached : Store Nat) (memory : MemInst)
    (requested : BitVec 32) : Prop :=
    (requested.toNat ≤ memory.pages ∧ reached = store) ∨
      (memory.pages < requested.toNat ∧ ∃ grown,
        memory.grow? (requested.toNat - memory.pages) = some grown ∧
        profile.growMaySucceed .memory 0 memory.pages (requested.toNat - memory.pages) ∧
        reached = store.setMem 0 grown)

theorem steps_of_success {profile : Profile} {host : HostSemantics Nat} {store reached : Store Nat}
    {frame : Frame} {memory : MemInst} {requested : BitVec 32} {tail : List Instr}
    (requestLocal : frame.local? ⟨1⟩ = some (some (.i32 requested))) (localBound : 1 < frame.locals.length)
    (lookup : store.mem? frame ⟨0⟩ = some (0, memory)) (width : memory.type.address = .i32)
    (pageBound : memory.pages ≤ 65536) (success : Succeeds profile store reached memory requested) :
    Steps profile host ⟨store, frame, expression (reserve ++ tail)⟩
      ⟨reached, frame.setLocal ⟨1⟩ (.i32 0), expression tail⟩ := by
  let pages := BitVec.ofNat 32 memory.pages
  have pageNat : pages.toNat = memory.pages := by
    dsimp only [pages]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  let branch : List Instr := [.localGet ⟨1⟩, .memorySize ⟨0⟩, .intBinOp .i32 .sub, .memoryGrow ⟨0⟩,
    .intConst .i32 (BitVec.allOnes 32), .intRelOp .i32 .eq, .if_ .empty [.unreachable] []]
  let reset := expression (.intConst .i32 0 :: .localSet ⟨1⟩ :: tail)
  let tests := .plain (.if_ .empty branch []) :: reset
  change Steps profile host
    ⟨store, frame, expression [.localGet ⟨1⟩, .memorySize ⟨0⟩] ++
      .plain (.intRelOp .i32 (.gt .unsigned)) :: tests⟩ _
  refine (measure requestLocal lookup width).trans ?_
  refine (Step.ctx [] tests (.numeric (.intRelOp (t := .i32)))).steps.trans ?_
  have clear : Steps profile host ⟨reached, frame, reset⟩
      ⟨reached, frame.setLocal ⟨1⟩ (.i32 0), expression tail⟩ :=
    (Step.ctx [] (expression tail) (.variable (.localSet (x := ⟨1⟩) (v := .i32 0) localBound))).steps
  refine Relation.ReflTransGen.trans ?_ clear
  rcases success with ⟨enough, same⟩ | ⟨needsGrowth, grown, grow, allowed, same⟩
  · subst reached
    have comparison : intRelOp .i32 (.gt .unsigned) requested pages = 0 := by
      change bool32 (decide (requested.toNat > pages.toNat)) = 0
      simp [bool32, pageNat, Nat.not_lt.mpr enough]
    change Steps profile host
      ⟨store, frame, constI32 (intRelOp .i32 (.gt .unsigned) requested pages) :: tests⟩ _
    rw [comparison]
    exact skip_if
  · subst reached
    have comparison : intRelOp .i32 (.gt .unsigned) requested pages ≠ 0 := by
      change bool32 (decide (requested.toNat > pages.toNat)) ≠ 0
      simp [bool32, pageNat, needsGrowth]
    have order : pages ≤ requested := by rw [BitVec.le_def, pageNat]; omega
    have delta : (requested - pages).toNat = requested.toNat - memory.pages := by
      rw [BitVec.toNat_sub_of_le order, pageNat]
    have notSentinel : pages ≠ BitVec.allOnes 32 := by
      intro equal
      rw [equal] at pageNat
      change 4294967295 = memory.pages at pageNat
      omega
    refine take_if comparison ?_
    let guard := expression [.intConst .i32 (BitVec.allOnes 32), .intRelOp .i32 .eq,
      .if_ .empty [.unreachable] []]
    change Steps profile host
      ⟨store, frame, expression [.localGet ⟨1⟩, .memorySize ⟨0⟩] ++
        .plain (.intBinOp .i32 .sub) :: .plain (.memoryGrow ⟨0⟩) :: guard⟩ _
    refine (measure requestLocal lookup width).trans ?_
    refine (Step.ctx [] (.plain (.memoryGrow ⟨0⟩) :: guard)
      (.numeric (.intBinOp (t := .i32) (z := requested - pages) rfl))).steps.trans ?_
    refine (Step.ctx [] guard (.memory (.growSucceed (a := .i32) lookup
      (delta.symm ▸ grow) (delta.symm ▸ allowed)))).steps.trans ?_
    refine (Step.ctx [] [.plain (.if_ .empty [.unreachable] [])] (.numeric (.intRelOp (t := .i32)))).steps.trans ?_
    have comparison : intRelOp .i32 .eq pages (BitVec.allOnes 32) = 0 := by
      change bool32 (pages == BitVec.allOnes 32) = 0
      have unequal : (pages == BitVec.allOnes 32) = false := by simpa using notSentinel
      rw [unequal]
      rfl
    change Steps profile host ⟨store.setMem 0 grown, frame,
      [constI32 (intRelOp .i32 .eq pages (BitVec.allOnes 32)), .plain (.if_ .empty [.unreachable] [])]⟩ _
    rw [comparison]
    exact skip_if (tail := [])

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.ReserveReplay
