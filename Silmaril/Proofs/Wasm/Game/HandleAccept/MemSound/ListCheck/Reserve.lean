module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Basic
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Take

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Reserve

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post)
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing (reserve)
open Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers (X.localGet X.localSet X.i32Const X.if_ X.blockEnd)
open Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Take (rel_eq_ne)

theorem grow_pages {memory grown : MemInst} {delta : Nat} (growth : memory.grow? delta = some grown) :
    grown.pages = memory.pages + delta := by
  unfold MemInst.grow? at growth
  dsimp only at growth
  split at growth
  · obtain rfl := Option.some.inj growth
    change (memory.bytes ++ ⟨Array.replicate (delta * Execution.Memory.pageSize) 0⟩).size /
      Execution.Memory.pageSize = memory.pages + delta
    rw [ByteArray.size_append]
    change (memory.bytes.size + (Array.replicate (delta * Execution.Memory.pageSize) (0 : UInt8)).size) /
      Execution.Memory.pageSize = memory.bytes.size / Execution.Memory.pageSize + delta
    rw [Array.size_replicate, Nat.add_mul_div_right _ _ (by decide : 0 < Execution.Memory.pageSize)]
  · cases growth

theorem grow_memory32 {memory grown : MemInst} {delta : Nat} (width : memory.type.address = .i32)
    (growth : memory.grow? delta = some grown) : grown.type.address = .i32 ∧ grown.pages ≤ 65536 := by
  have pages := grow_pages growth
  unfold MemInst.grow? at growth
  dsimp only at growth
  split at growth
  · rename_i allowed
    obtain rfl := Option.some.inj growth
    refine ⟨width, pages.trans_le ?_⟩
    have capacity := allowed.1
    rw [width] at capacity
    exact capacity
  · cases growth

theorem reserve_hwp {profile : Profile} {host : HostSemantics Nat} {store : Store Nat} {frame : Frame}
    {memory : MemInst} {requested : BitVec 32} {tail : List Instr} {post : Post Nat}
    (requestLocal : frame.local? ⟨1⟩ = some (some (.i32 requested))) (localBound : 1 < frame.locals.length)
    (lookup : store.mem? frame ⟨0⟩ = some (0, memory)) (width : memory.type.address = .i32)
    (pageBound : memory.pages ≤ 65536)
    (resume : ∀ current reached, requested.toNat ≤ reached.pages →
      ((current = store ∧ reached = memory) ∨
        (memory.grow? (requested.toNat - memory.pages) = some reached ∧ current = store.setMem 0 reached)) →
      HWP profile host current (frame.setLocal ⟨1⟩ (.i32 0)) (expression tail) post)
    (traps : post store frame .trap) :
    HWP profile host store frame (expression (reserve ++ tail)) post := by
  let pages := BitVec.ofNat 32 memory.pages
  have read : addrVal memory.type.address (BitVec.ofNat _ memory.pages) = .i32 pages := by
    obtain ⟨⟨_, _⟩, _⟩ := memory
    cases width
    rfl
  have pageNat : pages.toNat = memory.pages := by
    dsimp only [pages]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have notSentinel : pages ≠ BitVec.allOnes 32 := by
    intro equal
    rw [equal] at pageNat
    change 4294967295 = memory.pages at pageNat
    omega
  have reset : ∀ current reached, requested.toNat ≤ reached.pages →
      ((current = store ∧ reached = memory) ∨
        (memory.grow? (requested.toNat - memory.pages) = some reached ∧ current = store.setMem 0 reached)) →
      HWP profile host current frame (vals [] ++ expression (.intConst .i32 0 :: .localSet ⟨1⟩ :: tail)) post := by
    intro current reached capacity result
    refine X.i32Const (us := []) (X.localSet (us := []) localBound ?_)
    exact resume current reached capacity result
  unfold reserve
  simp only [List.cons_append, List.nil_append]
  refine X.localGet (us := []) requestLocal ?_
  refine Wp.memorySize (m := .part) (us := [.i32 requested]) (x := ⟨0⟩) lookup ?_
  rw [read]
  refine Wp.intRelOp (m := .part) (t := .i32) (us := []) ?_
  refine X.if_ (us := []) (fun larger => ?_) (fun enough => ?_)
  · simp [intRelOp, bool32] at larger
    change pages.toNat < requested.toNat at larger
    have needsGrowth : memory.pages < requested.toNat := pageNat ▸ larger
    have order : pages ≤ requested := BitVec.le_def.mpr (Nat.le_of_lt larger)
    have delta : (requested - pages).toNat = requested.toNat - memory.pages := by
      rw [BitVec.toNat_sub_of_le order, pageNat]
    refine X.localGet (us := []) requestLocal ?_
    refine Wp.memorySize (m := .part) (us := [.i32 requested]) (x := ⟨0⟩) lookup ?_
    rw [read]
    refine Wp.intBinOp (m := .part) (t := .i32) (us := []) (z := requested - pages) rfl ?_
    refine Wp.memoryGrow (m := .part) (a := .i32) (us := []) (x := ⟨0⟩) lookup ?_ ?_
    · intro grown growth _
      change memory.grow? ((requested - pages).toNat) = some grown at growth
      rw [delta] at growth
      have capacity : requested.toNat ≤ grown.pages := by rw [grow_pages growth]; omega
      rw [show addrVal .i32 (BitVec.ofNat _ memory.pages) = .i32 pages from rfl]
      refine X.i32Const (us := [.i32 pages]) ?_
      refine Wp.intRelOp (m := .part) (t := .i32) (us := []) ?_
      refine X.if_ (us := []) (fun impossible => ?_) (fun _ => ?_)
      · exact (notSentinel (rel_eq_ne impossible)).elim
      · exact X.blockEnd (reset _ _ capacity (.inr ⟨growth, rfl⟩))
    · intro _
      refine X.i32Const (us := [.i32 (BitVec.allOnes 32)]) ?_
      refine Wp.intRelOp (m := .part) (t := .i32) (us := []) ?_
      refine X.if_ (us := []) (fun _ => ?_) (fun impossible => ?_)
      · exact Wp.unreachable (m := .part) traps
      · simp [intRelOp, bool32] at impossible
  · simp [intRelOp, bool32] at enough
    change requested.toNat ≤ pages.toNat at enough
    exact reset store memory (enough.trans_eq pageNat) (.inl ⟨rfl, rfl⟩)

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Reserve
