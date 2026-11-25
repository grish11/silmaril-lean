module

public import Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData.Defs
import Silmaril.X86.MemoryModel.Tso.Thms

public section

namespace Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockFifoData

open Silmaril.Elf.Staged.Pinned.GlibcLibc.MutexUnlock.FifoData
open Silmaril.X86.Ext (leBytes length_leBytes)
open Silmaril.X86.MemoryModel.Tso

private theorem out_of_entry (address start : Nat) (bytes : List Byte)
    (outside : address < start ∨ start + bytes.length ≤ address) :
    entryByte start bytes address = none := by
  unfold entryByte
  split
  · exact List.getElem?_eq_none (by omega)
  · rfl

private theorem readMem_eq_of_span {m n : Mem} (start length : Nat)
    (equal : ∀ offset < length, m (start + offset) = n (start + offset)) :
    readMem m start length = readMem n start length := by
  induction length generalizing start with
  | zero => rfl
  | succ length previous =>
    have first := equal 0 (by omega)
    have rest : ∀ offset < length, m (start + 1 + offset) = n (start + 1 + offset) := by
      intro offset inside
      simpa [Nat.add_assoc, Nat.add_comm 1 offset] using equal (offset + 1) (by omega)
    simp only [readMem, Nat.add_zero] at first ⊢
    rw [first, previous _ rest]

theorem buffer_and_release (initial : XState Nat) (tid base : Nat) (users : BitVec 32)
    (empty : initial.buffer tid = [])
    (lock : readMem initial.memory base 4 = some [1, 0, 0, 0]) :
    ∃ queued drained final,
      queued = enqueue (enqueue (enqueue initial tid (base + 4) zeroDword)
        tid (base + 12) (usersDword users)) tid (base + 8) zeroDword ∧
      Execution XStep initial (stores tid base users) queued ∧
      queued.buffer tid =
        [(base + 4, zeroDword), (base + 12, usersDword users), (base + 8, zeroDword)] ∧
      queued.memory = initial.memory ∧
      XFlushes queued drained ∧ drained.buffer tid = [] ∧
      viewMem queued tid = drained.memory ∧
      (∀ address, address < base + 4 ∨ base + 16 ≤ address →
        drained.memory address = initial.memory address) ∧
      XWeakStep queued (.rmw tid base [1, 0, 0, 0] zeroDword) final ∧
      final.memory = writeMem (committedStores initial.memory base users) base zeroDword ∧
      (∀ peer, peer ≠ tid → final.buffer peer = initial.buffer peer) := by
  let afterDepth := enqueue initial tid (base + 4) zeroDword
  let afterUsers := enqueue afterDepth tid (base + 12) (usersDword users)
  let queued := enqueue afterUsers tid (base + 8) zeroDword
  have queuedStores : queued.buffer tid =
      [(base + 4, zeroDword), (base + 12, usersDword users), (base + 8, zeroDword)] := by
    simp [queued, afterUsers, afterDepth, enqueue, empty]
  have issue : Execution XStep initial (stores tid base users) queued :=
    .cons (.store _ _ _ _) (.cons (.store _ _ _ _) (.cons (.store _ _ _ _) (.nil _)))
  let depthFlushed : XState Nat :=
    ⟨writeMem queued.memory (base + 4) zeroDword,
      Function.update queued.buffer tid [(base + 12, usersDword users), (base + 8, zeroDword)]⟩
  let usersFlushed : XState Nat :=
    ⟨writeMem depthFlushed.memory (base + 12) (usersDword users),
      Function.update depthFlushed.buffer tid [(base + 8, zeroDword)]⟩
  let drained : XState Nat :=
    ⟨writeMem usersFlushed.memory (base + 8) zeroDword,
      Function.update usersFlushed.buffer tid []⟩
  have first : XFlush queued depthFlushed := .head _ _ _ _ _ queuedStores
  have second : XFlush depthFlushed usersFlushed := .head _ _ _ _ _ (by simp [depthFlushed])
  have third : XFlush usersFlushed drained := .head _ _ _ _ _ (by simp [usersFlushed])
  have propagation : XFlushes queued drained :=
    (Relation.ReflTransGen.single first).tail second |>.tail third
  have drainedEmpty : drained.buffer tid = [] := by simp [drained]
  have forwarding : viewMem queued tid = drained.memory := by
    funext address
    simp only [viewMem, queuedStores, readBufByte, drained, usersFlushed, depthFlushed, writeMem]
    cases entryByte (base + 8) zeroDword address <;>
      cases entryByte (base + 12) (usersDword users) address <;>
      cases entryByte (base + 4) zeroDword address <;> rfl
  have frame (address : Nat) (outside : address < base + 4 ∨ base + 16 ≤ address) :
      drained.memory address = initial.memory address := by
    have zeros : zeroDword.length = 4 := rfl
    have usersLength : (usersDword users).length = 4 := by simp [usersDword]
    have afterOwner := out_of_entry address (base + 8) zeroDword (by rw [zeros]; omega)
    have afterUsers := out_of_entry address (base + 12) (usersDword users) (by rw [usersLength]; omega)
    have afterDepth := out_of_entry address (base + 4) zeroDword (by rw [zeros]; omega)
    simp only [drained, usersFlushed, depthFlushed, writeMem, afterOwner, afterUsers, afterDepth,
      Option.none_or]
    rfl
  have old : readMem drained.memory base 4 = some [1, 0, 0, 0] := by
    rw [readMem_eq_of_span base 4 (fun offset inside => frame (base + offset) (.inl (by omega)))]
    exact lock
  let final := {drained with memory := writeMem drained.memory base zeroDword}
  have release : XWeakStep queued (.rmw tid base [1, 0, 0, 0] zeroDword) final :=
    ⟨drained, final, propagation, .rmw _ _ _ _ _ drainedEmpty old rfl, .refl⟩
  refine ⟨queued, drained, final, rfl, issue, queuedStores, rfl, propagation, drainedEmpty,
    forwarding, frame, release, rfl, ?_⟩
  intro peer other
  simp only [final, drained, usersFlushed, depthFlushed, queued, afterUsers, afterDepth, enqueue,
    Function.update_of_ne other]

private theorem no_forward_at (address start : Nat) (bytes : List Byte)
    (previous : List (Nat × List Byte)) (noneAt : entryByte start bytes address = none) :
    readBufByte address (previous ++ [(start, bytes)]) = readBufByte address previous := by
  induction previous with
  | nil => simp [readBufByte, noneAt]
  | cons head rest previousEq => simp only [List.cons_append, readBufByte, previousEq]

private theorem readView_enqueue_disjoint (state : XState Nat) (tid start address length : Nat)
    (bytes : List Byte)
    (apart : address + length ≤ start ∨ start + bytes.length ≤ address) :
    readView (enqueue state tid start bytes) tid address length = readView state tid address length := by
  unfold readView
  apply readMem_eq_of_span
  intro offset inside
  have noneAt := out_of_entry (address + offset) start bytes (by omega)
  simp [viewMem, enqueue, no_forward_at (address + offset) start bytes (state.buffer tid) noneAt]

theorem data_and_release (initial : XState Nat) (tid base : Nat) (users kind : BitVec 32)
    (empty : initial.buffer tid = [])
    (depth : readView initial tid (base + 4) 4 = some [1, 0, 0, 0])
    (count : readView initial tid (base + 12) 4 = some (leBytes (users.setWidth 64) 4))
    (kindRead : readView initial tid (base + 16) 4 = some (leBytes (kind.setWidth 64) 4))
    (flag : readView initial tid 0x20c040 1 = some [0])
    (flagApart : 0x20c041 ≤ base + 4 ∨ base + 16 ≤ 0x20c040)
    (lock : readMem initial.memory base 4 = some [1, 0, 0, 0]) :
    ∃ final, Execution XWeakStep initial (dataEvents tid base users kind) final ∧
      final.buffer tid = [] ∧
      final.memory = writeMem (committedStores initial.memory base users) base zeroDword ∧
      ∀ peer, peer ≠ tid → final.buffer peer = initial.buffer peer := by
  obtain ⟨queued, _, final, actual, _, _, _, _, _, _, _, release, memory, peers⟩ :=
    buffer_and_release initial tid base users empty lock
  subst queued
  let afterDepth := enqueue initial tid (base + 4) zeroDword
  let afterUsers := enqueue afterDepth tid (base + 12) (usersDword users)
  let afterOwner := enqueue afterUsers tid (base + 8) zeroDword
  have zs : zeroDword.length = 4 := rfl
  have us : (usersDword users).length = 4 := by simp [usersDword]
  have countAfter : readView afterDepth tid (base + 12) 4 = some (leBytes (users.setWidth 64) 4) := by
    unfold afterDepth
    rw [readView_enqueue_disjoint _ _ _ _ _ _ (.inr (by rw [zs]; omega))]
    exact count
  have kindAfter : readView afterOwner tid (base + 16) 4 = some (leBytes (kind.setWidth 64) 4) := by
    unfold afterOwner afterUsers afterDepth
    rw [readView_enqueue_disjoint _ _ _ _ _ _ (.inr (by rw [zs]; omega)),
      readView_enqueue_disjoint _ _ _ _ _ _ (.inr (by rw [us])),
      readView_enqueue_disjoint _ _ _ _ _ _ (.inr (by rw [zs]; omega))]
    exact kindRead
  have flagAfter : readView afterOwner tid 0x20c040 1 = some [0] := by
    unfold afterOwner afterUsers afterDepth
    rw [readView_enqueue_disjoint _ _ _ _ _ _ (by rw [zs]; omega),
      readView_enqueue_disjoint _ _ _ _ _ _ (by rw [us]; omega),
      readView_enqueue_disjoint _ _ _ _ _ _ (by rw [zs]; omega)]
    exact flag
  have first : XWeakStep initial (.load tid (base + 4) [1, 0, 0, 0]) initial :=
    ⟨_, _, .refl, .load _ _ _ _ depth, .refl⟩
  have second : XWeakStep initial (.store tid (base + 4) zeroDword) afterDepth :=
    ⟨_, _, .refl, .store _ _ _ _, .refl⟩
  have third : XWeakStep afterDepth (.load tid (base + 12) (leBytes (users.setWidth 64) 4)) afterDepth :=
    ⟨_, _, .refl, .load _ _ _ _ (by simpa only [length_leBytes] using countAfter), .refl⟩
  have fourth : XWeakStep afterDepth (.store tid (base + 12) (usersDword users)) afterUsers :=
    ⟨_, _, .refl, .store _ _ _ _, .refl⟩
  have fifth : XWeakStep afterUsers (.store tid (base + 8) zeroDword) afterOwner :=
    ⟨_, _, .refl, .store _ _ _ _, .refl⟩
  have sixth : XWeakStep afterOwner (.load tid (base + 16) (leBytes (kind.setWidth 64) 4)) afterOwner :=
    ⟨_, _, .refl, .load _ _ _ _ (by simpa only [length_leBytes] using kindAfter), .refl⟩
  have seventh : XWeakStep afterOwner (.load tid 0x20c040 [0]) afterOwner :=
    ⟨_, _, .refl, .load _ _ _ _ flagAfter, .refl⟩
  exact ⟨final, .cons first (.cons second (.cons third (.cons fourth (.cons fifth
    (.cons sixth (.cons seventh (.cons release (.nil _)))))))), weak_rmw_empty release, memory, peers⟩

end Silmaril.Proofs.Elf.Staged.Pinned.GlibcLibc.MutexUnlockFifoData
