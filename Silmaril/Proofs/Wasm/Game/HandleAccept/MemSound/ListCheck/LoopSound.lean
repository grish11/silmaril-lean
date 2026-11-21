module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Thms
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Sound
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Basic
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Take
import Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopSound

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Items Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck
  Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop Silmaril.Wasm.Logic.Hoare
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
open Silmaril.Wasm.Logic.Core (Outcome Post bytesAt leNat load_eq)
open Silmaril.Wasm.Game.HandleAccept.Memory (MemAtom)
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound (hwp_call stubOk stubOk_spec)
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items (X.load32)
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck
  (ChildKind list_items_ans list_child_ans readAccept_inv' readAccept_two)
open Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers (X.localGet X.localSet X.i32Const X.if_
  X.rel32 X.add32 X.return_ X.br0 X.loop Leaves)
open Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Take (rel_eq_ne rel_eq_z rel_gtu_z)
open Silmaril.Proofs.Wasm.Game.HandleAccept.Mixed.Chunk.Ring (X.sub32)

abbrev Contract (ix : ListImports) (kind : Set SymStrBytesSExp)
    (env : Env (BitVec 32) SymStrBytesSExp) :=
  readerContract ix.toRead env (boundedListsOf kind) itemsReply

def Inv (kind : Set SymStrBytesSExp) (env : Env (BitVec 32) SymStrBytesSExp)
    (root : BitVec 32) (inst : ModuleInst) (funcs : List (FuncInst Nat))
    (store : Store Nat) (frame : Frame) : Prop :=
  store.funcs = funcs ∧ store.mems.length = 1 ∧
    ∃ index base offset : BitVec 32,
      frame = ⟨[some (.i32 root), some (.i32 index), some (.i32 base), some (.i32 offset)], inst⟩ ∧
      index.toNat ≤ 2 ^ 30 ∧
      ∀ children, env root = some (SExp.ofList children) →
        CheckedPrefix kind env root children index.toNat

private theorem mul32 {P : Profile} {host : HostSemantics Nat} {s : Store Nat}
    {f : Frame} {us : List Val} {rest : List Instr} {Q : Post Nat} {x y : BitVec 32}
    (next : HWP P host s f (vals (us ++ [.i32 (x * y)]) ++ expression rest) Q) :
    HWP P host s f (vals (us ++ [.i32 x] ++ [.i32 y]) ++
      expression (.intBinOp .i32 .mul :: rest)) Q := by
  rw [List.append_assoc]
  exact Wp.intBinOp (m := .part) (t := .i32) (x := x) (y := y) (z := x * y) rfl next

private theorem loadedWord {mem : ByteArray} {addr : Nat} {actual : BitVec 32}
    (loaded : Execution.Memory.load mem addr 4 = some actual) (bound : addr + 4 ≤ mem.size) :
    actual.setWidth 32 = BitVec.ofNat 32 (leNat (bytesAt mem ⟨addr, 4⟩)) := by
  obtain rfl := Option.some.inj (loaded.symm.trans (load_eq bound))
  simp

theorem round {P : Profile} {ix : ListImports} {module_ : Module}
    (imports : module_.imports = (Loop.mod ix).imports)
    {reply : UCall Nat → UReply → Prop} {Stable : Store Nat → Prop}
    (replyOK : ∀ call answer, reply call answer →
      itemsReply call answer ∧ (Stable call.store → Stable answer.store))
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)} {kind : Set SymStrBytesSExp}
    (childKind : ChildKind ans kind) (distinct : ix.child ≠ ix.items)
    {env : Env (BitVec 32) SymStrBytesSExp} {root : BitVec 32}
    {inst : ModuleInst} (hFuncs : inst.funcs = [0, 1, 2, 3]) (hMems : inst.mems = [0])
    {funcs : List (FuncInst Nat)} {items child accept : FuncInst Nat}
    (atItems : funcs[0]? = some items) (atChild : funcs[1]? = some child)
    (atAccept : funcs[2]? = some accept) (stubItems : stubOk 0 2 items = true)
    (stubChild : stubOk 1 2 child = true) (stubAccept : stubOk 2 1 accept = true)
    {store : Store Nat} {frame : Frame} (initial : Inv kind env root inst funcs store frame)
    (entryStable : Stable store) {Q : Post Nat}
    (exits : ∀ st : Store Nat, st.funcs = funcs → st.mems.length = 1 → Stable st → Leaves Q st) :
    HWP P (memHost module_ (some 0) (listRoles ix ans)
      (readerContract ix.toRead env (boundedListsOf kind) reply)) store frame
      (vals [] ++ expression iteration)
      (loopPost 0 [] (fun st fr stack => stack = [] ∧ Stable st ∧ Inv kind env root inst funcs st fr) Q) := by
  obtain ⟨entryFuncs, entryMems, index, oldBase, oldOffset, rfl, bounded, invariant⟩ := initial
  obtain ⟨_, _, itemsCode, itemsType, itemsCount⟩ := stubOk_spec stubItems
  obtain ⟨_, _, childCode, childType, childCount⟩ := stubOk_spec stubChild
  obtain ⟨_, _, acceptCode, acceptType, acceptCount⟩ := stubOk_spec stubAccept
  let post := loopPost 0 [] (fun st fr stack => stack = [] ∧ Stable st ∧ Inv kind env root inst funcs st fr) Q
  have leave : ∀ st : Store Nat, st.funcs = funcs → st.mems.length = 1 → Stable st → Leaves post st :=
    fun st hfs hms stable => (exits st hfs hms stable).loop
  unfold iteration
  refine X.localGet (v := .i32 root) rfl ?_
  refine X.i32Const (us := [] ++ [.i32 root]) ?_
  refine hwp_call (us := []) (args := [.i32 root, .i32 0]) (x := ⟨0⟩) (k := 0)
    (fk := items) (i := ⟨ix.items.1, ix.items.2, .func ⟨0⟩⟩) (by rw [hFuncs]; rfl)
    (by rw [entryFuncs]; exact atItems) itemsCode itemsType (by simp [itemsCount]) (by rw [imports]; rfl)
    (fun _ read => absurd read (readAccept_two rfl)) ?_
  intro readStore readResult readReply readOK
  obtain ⟨⟨⟨readFuncs, readMems⟩, readShape⟩, readStable⟩ := replyOK _ _ readReply
  have readFuncs' := readFuncs.trans entryFuncs
  have readMems' := readMems.trans entryMems
  have readStable' := readStable entryStable
  have readLeaves := leave readStore readFuncs' readMems' readStable'
  refine ⟨fun result values => ?_, fun _ => (readLeaves _).2.1,
    fun error _ => (readLeaves _).2.2 error⟩
  obtain rfl := readShape result values
  subst values
  refine X.localGet (v := .i32 index) rfl ?_
  refine X.i32Const (us := [] ++ [.i32 index]) ?_
  refine X.load32 (us := [] ++ [.i32 index])
    (F := ⟨[some (.i32 root), some (.i32 index), some (.i32 oldBase), some (.i32 oldOffset)], inst⟩)
    hMems readMems' (readLeaves _).2.1 ?_
  intro memory size atMemory rawSize
  obtain ⟨handles, read, children, denotes, aligned⟩ :=
    list_items_ans (S := kind) atMemory readOK
  obtain ⟨base, headerBound, headerBase, headerSize, fullRange, pointerAt⟩ := items_loads read
  have checked := invariant children denotes
  obtain ⟨sameLength, handleAt⟩ := reread_prefix checked denotes aligned
  have sizeNat : (size.setWidth 32).toNat = children.length := by
    rw [← sameLength, headerSize]
    exact congrArg BitVec.toNat (loadedWord rawSize (by simpa [effAddr] using headerBound))
  refine X.rel32 (us := []) ?_
  refine X.if_ (us := []) (fun done => ?_) (fun more => ?_)
  · have complete : index.toNat = children.length :=
      (congrArg BitVec.toNat (rel_eq_ne done)).trans sizeNat
    refine X.localGet (v := .i32 root) rfl ?_
    refine hwp_call (us := []) (args := [.i32 root]) (x := ⟨2⟩) (k := 2)
      (fk := accept) (i := ⟨ix.accept.1, ix.accept.2, .func ⟨1⟩⟩) (by rw [hFuncs]; rfl)
      (by rw [readFuncs']; exact atAccept) acceptCode acceptType (by simp [acceptCount])
      (by rw [imports]; rfl) ?_ ?_
    · intro handle decoded tree found
      have sameHandle : handle = root := i32_inj (readAccept_inv' rfl decoded)
      subst handle
      refine ⟨children, complete ▸ bounded, ?_, Option.some.inj (found.symm.trans denotes)⟩
      intro child member
      obtain ⟨position, atPosition⟩ := List.mem_iff_getElem?.mp member
      obtain ⟨within, rfl⟩ := List.getElem?_eq_some_iff.mp atPosition
      exact checked.2.2 position within (complete.symm ▸ within)
    intro final result finalReply _
    obtain ⟨⟨⟨finalFuncs, finalMems⟩, finalShape⟩, finalStable⟩ := replyOK _ _ finalReply
    have finalLeaves := leave final (finalFuncs.trans readFuncs') (finalMems.trans readMems')
      (finalStable readStable')
    refine ⟨fun vals returned => ?_, fun _ => (finalLeaves _).2.1,
      fun error _ => (finalLeaves _).2.2 error⟩
    obtain rfl := finalShape vals returned
    exact X.return_ ((finalLeaves _).1 [])
  · have before : index.toNat < children.length := by
      have different : index.toNat ≠ (size.setWidth 32).toNat :=
        fun equal => rel_eq_z more (BitVec.eq_of_toNat_eq equal)
      have leLength := checked.2.1
      omega
    refine X.localGet (v := .i32 index) rfl ?_
    refine X.i32Const (us := [] ++ [.i32 index]) ?_
    refine X.rel32 (us := []) ?_
    refine X.if_ (us := []) (fun _ => Wp.unreachable (m := .part) (us := [])
      (readLeaves.label _).2.1) (fun indexGuard => ?_)
    have indexBound : index.toNat ≤ 1073741823 := rel_gtu_z indexGuard
    refine X.localGet (v := .i32 index) rfl ?_
    refine X.i32Const (us := [] ++ [.i32 index]) ?_
    refine mul32 (us := []) ?_
    refine X.localSet (x := ⟨3⟩) (by change 3 < 4; decide) ?_
    refine X.i32Const (us := []) ?_
    refine X.load32 (us := []) (by exact hMems) readMems' (readLeaves _).2.1 ?_
    intro memAgain ptr atMemoryAgain rawPtr
    have sameMemory := Option.some.inj (atMemory.symm.trans atMemoryAgain)
    subst memAgain
    have ptrEq : ptr.setWidth 32 = base := by
      rw [headerBase]
      exact loadedWord rawPtr (by omega)
    rw [ptrEq]
    refine X.localSet (x := ⟨2⟩) (by change 2 < 4; decide) ?_
    refine X.localGet (v := .i32 base) rfl ?_
    refine X.i32Const (us := [] ++ [.i32 base]) ?_
    refine X.localGet (v := .i32 (index * 4)) rfl ?_
    refine X.sub32 (us := [] ++ [.i32 base]) ?_
    refine X.rel32 (us := []) ?_
    refine X.if_ (us := []) (fun _ => Wp.unreachable (m := .part) (us := [])
      (readLeaves.label _).2.1) (fun baseGuard => ?_)
    have offsetNat : (index * 4).toNat = 4 * index.toNat := by
      rw [BitVec.toNat_mul]
      change (index.toNat * 4) % 2 ^ 32 = 4 * index.toNat
      rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm index.toNat 4]
    have baseBound := rel_gtu_z baseGuard
    have limit : ((4294967292 : BitVec 32) - index * 4).toNat =
        4294967292 - 4 * index.toNat := by
      have order : index * 4 ≤ (4294967292 : BitVec 32) := by
        rw [BitVec.le_def, offsetNat]
        change 4 * index.toNat ≤ 4294967292
        omega
      rw [BitVec.toNat_sub_of_le order, offsetNat]
      rfl
    have guarded : Addressable base index := ⟨indexBound, limit ▸ baseBound⟩
    refine X.localGet (v := .i32 base) rfl ?_
    refine X.localGet (v := .i32 (index * 4)) rfl ?_
    refine X.add32 (us := []) ?_
    refine X.load32 (us := []) (by exact hMems) readMems' (readLeaves _).2.1 ?_
    intro childMemory childWord atChildMemory rawChild
    have sameChildMemory : childMemory = memory := Option.some.inj (atChildMemory.symm.trans atMemory)
    subst childMemory
    have within : index.toNat < handles.length := by omega
    have childEq : childWord.setWidth 32 = handles[index.toNat] := by
      rw [pointerAt index.toNat within]
      change Memory.load memory.bytes (base + index * 4).toNat 4 = some childWord at rawChild
      rw [address_eq guarded] at rawChild
      exact loadedWord rawChild (by omega)
    rw [childEq]
    refine X.i32Const (us := [] ++ [.i32 handles[index.toNat]]) ?_
    refine hwp_call (us := []) (args := [.i32 handles[index.toNat], .i32 0]) (x := ⟨1⟩) (k := 1)
      (fk := child) (i := ⟨ix.child.1, ix.child.2, .func ⟨0⟩⟩)
      (by change inst.funcs[1]? = some 1; rw [hFuncs]; rfl)
      (by rw [readFuncs']; exact atChild) childCode childType (by simp [childCount]) (by rw [imports]; rfl)
      (fun _ decoded => absurd decoded (readAccept_two rfl)) ?_
    intro next result nextReply childOK
    obtain ⟨⟨⟨nextFuncs, nextMems⟩, nextShape⟩, nextStable⟩ := replyOK _ _ nextReply
    have nextFuncs' := nextFuncs.trans readFuncs'
    have nextMems' := nextMems.trans readMems'
    have nextStable' := nextStable readStable'
    have nextLeaves := leave next nextFuncs' nextMems' nextStable'
    refine ⟨fun res returned => ?_, fun _ => (nextLeaves _).2.1, fun error _ => (nextLeaves _).2.2 error⟩
    obtain rfl := nextShape res returned
    subst returned
    have checkedMore := advance_prefix checked before (handleAt index.toNat within before)
      (list_child_ans (s := readStore) childKind distinct childOK)
    refine X.localGet (v := .i32 index) rfl ?_
    refine X.i32Const (us := [] ++ [.i32 index]) ?_
    refine X.add32 (us := []) ?_
    refine X.localSet (x := ⟨1⟩) (by change 1 < 4; decide) ?_
    refine X.br0 ⟨[], [], rfl, rfl, rfl, nextStable', nextFuncs', nextMems', _, _, _, rfl, ?_⟩
    refine ⟨?_, ?_⟩
    · change (index + (1 : BitVec 32)).toNat ≤ 2 ^ 30
      rw [next_index guarded]
      omega
    intro children' same
    have sameChildren := SExp.ofList_injective (Option.some.inj (same.symm.trans denotes))
    subst children'
    change CheckedPrefix kind env root children (index + 1).toNat
    exact Eq.mp (congrArg (CheckedPrefix kind env root children) (next_index guarded).symm) checkedMore

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopSound
