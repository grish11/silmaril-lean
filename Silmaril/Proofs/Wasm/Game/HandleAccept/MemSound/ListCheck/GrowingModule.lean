module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Run.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopModule
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rules
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Reserve
import Silmaril.Wasm.Execution.Core.Soundness.PureRedex

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.GrowingModule

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation Silmaril.Wasm.Logic.Hoare
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
open Silmaril.Wasm.Game.HandleAccept.MemSound
open Silmaril.Wasm.Game.HandleAccept.MemSound.Items (itemsReply tyItems)
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing (Memory32 reserve reply)
open Silmaril.Wasm.Game.HandleAccept.MemSound.Readers (symTextAns blobAns)
open Silmaril.Wasm.Game.HandleAccept.Memory (MemAtom)
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
open Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers (X.loop)
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck
  (ChildKind symTextAns_kind blobAns_kind)

private theorem itemsSize {memory bytes : ByteArray} {handles : List (BitVec 32)}
    (encoded : writeItemsReply memory handles = .ok bytes) : bytes.size = memory.size := by
  unfold writeItemsReply at encoded
  split at encoded
  · cases encoded
  split at encoded
  · cases encoded
  dsimp only at encoded
  split at encoded
  · rename_i updated write
    cases encoded
    exact Execution.Memory.writeBytes_size _ _ _ _ write
  · cases encoded

private theorem childSize {memory bytes : ByteArray} {raw : List UInt8}
    (encoded : writeByteReply memory raw = .ok bytes) : bytes.size = memory.size := by
  unfold writeByteReply at encoded
  split at encoded
  · cases encoded
  split at encoded
  · cases encoded
  dsimp only at encoded
  split at encoded
  · rename_i updated write
    cases encoded
    exact Execution.Memory.writeBytes_size _ _ _ _ write
  · cases encoded

private theorem write_preserves {store : Store Nat} {memory : MemInst} {bytes : ByteArray}
    (slot : store.mems = [memory]) (size : bytes.size = memory.bytes.size) (before : Memory32 store) :
    Memory32 (store.setMem 0 { memory with bytes }) := by
  obtain ⟨actual, stored, width, pages⟩ := before
  have same : actual = memory := List.singleton_inj.mp (stored.symm.trans slot)
  subst actual
  refine ⟨{ memory with bytes }, by simp [Store.setMem, slot], width, ?_⟩
  simpa only [MemInst.pages, size] using pages

theorem byte_reply_admitted (store : Store Nat) (handles : List (BitVec 32)) (raw : BitVec 32 → List UInt8) :
    ReplyEnvs reply store (byteReplyHost handles raw) := by
  intro state call answer next answered
  change ScriptReply handles (fun memory handle => writeByteReply memory (raw handle)) call answer at answered
  constructor
  · cases answered <;> simp [itemsReply, ShapedReply, KeepsCode, Store.setMem]
  · cases answered with
    | items slot encoded => exact write_preserves slot (itemsSize encoded)
    | child slot _ encoded => exact write_preserves slot (childSize encoded)
    | itemsError | childError | accept => exact id

@[expose] def validatedType : CModuleType :=
  let types := allocTypes [tyItems, Hi.tyAcc]
  let items := CExternType.func (List.get types ⟨0, by decide⟩)
  let accept := CExternType.func (List.get types ⟨1, by decide⟩)
  ⟨[items, items, accept], [items]⟩

theorem validate_shape (ix : ListImports) (pages : InitialPages) :
    validate? (Growing.mod ix pages) = some validatedType := by
  rw [LoopSound.checkModule_ignore_checked_memories]
  · cbv
  · intro memory member
    change memory ∈ [memoryType pages] at member
    obtain rfl := List.mem_singleton.mp member
    exact decide_eq_true ⟨pages.property, trivial⟩

theorem validates (checker : Checker) (pages : InitialPages) :
    (validate? (Growing.mod checker.imports pages)).isSome = true := by
  rw [validate_shape]
  rfl

private def StoreInv (ix : ListImports) (pages : InitialPages) (store : Store Nat) : Prop :=
  ∃ cfg start, prep (Growing.mod ix pages) = some (cfg, start) ∧
    store.funcs = cfg.store.funcs ∧ Memory32 store

@[expose] def initialMem (pages : InitialPages) : MemInst :=
  ⟨memoryType pages, ⟨Array.replicate (pages.val * 65536) 0⟩⟩

theorem initial_bytes (pages : InitialPages) : (initialMem pages).bytes.size = pages.val * 65536 :=
  Array.size_replicate

theorem initial_pages (pages : InitialPages) : (initialMem pages).pages = pages.val := by
  rw [MemInst.pages, initial_bytes]
  change pages.val * 65536 / 65536 = pages.val
  omega

theorem initial_alloc {ix : ListImports} {pages : InitialPages} {cfg : Config Nat}
    {start : Option FuncIdx} (prepared : prep (Growing.mod ix pages) = some (cfg, start)) :
    cfg.store.mems = [initialMem pages] := by
  have initial : (prep (Growing.mod ix pages)).map (·.1.store.mems) = some [initialMem pages] := by
    unfold prep
    rw [validate_shape]
    rfl
  rw [prepared] at initial
  exact Option.some.inj initial

private theorem initialMemory {ix : ListImports} {pages : InitialPages} {cfg : Config Nat}
    {start : Option FuncIdx} (prepared : prep (Growing.mod ix pages) = some (cfg, start)) :
    Memory32 cfg.store :=
  ⟨initialMem pages, initial_alloc prepared, rfl, (initial_pages pages).trans_le pages.property⟩

theorem prepared_shape (ix : ListImports) (pages : InitialPages) :
    LoopSound.preparedShape (prep (Growing.mod ix pages)) [.i32, .i32]
      [.i32, .i32] (reserve ++ body) = true := by
  unfold prep
  rw [validate_shape]
  rfl

private theorem sat (profile : Profile) (pages : InitialPages) {ix : ListImports}
    (distinct : ix.child ≠ ix.items)
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)} {kind : Set SymStrBytesSExp}
    (childKind : ChildKind ans kind) (env : Env (BitVec 32) SymStrBytesSExp) :
    MemSat profile (Growing.mod ix pages) 0 (listRoles ix ans)
      (readerContract ix.toRead env (boundedListsOf kind) reply) (StoreInv ix pages) := by
  intro mt instance_ config spec
  obtain ⟨cfg, start, prepared, rfl, _, exported⟩ := prep_of_spec spec
  have preparedOK := prepared_shape ix pages
  rw [prepared] at preparedOK
  obtain ⟨rfl, noCode, mems, exports, _, items, child, accept, check, storeFuncs, okItems,
    okChild, okAccept, declared, okCheck⟩ := LoopSound.preparedShape_facts preparedOK
  have memoryAddr : (cfg.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, mems]
  rw [memoryAddr]
  refine ⟨fun _ => Safe.of_exits (o := .normal []) (by simp [Config.withStart, noCode]; rfl)
    (fun _ _ => ⟨cfg, none, prepared, rfl, initialMemory prepared⟩), ?_⟩
  intro addr member
  rw [← exported, exports] at member
  obtain rfl : addr = 3 := by simpa using member
  obtain ⟨code, _, _, hasCode, locals, hasBody, expanded, _, noResults, funcs, memory,
    defaultLocals⟩ := fnOk_spec okCheck
  have stable : ∀ st, StoreInv ix pages st → st.funcs = cfg.store.funcs := by
    rintro st ⟨cfg', start', inst, same, _⟩
    have eqCfg := (Prod.mk.inj (Option.some.inj (inst.symm.trans prepared))).1
    exact same.trans (congrArg (fun cfg : Config Nat => cfg.store.funcs) eqCfg)
  have atCheck : ∀ st, StoreInv ix pages st → st.funcs[3]? = some check := fun st inv => by
    rw [stable st inv, storeFuncs]; rfl
  refine export_valid atCheck hasCode expanded noResults ?_
  intro store args inv typed post exits
  obtain ⟨callee, ps, rs, lookup, type, argTypes⟩ := typed
  have sameCallee : callee = check := Option.some.inj (lookup.symm.trans (atCheck store inv))
  subst callee
  have signature := Expand.iff.1 type
  rw [declared] at signature
  change some (Ty.func (Ty.ofList [.i32, .i32]) .nil) = some (Ty.func ps rs) at signature
  obtain ⟨rfl, rfl⟩ := Ty.func.inj (Option.some.inj signature)
  rcases argTypes with _ | ⟨rootType, rest⟩
  rcases rest with _ | ⟨requestType, rest⟩
  cases rest
  obtain ⟨root, rfl⟩ := ValOk.num_inv rootType
  obtain ⟨requested, rfl⟩ := ValOk.num_inv requestType
  have storeMemory : Memory32 store := by obtain ⟨_, _, _, _, valid⟩ := inv; exact valid
  obtain ⟨mem, memAt, width, pagesBound⟩ := storeMemory
  have storeCount : store.mems.length = 1 := by simp [memAt]
  have frameEq : Frame.forCall check.module [.i32 root, .i32 requested] code.locals =
      ⟨[some (.i32 root), some (.i32 requested), some (.i32 0), some (.i32 0)], check.module⟩ := by
    unfold Frame.forCall
    rw [locals, defaultLocals]
    rfl
  rw [hasBody]
  change HWP profile _ store (Frame.forCall check.module [.i32 root, .i32 requested] code.locals)
    (expression (reserve ++ body)) post
  rw [frameEq]
  refine Reserve.reserve_hwp rfl (by change 1 < 4; decide) (mem?_of memory (by simp [memAt])) width pagesBound ?_
    (exits store inv _).2.2.1
  intro reached grown _ result
  have reachedState : reached.funcs = cfg.store.funcs ∧ reached.mems.length = 1 ∧ Memory32 reached := by
    rcases result with ⟨sameStore, sameMem⟩ | ⟨growth, updated⟩
    · subst reached
      subst grown
      exact ⟨stable store inv, storeCount, mem, memAt, width, pagesBound⟩
    · subst reached
      obtain ⟨_, count, functions⟩ := setMem_mems (mi := grown) storeCount
      refine ⟨functions.trans (stable store inv), count, grown, ?_, Reserve.grow_memory32 width growth⟩
      simp [Store.setMem, memAt]
  refine X.loop (Inv := fun st fr => Memory32 st ∧ LoopSound.Inv kind env root check.module cfg.store.funcs st fr)
    (fun st frame invariant => LoopSound.round rfl (fun _ _ valid => valid) childKind distinct funcs memory
      (by rw [storeFuncs]; rfl) (by rw [storeFuncs]; rfl) (by rw [storeFuncs]; rfl)
      okItems okChild okAccept invariant.2 invariant.1 (fun st same _ valid endFrame => (exits st
        ⟨cfg, none, prepared, same, valid⟩ endFrame).2)) ?_
  exact ⟨reachedState.2.2, reachedState.1, reachedState.2.1, 0, 0, 0, rfl, by decide,
    fun children denotes => ⟨denotes, Nat.zero_le _, fun _ _ before => by simp at before⟩⟩

theorem bounded (profile : Profile) (checker : Checker) (pages : InitialPages)
    {policy : OnInvalid} (noUB : policy ≠ .ub) (envs : Set (Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang profile (ReplyEnvs reply) 0 (Growing.mod checker.imports pages) checker.imports
      checker.decodeChild .trap policy envs ⊆ boundedListsOf checker.kind := by
  cases checker
  · exact ListCheck.listReaderLang_subset (sat profile pages (by decide) symTextAns_kind) (fun _ _ valid => valid)
      noUB envs
  · exact ListCheck.listReaderLang_subset (sat profile pages (by decide) blobAns_kind) (fun _ _ valid => valid)
      noUB envs

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.GrowingModule
