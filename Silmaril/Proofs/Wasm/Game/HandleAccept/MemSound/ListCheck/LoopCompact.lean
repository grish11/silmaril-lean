module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Run.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopTrace
import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Replies.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rules
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveRun

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Formats.Api
open Silmaril.Wasm.Game.HandleAccept.MemSound
open Silmaril.Wasm.Game.HandleAccept.MemSound.Items (itemsReply)
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck
open Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
open Silmaril.Wasm.Game.HandleAccept.MemSound.Text (bytesList)
open Silmaril.Wasm.Game.HandleAccept.MemSound.Readers (symTextAns blobAns)
open Silmaril.Wasm.Game.HandleAccept.Memory (MemAtom utf8?)
open Silmaril.Wasm.Numerics Silmaril.Accept.Handle Silmaril.Formats Silmaril.Wasm.Validation
open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound (setMem_mems memOf_setMem)

open Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound (prep)

theorem checker_instance_pages (checker : Checker) (pages : InitialPages) :
    ∃ mt instance_ initial, IsSpecInstance (Loop.mod checker.imports pages) mt instance_ initial ∧
      ReplySpace (pages.val * 65536) initial.store := by
  have valid : (Silmaril.Wasm.Verify.specInstance? (Loop.mod checker.imports pages)).isSome = true := by
    unfold Silmaril.Wasm.Verify.specInstance?
    rw [LoopSound.validate_shape]
    rfl
  have page : Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.memSizes (Loop.mod checker.imports pages) =
      [pages.val * 65536] := by
    simp only [Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.memSizes, prep,
      LoopSound.validate_shape, Option.bind_some]
    change [(Array.replicate (pages.val * 65536) (0 : UInt8)).size] = [pages.val * 65536]
    rw [Array.size_replicate]
  obtain ⟨mt, instance_, initial, spec⟩ := Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.spec_exists valid
  obtain ⟨cfg, start, prepared, rfl, _, _⟩ :=
    Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.prep_of_spec spec
  unfold Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.memSizes at page
  rw [prepared] at page
  have space : ReplySpace (pages.val * 65536) cfg.store := by simpa [ReplySpace] using page
  exact ⟨mt, instance_, cfg.withStart start, spec, by cases start <;> exact space⟩

theorem checker_instance (checker : Checker) :
    ∃ mt instance_ initial, IsSpecInstance (Loop.mod checker.imports) mt instance_ initial ∧
      ReplySpace 65536 initial.store :=
  checker_instance_pages checker InitialPages.one

theorem script_admitted {handles : List (BitVec 32)}
    {encodeChild : ByteArray → BitVec 32 → Except ReplyIssue ByteArray}
    (store : Store Nat) : ReplyEnvs itemsReply store (scriptHost handles encodeChild) := by
  intro state call reply next answer
  change ScriptReply handles encodeChild call reply at answer
  cases answer <;> simp [itemsReply, ShapedReply, KeepsCode, Store.setMem]

theorem compact_admitted {handles : List (BitVec 32)} {childBytes : BitVec 32 → ByteArray}
    (store : Store Nat) : ReplyEnvs itemsReply store (compactHost handles childBytes) :=
  script_admitted store

private theorem script_plan {capacity : Nat} (width : capacity ≤ 2 ^ 32)
    {root : BitVec 32} {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ capacity)
    {encodeChild : ByteArray → BitVec 32 → Except ReplyIssue ByteArray}
    {decode : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)}
    {answerFor : BitVec 32 → SxA MemAtom (BitVec 32)}
    (childFits : ∀ handle ∈ handles, ∀ memory : ByteArray, memory.size = capacity →
      ∃ bytes, encodeChild memory handle = .ok bytes ∧ bytes.size = capacity ∧
        decode ⟨.values [], some bytes⟩ 0 = answerFor handle) :
    ReplyPlan (scriptHost handles encodeChild) (ReplySpace capacity) decode root handles answerFor := by
  constructor
  · intro store state ready
    obtain ⟨mem, atMemory, size⟩ := ready
    obtain ⟨bytes, written, sameSize, decoded, _⟩ :=
      writeItemsReply_roundtrip (memory := mem.bytes) (handles := handles) (size.symm ▸ width) (size.symm ▸ fits)
    let newMem : MemInst := { mem with bytes }
    have memLen : store.mems.length = 1 := by rw [atMemory]; rfl
    have facts := setMem_mems (mi := newMem) memLen
    refine ⟨store.setMem 0 newMem, (), newMem, ScriptReply.items atMemory written,
      ⟨newMem, ?_, sameSize.trans size⟩, facts.2.2, facts.1, decoded, ?_⟩
    · simp [Store.setMem, atMemory, newMem]
    · exact (sameSize.trans size).symm ▸ width
  · intro handle member store state ready
    obtain ⟨mem, atMemory, size⟩ := ready
    obtain ⟨bytes, written, sameSize, decoded⟩ := childFits handle member mem.bytes size
    let newMem : MemInst := { mem with bytes }
    have memLen : store.mems.length = 1 := by rw [atMemory]; rfl
    have facts := setMem_mems (mi := newMem) memLen
    refine ⟨store.setMem 0 newMem, (), ScriptReply.child atMemory member written,
      ⟨newMem, ?_, sameSize⟩, facts.2.2, ?_⟩
    · simp [Store.setMem, atMemory, newMem]
    · rw [memOf_setMem memLen]
      exact decoded

theorem compact_plan {capacity : Nat} (width : capacity ≤ 2 ^ 32)
    {root : BitVec 32} {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ capacity)
    {childBytes : BitVec 32 → ByteArray}
    (childFits : ∀ handle ∈ handles, (childBytes handle).size = capacity)
    (decode : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)) :
    ReplyPlan (compactHost handles childBytes) (ReplySpace capacity) decode root handles
      (fun handle => decode ⟨.values [], some (childBytes handle)⟩ 0) :=
  script_plan width fits (fun handle member _ _ => ⟨_, rfl, childFits handle member, rfl⟩)

private theorem decoded_child (checker : Checker) {image : ByteArray} {bytes : List UInt8}
    (payload : bytesList image 0 = some bytes) :
    checker.decodeChild ⟨.values [], some image⟩ 0 =
      ((checker.decodeBytes bytes).map SxA.atom).getD (.handle 0) := by
  cases checker
  · cases utf : utf8? bytes <;> simp [Checker.decodeBytes, Checker.decodeChild, symTextAns, payload, utf]
  · simp [Checker.decodeBytes, Checker.decodeChild, blobAns, payload]

theorem bytes_plan (checker : Checker) {capacity : Nat} (width : capacity ≤ 2 ^ 32)
    {root : BitVec 32} {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ capacity)
    (raw : BitVec 32 → List UInt8) (space : ∀ handle ∈ handles, 8 + (raw handle).length ≤ capacity) :
    ReplyPlan (byteReplyHost handles raw) (ReplySpace capacity) checker.decodeChild root handles
      (fun handle => ((checker.decodeBytes (raw handle)).map SxA.atom).getD (.handle 0)) := by
  apply script_plan (encodeChild := fun memory handle => writeByteReply memory (raw handle)) width fits
  intro handle member memory size
  obtain ⟨bytes, written, sameSize, decoded⟩ := writeByteReply_roundtrip
    (memory := memory) (payload := raw handle) (size.symm ▸ width) (size.symm ▸ space handle member)
  exact ⟨bytes, written, sameSize.trans size, decoded_child checker decoded⟩

theorem bytes_accepts_pages {profile : Profile} (checker : Checker) {pages : InitialPages}
    (shape : LoopSound.shapeOk checker.imports pages = true)
    {mt : CModuleType} {instance_ : ScalarInstance} {initial : Config Nat}
    (spec : IsSpecInstance (Loop.mod checker.imports pages) mt instance_ initial)
    {capacity : Nat} (width : capacity ≤ 2 ^ 32) (ready : ReplySpace capacity initial.store)
    (policy : OnInvalid) {Rhos : Set (Env (BitVec 32) SymStrBytesSExp)}
    {rho : Env (BitVec 32) SymStrBytesSExp} (allowed : rho ∈ Rhos) {root : BitVec 32}
    {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ capacity)
    (raw : BitVec 32 → List UInt8) (space : ∀ handle ∈ handles, 8 + (raw handle).length ≤ capacity)
    {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom,
      checker.decodeBytes (raw handle) = some atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile (ReplyEnvs itemsReply) 0 (Loop.mod checker.imports pages)
      checker.imports checker.decodeChild .trap policy Rhos := by
  apply checker_accepts_pages checker shape spec (script_admitted instance_.store) () ready
    (bytes_plan checker width fits raw space)
    policy allowed rootDenotes denotes
  intro handle member
  obtain ⟨atom, meaning, named⟩ := atoms handle member
  exact ⟨atom, by simp [meaning], named⟩

theorem checker_instance_two (checker : Checker) :
    ∃ mt instance_ initial, IsSpecInstance (Loop.mod checker.imports ⟨2, by decide⟩) mt instance_ initial ∧
      ReplySpace 131072 initial.store := by
  have size : (⟨2, by decide⟩ : InitialPages).val * 65536 = 131072 := rfl
  simpa only [size] using checker_instance_pages checker ⟨2, by decide⟩

theorem bytes_accepts_initial {profile : Profile} (checker : Checker) (pages : InitialPages)
    (policy : OnInvalid) {Rhos : Set (Env (BitVec 32) SymStrBytesSExp)}
    {rho : Env (BitVec 32) SymStrBytesSExp} (allowed : rho ∈ Rhos) {root : BitVec 32}
    {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ pages.val * 65536)
    (raw : BitVec 32 → List UInt8) (space : ∀ handle ∈ handles, 8 + (raw handle).length ≤ pages.val * 65536)
    {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom,
      checker.decodeBytes (raw handle) = some atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile (ReplyEnvs itemsReply) 0 (Loop.mod checker.imports pages)
      checker.imports checker.decodeChild .trap policy Rhos := by
  obtain ⟨_, _, _, spec, ready⟩ := checker_instance_pages checker pages
  have shape := (LoopSound.shape_pages checker.imports pages InitialPages.one).trans (checker_shape checker)
  have width : pages.val * 65536 ≤ 2 ^ 32 := Nat.mul_le_mul_right 65536 pages.property
  exact bytes_accepts_pages checker shape spec width ready policy allowed fits raw space rootDenotes denotes atoms

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun
