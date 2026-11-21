module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Run.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Soundness
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopTrace
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopCompact
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopModule

public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Numerics Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Validation
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
open Silmaril.Wasm.Game.HandleAccept.MemSound (ReplyEnvs)
open Silmaril.Wasm.Game.HandleAccept.MemSound.Items (itemsReply)
open Silmaril.Wasm.Game.HandleAccept.Memory (MemAtom)

/-- Every finite correctly denoting reply plan produces an actual accepting export prefix,
including an empty vector or multiple occurrences of a child handle. This is a lower bound,
not termination under arbitrary hosts or equality with the memory32 length upper bound. -/
theorem accepts_of_plan {profile : Profile} (checker : Checker)
    {mt : CModuleType} {instance_ : ScalarInstance} {initial : Config Nat}
    (spec : IsSpecInstance (Loop.mod checker.imports) mt instance_ initial)
    {Envs : Store Nat → SEnv UImp → Prop} {L : SEnv UImp} (env : Envs instance_.store L)
    (initState : L.S) {ready : Store Nat → Prop} (good : ready initial.store)
    {root : BitVec 32} {handles : List (BitVec 32)} {answerFor : BitVec 32 → SxA MemAtom (BitVec 32)}
    (plan : ReplyPlan L ready checker.decodeChild root handles answerFor)
    (policy : OnInvalid) {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {rho : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp}
    (allowed : rho ∈ Rhos) {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom, answerFor handle = .atom atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile Envs 0 (Loop.mod checker.imports) checker.imports
      checker.decodeChild .trap policy Rhos :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.checker_accepts_pages
    checker (Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.checker_shape checker)
    spec env initState good plan policy allowed rootDenotes denotes atoms

theorem script_host_admitted {handles : List (BitVec 32)}
    {encodeChild : ByteArray → BitVec 32 → Except ReplyIssue ByteArray}
    (store : Store Nat) : ReplyEnvs itemsReply store (scriptHost handles encodeChild) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.script_admitted store

theorem compact_host_admitted {handles : List (BitVec 32)} {childBytes : BitVec 32 → ByteArray}
    (store : Store Nat) : ReplyEnvs itemsReply store (compactHost handles childBytes) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.compact_admitted store

/-- The checked encoder supplies the whole reply plan whenever the vector and child
payloads fit. The child decoder observes the bytes supplied for that exact handle. -/
theorem compact_reply_plan {capacity : Nat} (width : capacity ≤ 2 ^ 32)
    {root : BitVec 32} {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ capacity)
    {childBytes : BitVec 32 → ByteArray}
    (childFits : ∀ handle ∈ handles, (childBytes handle).size = capacity)
    (decode : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)) :
    ReplyPlan (compactHost handles childBytes) (ReplySpace capacity) decode root handles
      (fun handle => decode ⟨.values [], some (childBytes handle)⟩ 0) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.compact_plan width fits childFits decode

/-- In-place replies preserve the capacity, regardless of the bytes left by the previous
call. The child observation depends on the current payload, not on trailing memory. -/
theorem byte_reply_plan (checker : Checker) {capacity : Nat} (width : capacity ≤ 2 ^ 32)
    {root : BitVec 32} {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ capacity)
    (raw : BitVec 32 → List UInt8) (space : ∀ handle ∈ handles, 8 + (raw handle).length ≤ capacity) :
    ReplyPlan (byteReplyHost handles raw) (ReplySpace capacity) checker.decodeChild root handles
      (fun handle => ((checker.decodeBytes (raw handle)).map SxA.atom).getD (.handle 0)) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.bytes_plan checker width fits raw space

/-- Both checkers have a validated instance with one initial memory page. -/
theorem checker_instance (checker : Checker) :
    ∃ mt instance_ initial, IsSpecInstance (Loop.mod checker.imports) mt instance_ initial ∧
      ReplySpace 65536 initial.store :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.checker_instance checker

/-- Check the actual prepared checker shape, rather than assuming an arbitrary instance
uses the same function and memory indices as the one-page example. -/
def checkedPageShape (checker : Checker) (pages : InitialPages) : Bool :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopSound.shapeOk checker.imports pages

/-- All permitted initial page counts have the same checked code, imports and memory
address. Validation and shape checks do not depend on evaluating the allocated bytes. -/
theorem checkedPageShape_all (checker : Checker) (pages : InitialPages) : checkedPageShape checker pages = true :=
  (Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopSound.shape_pages
    checker.imports pages InitialPages.one).trans
    (Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.checker_shape checker)

theorem checkedPageShape_two (checker : Checker) : checkedPageShape checker ⟨2, by decide⟩ = true :=
  checkedPageShape_all checker ⟨2, by decide⟩

/-- A validated instance at any allowed memory32 minimum comes with exactly that
initial capacity. This is a specification instance, not a claim about physical memory. -/
theorem checker_instance_pages (checker : Checker) (pages : InitialPages) :
    ∃ mt instance_ initial, IsSpecInstance (Loop.mod checker.imports pages) mt instance_ initial ∧
      ReplySpace (pages.val * 65536) initial.store :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.checker_instance_pages checker pages

/-- The same child-kind and addressability bound holds for arbitrary export prefixes
from any checked page configuration. -/
theorem checker_bounded_in (profile : Profile) (checker : Checker) {pages : InitialPages}
    (shape : checkedPageShape checker pages = true) {policy : OnInvalid} (noUB : policy ≠ .ub)
    (envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang profile (ReplyEnvs itemsReply) 0 (Loop.mod checker.imports pages)
      checker.imports checker.decodeChild .trap policy envs ⊆ boundedListsOf checker.kind :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.checker_bounded_pages
    profile checker shape noUB envs

theorem checker_bounded_pages (profile : Profile) (checker : Checker) (pages : InitialPages)
    {policy : OnInvalid} (noUB : policy ≠ .ub)
    (envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang profile (ReplyEnvs itemsReply) 0 (Loop.mod checker.imports pages)
      checker.imports checker.decodeChild .trap policy envs ⊆ boundedListsOf checker.kind :=
  checker_bounded_in profile checker (checkedPageShape_all checker pages) noUB envs

theorem checker_instance_two (checker : Checker) :
    ∃ mt instance_ initial, IsSpecInstance (Loop.mod checker.imports ⟨2, by decide⟩) mt instance_ initial ∧
      ReplySpace 131072 initial.store :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.checker_instance_two checker

/-- The compact script realizes the accepted tree in an actual module instance, using
only shaped host replies. The required capacity includes the eight-byte list header. -/
theorem compact_accepts {profile : Profile} (checker : Checker)
    {mt : CModuleType} {instance_ : ScalarInstance} {initial : Config Nat}
    (spec : IsSpecInstance (Loop.mod checker.imports) mt instance_ initial)
    {capacity : Nat} (width : capacity ≤ 2 ^ 32) (good : ReplySpace capacity initial.store)
    {root : BitVec 32} {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ capacity)
    {childBytes : BitVec 32 → ByteArray} (childFits : ∀ handle ∈ handles, (childBytes handle).size = capacity)
    (policy : OnInvalid) {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {rho : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp}
    (allowed : rho ∈ Rhos) {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom,
      checker.decodeChild ⟨.values [], some (childBytes handle)⟩ 0 = .atom atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile (ReplyEnvs itemsReply) 0 (Loop.mod checker.imports) checker.imports
      checker.decodeChild .trap policy Rhos :=
  accepts_of_plan checker spec (compact_host_admitted instance_.store) () good
    (compact_reply_plan width fits childFits checker.decodeChild) policy allowed rootDenotes denotes atoms

/-- Use the checked memory capacity of the actual module instance, not an assumed page
count or a scratch-memory override. -/
theorem byte_reply_accepts_in {profile : Profile} (checker : Checker) {pages : InitialPages}
    (shape : checkedPageShape checker pages = true)
    {mt : CModuleType} {instance_ : ScalarInstance} {initial : Config Nat}
    (spec : IsSpecInstance (Loop.mod checker.imports pages) mt instance_ initial)
    {capacity : Nat} (width : capacity ≤ 2 ^ 32) (ready : ReplySpace capacity initial.store)
    (policy : OnInvalid) {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {rho : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp} (allowed : rho ∈ Rhos) {root : BitVec 32}
    {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ capacity)
    (raw : BitVec 32 → List UInt8) (space : ∀ handle ∈ handles, 8 + (raw handle).length ≤ capacity)
    {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom,
      checker.decodeBytes (raw handle) = some atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile (ReplyEnvs itemsReply) 0 (Loop.mod checker.imports pages)
      checker.imports checker.decodeChild .trap policy Rhos :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.bytes_accepts_pages
    checker shape spec width ready policy allowed fits raw space rootDenotes denotes atoms

/-- Any correctly denoting byte script that fits the configured initial memory produces
an actual accepting export prefix. Instance validation and shape follow from `pages`. -/
theorem byte_reply_accepts_pages {profile : Profile} (checker : Checker) (pages : InitialPages)
    (policy : OnInvalid) {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {rho : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp} (allowed : rho ∈ Rhos) {root : BitVec 32}
    {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ pages.val * 65536)
    (raw : BitVec 32 → List UInt8) (space : ∀ handle ∈ handles, 8 + (raw handle).length ≤ pages.val * 65536)
    {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom,
      checker.decodeBytes (raw handle) = some atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile (ReplyEnvs itemsReply) 0 (Loop.mod checker.imports pages)
      checker.imports checker.decodeChild .trap policy Rhos :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopRun.bytes_accepts_initial
    checker pages policy allowed fits raw space rootDenotes denotes atoms

/-- The validated one-page checker accepts any correctly denoting byte script fitting the
page. The checked encoders construct both kinds of reply in place. -/
theorem byte_reply_accepts {profile : Profile} (checker : Checker)
    (policy : OnInvalid) {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {rho : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp} (allowed : rho ∈ Rhos) {root : BitVec 32}
    {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ 65536)
    (raw : BitVec 32 → List UInt8) (space : ∀ handle ∈ handles, 8 + (raw handle).length ≤ 65536)
    {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom,
      checker.decodeBytes (raw handle) = some atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile (ReplyEnvs itemsReply) 0 (Loop.mod checker.imports)
      checker.imports checker.decodeChild .trap policy Rhos :=
  byte_reply_accepts_pages checker InitialPages.one policy allowed fits raw space rootDenotes denotes atoms

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
