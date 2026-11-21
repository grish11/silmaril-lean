module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Run.Defs
public import Silmaril.Wasm.Logic.Hoare.Defs
public import Silmaril.Wasm.Validation.Check.Validate
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Reserve
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.GrowingModule
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.GrowingTrace

public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Accept.Handle Silmaril.Formats
open Silmaril.Wasm.Logic.Core (Post)

/-- Refusal traps in the original store before reaching the checker or calling any host.
Otherwise local 1 is reset and the requested number of pages is available to the continuation. -/
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
    HWP profile host store frame (expression (reserve ++ tail)) post :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Reserve.reserve_hwp
    requestLocal localBound lookup width pageBound resume traps

/-- Both module variants validate at every legal initial memory32 page count. -/
theorem validates (checker : Checker) (pages : InitialPages) :
    (Validation.validate? (mod checker.imports pages)).isSome = true :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.GrowingModule.validates checker pages

/-- The checked in-place byte encoders meet the growing checker's host contract, including
their effect-free error paths. -/
theorem byte_reply_admitted (store : Store Nat) (handles : List (BitVec 32)) (raw : BitVec 32 → List UInt8) :
    ReplyEnvs reply store (byteReplyHost handles raw) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.GrowingModule.byte_reply_admitted store handles raw

/-- The actual growing checker accepts only lists of the selected kind within the memory32
word bound, over arbitrary export prefixes and all profiles. Hosts must preserve memory32. -/
theorem bounded (profile : Profile) (checker : Checker) (pages : InitialPages)
    {policy : OnInvalid} (noUB : policy ≠ .ub)
    (envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang profile (ReplyEnvs reply) 0 (mod checker.imports pages) checker.imports
      checker.decodeChild .trap policy envs ⊆ boundedListsOf checker.kind :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.GrowingModule.bounded profile checker pages noUB envs

/-- Every correctly denoting compact byte script fitting the initial or requested capacity
has an accepting export prefix, provided a necessary growth may succeed in the profile. -/
theorem byte_reply_accepts {profile : Profile} (checker : Checker) (pages requested : InitialPages)
    (allows : pages.val < requested.val →
      profile.growMaySucceed .memory 0 pages.val (requested.val - pages.val))
    (policy : OnInvalid) {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {rho : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp} (allowed : rho ∈ Rhos) {root : BitVec 32}
    {handles : List (BitVec 32)} (fits : 8 + 4 * handles.length ≤ max pages.val requested.val * 65536)
    (raw : BitVec 32 → List UInt8)
    (space : ∀ handle ∈ handles, 8 + (raw handle).length ≤ max pages.val requested.val * 65536)
    {children : List SymStrBytesSExp} (rootDenotes : rho root = some (SExp.ofList children))
    (denotes : List.Forall₂ (fun handle child => rho handle = some child) handles children)
    (atoms : ∀ handle ∈ handles, ∃ atom,
      checker.decodeBytes (raw handle) = some atom ∧ rho handle = some (.atom atom)) :
    SExp.ofList children ∈ listReaderLang profile (ReplyEnvs reply) 0 (mod checker.imports pages)
      checker.imports checker.decodeChild .trap policy Rhos :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.GrowingTrace.byte_reply_accepts
    checker pages requested allows policy allowed fits raw space rootDenotes denotes atoms

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Growing
