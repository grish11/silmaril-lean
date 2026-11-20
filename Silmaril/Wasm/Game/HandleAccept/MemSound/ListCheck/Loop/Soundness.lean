module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop.Thms
public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopModule

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Items
  Silmaril.Wasm.Game.HandleAccept.MemSound.Readers Silmaril.Accept.Handle Silmaril.Formats

theorem boundedListsOf_subset (kind : Set SymStrBytesSExp) : boundedListsOf kind ⊆ listsOf kind := by
  rintro _ ⟨children, _, member, rfl⟩
  exact ⟨children, member, rfl⟩

/-- The actual symbol checker cannot accept a list longer than the memory32 word range. -/
theorem symbols_bounded (profile : Profile) {policy : OnInvalid} (noUB : policy ≠ .ub)
    (envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang profile (ReplyEnvs itemsReply) 0 (mod {}) {} symTextAns .trap policy envs ⊆
      boundedListsOf symbols :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopSound.symbols_bounded profile noUB envs

/-- The same enforced memory32 length bound applies to the blob checker. -/
theorem blobs_bounded (profile : Profile) {policy : OnInvalid} (noUB : policy ≠ .ub)
    (envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang profile (ReplyEnvs itemsReply) 0 (mod blobImports) blobImports blobAns
      .trap policy envs ⊆ boundedListsOf blobs :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.LoopSound.blobs_bounded profile noUB envs

/-- Every accepted tree is a list of symbols, across all permitted export calls and shaped replies. -/
theorem symbols_sound (profile : Profile) {policy : OnInvalid} (noUB : policy ≠ .ub)
    (envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang profile (ReplyEnvs itemsReply) 0 (mod {}) {} symTextAns .trap policy envs ⊆
      listsOf symbols :=
  (symbols_bounded profile noUB envs).trans (boundedListsOf_subset _)

/-- Every accepted tree is a list of blobs, across all permitted export calls and shaped replies. -/
theorem blobs_sound (profile : Profile) {policy : OnInvalid} (noUB : policy ≠ .ub)
    (envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang profile (ReplyEnvs itemsReply) 0 (mod blobImports) blobImports blobAns
      .trap policy envs ⊆ listsOf blobs :=
  (blobs_bounded profile noUB envs).trans (boundedListsOf_subset _)

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Loop
