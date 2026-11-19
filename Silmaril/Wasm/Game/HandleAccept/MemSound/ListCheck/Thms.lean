module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.Live

/-!
# The list checkers accept only lists of two symbols (or two blobs)

* `listReaderLang_subset` (**the list reader bridge**): with the reader contract
  (`readerContract`: accepts name members of `L`, every decoded read is correct in `ρ`) proved
  in every fixed environment for the roles `listRoles ix ans`, the reader language under the
  trapping read policy is included in `L`, for every accept policy without undefined behaviour
  and every set of fixed environments.
* `symListMod_sound`: for every profile, against every host admitted by `itemsReply` (keeps the
  code, may rewrite any memory contents at every answer, returns no values), `symListMod`
  accepts only lists of two symbols (`symPairs`).
* `blobListMod_sound`: the same for `blobListMod` and lists of two blobs (`blobPairs`).
* `symListMod_live_of`, `blobListMod_live_of` (**non-vacuity**): against the host
  `listEnv w w` (every `items` and child call writes the words `8, 2, w, w` at `[0, 16)`), with
  `w` the word whose two low little-endian bytes are `b₀ b₁`, the session reads the children
  `[w, w]` and then the symbol of the UTF-8 text of `b₀ b₁` (the blob `b₀ b₁`) twice, and accepts
  `h`: the list of two copies of that symbol (blob) is in the language whenever a fixed
  environment of `Rhos` names it by `h` and the child by `w`.

What is observed: `items(h, 0)` is decoded as `read (items h) (items hs)` from the memory after
its answer; the module loads `len` and the two handles `c₁ c₂` from that same memory, before any
other call, so `[c₁, c₂] = hs`; `symbol_text(cᵢ, 0)` (or `blob_bytes`) is decoded as
`read (atom cᵢ) a` from the memory after its own answer. Under the trapping read policy a
session continues only through correct reads in a fixed environment `ρ`: `h` denotes a list
whose children `hs` denote, and each `cᵢ` denotes a symbol (a blob). The proof is a Hoare-logic
proof of the code (`Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.list_sat`), generic
in the child reader, and the bridge.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Items Silmaril.Wasm.Game.HandleAccept.MemSound.Readers

/-- **The list reader bridge.** -/
theorem listReaderLang_subset {P : Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {ix : ListImports}
    {ans : HostReply → BitVec 32 → SxA MemAtom (BitVec 32)} {L : Set SymStrBytesSExp}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (listRoles ix ans) (readerContract ix.toRead ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang P Envs memIdx m ix ans .trap oa Rhos ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.listReaderLang_subset hsat hE hoa
    Rhos

/-- **`symListMod` accepts only lists of two symbols.** -/
theorem symListMod_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang P (ReplyEnvs itemsReply) 0 symListMod {} symTextAns .trap oa Rhos ⊆
      symPairs :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.symListMod_sound P hoa Rhos

/-- **`blobListMod` accepts only lists of two blobs.** -/
theorem blobListMod_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang P (ReplyEnvs itemsReply) 0 blobListMod blobImports blobAns .trap oa Rhos ⊆
      blobPairs :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.blobListMod_sound P hoa Rhos

/-- **`symListMod` accepts the list of two copies of the symbol of every two-byte UTF-8
text** `b₀ b₁` named in `Rhos` (a live session). -/
theorem symListMod_live_of (P : Profile) (oa : OnInvalid)
    {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp} (hρ : ρ ∈ Rhos)
    {h : BitVec 32} {b₀ b₁ : UInt8} {str : String} (hu : utf8? [b₀, b₁] = some str)
    (e : ρ h = some (SExp.ofList [.atom ⟨.symbol, by decide, str⟩,
      .atom ⟨.symbol, by decide, str⟩]))
    (ew : ρ (BitVec.ofNat 32 (b₀.toNat + 256 * b₁.toNat)) =
      some (.atom ⟨.symbol, by decide, str⟩)) :
    SExp.ofList [.atom ⟨.symbol, by decide, str⟩, .atom ⟨.symbol, by decide, str⟩] ∈
      listReaderLang P (ReplyEnvs itemsReply) 0 symListMod {} symTextAns .trap oa Rhos :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.symListMod_live_of P oa hρ hu e ew

/-- **`blobListMod` accepts the list of two copies of every two-byte blob** `b₀ b₁` named in
`Rhos` (a live session). -/
theorem blobListMod_live_of (P : Profile) (oa : OnInvalid)
    {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp} (hρ : ρ ∈ Rhos)
    {h : BitVec 32} {b₀ b₁ : UInt8}
    (e : ρ h = some (SExp.ofList [.atom ⟨.bytes, by decide, [b₀, b₁]⟩,
      .atom ⟨.bytes, by decide, [b₀, b₁]⟩]))
    (ew : ρ (BitVec.ofNat 32 (b₀.toNat + 256 * b₁.toNat)) =
      some (.atom ⟨.bytes, by decide, [b₀, b₁]⟩)) :
    SExp.ofList [.atom ⟨.bytes, by decide, [b₀, b₁]⟩, .atom ⟨.bytes, by decide, [b₀, b₁]⟩] ∈
      listReaderLang P (ReplyEnvs itemsReply) 0 blobListMod blobImports blobAns .trap oa Rhos :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ListCheck.blobListMod_live_of P oa hρ e ew

/-- For the Wasm-facing call-local trap. -/
theorem symListMod_sound_callTrap (P : Profile)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    listReaderLang P (ReplyEnvs itemsReply) 0 symListMod {} symTextAns .trap .callTrap Rhos ⊆
      symPairs :=
  symListMod_sound P (by decide) Rhos

end Silmaril.Wasm.Game.HandleAccept.MemSound.ListCheck
