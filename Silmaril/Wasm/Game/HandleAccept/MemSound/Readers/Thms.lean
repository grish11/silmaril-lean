module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Readers.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers.BlobLive
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers.SymLive

/-!
# The blob and symbol text readers: soundness and non-vacuity

* `blobReaderLang_subset` (**the blob reader bridge**): with the blob reader contract proved in
  every fixed environment, the reader language under the trapping read policy is included in
  `L`, for every accept policy without undefined behaviour and every set of fixed environments.
* `blobMod_sound`: for every profile, against every host admitted by `itemsReply`, `blobMod`
  accepts only blobs of two bytes (`twoByteBlobs`), by the Hoare-logic proof of `textMod` with
  the blob decoder.
* `blobMod_live_of`: `blobMod` accepts the blob `[b₀, b₁]` in every set of fixed environments
  one of which names it (the live session against the host `itemsEnv (blobWord b₀ b₁) 0`, which
  writes `b₀ b₁` as the bytes).
* `blobMod_lang`: **the language is exactly `twoByteBlobs`** over every set of fixed
  environments naming every two-byte blob (`blobMod_lang_univ`: over all fixed environments).
* The same for **symbols** (`symbol_text`): `symTextReaderLang_subset`, `symTextMod_sound`
  (only symbols of two UTF-8 bytes, `twoByteSyms`), `symTextMod_live_of`, `symTextMod_lang`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Readers

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Items

/-- **The blob reader bridge.** -/
theorem blobReaderLang_subset {P : Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {ix : BlobImports} {L : Set SymStrBytesSExp}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (blobRoles ix) (blobContract ix ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    blobReaderLang P Envs memIdx m ix .trap oa Rhos ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers.blobReaderLang_subset hsat hE hoa Rhos

/-- **`blobMod` accepts only blobs of two bytes.** -/
theorem blobMod_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    blobReaderLang P (ReplyEnvs itemsReply) 0 blobMod {} .trap oa Rhos ⊆ twoByteBlobs :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers.blobMod_sound P hoa Rhos

/-- **`blobMod` accepts every blob of two bytes** named in `Rhos` (a live session). -/
theorem blobMod_live_of (P : Profile) (oa : OnInvalid)
    {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp} (hρ : ρ ∈ Rhos)
    {h : BitVec 32} {b₀ b₁ : UInt8} (e : ρ h = some (.atom ⟨.bytes, by decide, [b₀, b₁]⟩)) :
    .atom ⟨.bytes, by decide, [b₀, b₁]⟩ ∈
      blobReaderLang P (ReplyEnvs itemsReply) 0 blobMod {} .trap oa Rhos :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers.blobMod_live_of P oa hρ e

/-- **The language of `blobMod` is exactly the blobs of two bytes**, over every set of fixed
environments naming each of them. -/
theorem blobMod_lang (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    (hR : ∀ x ∈ twoByteBlobs, ∃ ρ ∈ Rhos, ∃ h, ρ h = some x) :
    blobReaderLang P (ReplyEnvs itemsReply) 0 blobMod {} .trap oa Rhos = twoByteBlobs :=
  Set.Subset.antisymm (blobMod_sound P hoa Rhos)
    (Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers.twoByteBlobs_subset P oa hR)

/-- **Over all fixed environments, the language of `blobMod` is `twoByteBlobs`.** -/
theorem blobMod_lang_univ (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub) :
    blobReaderLang P (ReplyEnvs itemsReply) 0 blobMod {} .trap oa Set.univ = twoByteBlobs :=
  blobMod_lang P hoa fun x _ => ⟨fun _ => some x, Set.mem_univ _, 0, rfl⟩

/-! ## Symbols -/

/-- **The symbol text reader bridge.** -/
theorem symTextReaderLang_subset {P : Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {ix : SymTextImports} {L : Set SymStrBytesSExp}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (symTextRoles ix) (symTextContract ix ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    symTextReaderLang P Envs memIdx m ix .trap oa Rhos ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers.symTextReaderLang_subset hsat hE hoa
    Rhos

/-- **`symTextMod` accepts only symbols of two UTF-8 bytes.** -/
theorem symTextMod_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    symTextReaderLang P (ReplyEnvs itemsReply) 0 symTextMod {} .trap oa Rhos ⊆ twoByteSyms :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers.symTextMod_sound P hoa Rhos

/-- **`symTextMod` accepts the symbol of every two-byte UTF-8 text** named in `Rhos`. -/
theorem symTextMod_live_of (P : Profile) (oa : OnInvalid)
    {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp} (hρ : ρ ∈ Rhos)
    {h : BitVec 32} {b₀ b₁ : UInt8} {str : String} (hu : utf8? [b₀, b₁] = some str)
    (e : ρ h = some (.atom ⟨.symbol, by decide, str⟩)) :
    .atom ⟨.symbol, by decide, str⟩ ∈
      symTextReaderLang P (ReplyEnvs itemsReply) 0 symTextMod {} .trap oa Rhos :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers.symTextMod_live_of P oa hρ hu e

/-- **The language of `symTextMod` is exactly the symbols of two UTF-8 bytes**, over every set
of fixed environments naming each of them. -/
theorem symTextMod_lang (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    (hR : ∀ x ∈ twoByteSyms, ∃ ρ ∈ Rhos, ∃ h, ρ h = some x) :
    symTextReaderLang P (ReplyEnvs itemsReply) 0 symTextMod {} .trap oa Rhos = twoByteSyms :=
  Set.Subset.antisymm (symTextMod_sound P hoa Rhos)
    (Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Readers.twoByteSyms_subset P oa hR)

end Silmaril.Wasm.Game.HandleAccept.MemSound.Readers
