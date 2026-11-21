module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Text.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.TextLive

/-!
# The text reader: soundness and non-vacuity

* `textReaderLang_subset` (**the text reader bridge**): with the text reader contract proved in
  every fixed environment, the reader language under the trapping read policy is included in
  `L`, for every accept policy without undefined behaviour and every set of fixed environments.
* `textMod_sound`: for every profile, against every host admitted by `itemsReply`, `textMod`
  accepts only string atoms whose UTF-8 text has two bytes (`twoByteStrs`). Proof: a Hoare-logic
  proof (`Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Text.text_sat`) that `accept(h)` is
  called only after the length word the host wrote at `[4, 8)` is `2`, which is the length of
  the bytes the decoder reads, whose UTF-8 text is the string `h` denotes by the reader
  contract.
* `textMod_live`: `textMod` accepts the string `"hi"` in every set of fixed environments one of
  which names it (the session against `itemsEnv 0x6968 0`).

Only strings are covered: the decoded atom's kind is fixed by the import (`string_text`), and
the memory-carrying reader has `MemAtom` atoms (no keywords; a keyword reader would need a
reader over `KwAtom`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Text

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound.Items

/-- **The text reader bridge.** -/
theorem textReaderLang_subset {P : Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {ix : TextImports} {L : Set SymStrBytesSExp}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx (textRoles ix) (textContract ix ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    textReaderLang P Envs memIdx m ix .trap oa Rhos ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Text.textReaderLang_subset hsat hE hoa Rhos

/-- **`textMod` accepts only strings of two UTF-8 bytes.** -/
theorem textMod_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    textReaderLang P (ReplyEnvs itemsReply) 0 textMod {} .trap oa Rhos ⊆ twoByteStrs :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Text.textMod_sound P hoa Rhos

/-- **`textMod` accepts the string `"hi"`.** -/
theorem textMod_live (P : Profile) (oa : OnInvalid)
    {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp} (hρ : ρ ∈ Rhos) {h : BitVec 32}
    (e : ρ h = some (.atom ⟨.string, by decide, "hi"⟩)) :
    .atom ⟨.string, by decide, "hi"⟩ ∈
      textReaderLang P (ReplyEnvs itemsReply) 0 textMod {} .trap oa Rhos :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Text.textMod_live P oa hρ e

end Silmaril.Wasm.Game.HandleAccept.MemSound.Text
