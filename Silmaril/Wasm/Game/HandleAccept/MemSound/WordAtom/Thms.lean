module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WordAtom

/-!
# Word-tree atoms through linear memory: soundness and non-vacuity

For every profile, `wordMod` (store the `i64` `42` at `[0, 8)`, accept the handle of `word(0)`),
against the hosts `ReplyEnvs hiReply`:

* `word_sound`: its word-tree writer language (`wordWriterLang`, decoder `wordWrite`: `word(ptr)`
  reads eight little-endian bytes at `ptr` of the memory at the call) is included in `{42}` for
  every policy without undefined behaviour (Hoare-logic proof under the closed-writes contract);
* `word_live`: it contains `42` for every policy (traced session against the counting host);
* `word_lang`: **the language is exactly `{42}`**.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom

open Silmaril.Wasm Silmaril.Accept.Handle Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

/-- `wordMod` accepts only the word `42`. -/
theorem word_sound (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    wordWriterLang P (ReplyEnvs hiReply) 0 wordMod {} pol ⊆ {.atom 42} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WordAtom.word_sound P ha hw

/-- `wordMod` accepts the word `42`. -/
theorem word_live (P : Profile) (pol : Policy (BitVec 32)) :
    .atom 42 ∈ wordWriterLang P (ReplyEnvs hiReply) 0 wordMod {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WordAtom.word_live P pol

/-- **The word-tree writer language of `wordMod` is `{42}`.** -/
theorem word_lang (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    wordWriterLang P (ReplyEnvs hiReply) 0 wordMod {} pol = {.atom 42} :=
  Set.Subset.antisymm (word_sound P ha hw) (Set.singleton_subset_iff.2 (word_live P pol))

end Silmaril.Wasm.Game.HandleAccept.MemSound.WordAtom
