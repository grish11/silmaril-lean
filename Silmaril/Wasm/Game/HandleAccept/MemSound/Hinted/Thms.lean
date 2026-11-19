module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.HintedSep

/-!
# Hinted Rivest atoms through linear memory: soundness and non-vacuity

For every profile, `hintedMod` (store `68 69` at `[0, 2)`, accept the handle of
`hinted(0, 2, 0, 2)`), against the hosts `ReplyEnvs hiReply`:

* `hinted_sound`: its hinted writer language (`hintedWriterLang`, decoder `hintedWrite`: the hint
  at `[hptr, hptr + hlen)` and the octets at `[ptr, ptr + len)` of the memory at the call) is
  included in `{[hi]hi}` for every policy without undefined behaviour;
* `hinted_live`: it contains `[hi]hi` for every policy;
* `hinted_lang`: **the language is exactly `{[hi]hi}`** (`hiHinted`: hint `hi`, octets `hi`).

Hint and octets from **separate segments**: `hintedSepMod` stores `68 69 61 62` at `[0, 4)` and
accepts `hinted(0, 2, 2, 2)` (hint at `[0, 2)`, octets at `[2, 4)`): `hintedSep_sound`,
`hintedSep_live`, `hintedSep_lang` (**exactly `{[hi]ab}`**, `hiabHinted`).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted

open Silmaril.Wasm Silmaril.Accept.Handle Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

/-- `hintedMod` accepts only `[hi]hi`. -/
theorem hinted_sound (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    hintedWriterLang P (ReplyEnvs hiReply) 0 hintedMod {} pol ⊆ {.atom hiHinted} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Hinted.hinted_sound P ha hw

/-- `hintedMod` accepts `[hi]hi`. -/
theorem hinted_live (P : Profile) (pol : Policy (BitVec 32)) :
    .atom hiHinted ∈ hintedWriterLang P (ReplyEnvs hiReply) 0 hintedMod {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Hinted.hinted_live P pol

/-- **The hinted writer language of `hintedMod` is `{[hi]hi}`.** -/
theorem hinted_lang (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    hintedWriterLang P (ReplyEnvs hiReply) 0 hintedMod {} pol = {.atom hiHinted} :=
  Set.Subset.antisymm (hinted_sound P ha hw) (Set.singleton_subset_iff.2 (hinted_live P pol))

/-- `hintedSepMod` accepts only `[hi]ab`. -/
theorem hintedSep_sound (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    hintedWriterLang P (ReplyEnvs hiReply) 0 hintedSepMod {} pol ⊆ {.atom hiabHinted} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.HintedSep.hintedSep_sound P ha hw

/-- `hintedSepMod` accepts `[hi]ab`. -/
theorem hintedSep_live (P : Profile) (pol : Policy (BitVec 32)) :
    .atom hiabHinted ∈ hintedWriterLang P (ReplyEnvs hiReply) 0 hintedSepMod {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.HintedSep.hintedSep_live P pol

/-- **The hinted writer language of `hintedSepMod` is `{[hi]ab}`**: the hint and the octets come
from the disjoint segments `[0, 2)` and `[2, 4)`. -/
theorem hintedSep_lang (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    hintedWriterLang P (ReplyEnvs hiReply) 0 hintedSepMod {} pol = {.atom hiabHinted} :=
  Set.Subset.antisymm (hintedSep_sound P ha hw)
    (Set.singleton_subset_iff.2 (hintedSep_live P pol))

end Silmaril.Wasm.Game.HandleAccept.MemSound.Hinted
