module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hi.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Hi

/-!
# `hiMod` writes only the symbol `hi`

`hiMod_sound`: for every profile and every writer policy without undefined behaviour, every tree
`hiMod` accepts through the memory-carrying writer imports, against every environment whose
replies are admitted by `hiReply` (they keep the code, may rewrite memory, return one `i32` from
`symbol` and nothing from `accept`), is the symbol `hi`: the bytes the callout of
`symbol(0, 2)` observes in memory are `68 69`, the UTF-8 text `hi`, on every call.

The proof is a Hoare-logic proof of the module's code under the closed-writes contract
(`Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Hi.hi_sat`) and the bridge
`memWriterLang_subset_of_closed`. The statement is an upper bound: it does not say that `hi` is
accepted by some session (the memory has one page, so the store does not trap, but no
accepting run is exhibited).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

open Silmaril.Wasm Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Accept.Handle Silmaril.Formats

/-- **`hiMod` accepts only the symbol `hi`.** -/
theorem hiMod_sound (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    memWriterLang P (ReplyEnvs hiReply) 0 hiMod {} pol ⊆ {.atom hiAtom} :=
  memWriterLang_subset_of_closed (Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Hi.hi_sat P)
    (fun _ _ h => h) ha hw

end Silmaril.Wasm.Game.HandleAccept.MemSound.Hi
