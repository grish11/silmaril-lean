module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Items.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items

/-!
# `itemsMod` accepts only lists of two children

`itemsMod_sound`: for every profile, every accept policy without undefined behaviour (the
Wasm-facing call-local trap included) and every set of fixed environments, the reader language
of `itemsMod` through the memory-returning reader, under the trapping read policy and against
every environment whose replies are admitted by `itemsReply` (they keep the code, may write any
memory contents, return no values), is included in `twoL`.

What is observed: the read `read (items h) (items hs)` is decoded from the memory **after** the
host's answer to `items(h, 0)`: `(ptr, len)` at `[0, 8)`, then `len` little-endian handles at
`ptr`; the module loads `len` from the same bytes (`i32.load offset=4`) and calls `accept(h)`
only when it is `2`. A correct read in `ρ` says that `h` denotes a list of `hs.length` children.
The proof is a Hoare-logic proof of the code
(`Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items.items_sat`) and the bridge
`memReaderLang_subset`. The statement is an upper bound (no accepting session is exhibited).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Items

open Silmaril.Wasm Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Accept.Handle Silmaril.Formats

/-- **`itemsMod` accepts only lists of two children.** -/
theorem itemsMod_sound (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    memReaderLang P (ReplyEnvs itemsReply) 0 itemsMod {} .trap oa Rhos ⊆ twoL :=
  memReaderLang_subset
    (fun ρ => Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Items.items_sat P ρ)
    (fun _ _ h => h) hoa Rhos

/-- For the Wasm-facing call-local trap. -/
theorem itemsMod_sound_callTrap (P : Profile)
    (Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)) :
    memReaderLang P (ReplyEnvs itemsReply) 0 itemsMod {} .trap .callTrap Rhos ⊆ twoL :=
  itemsMod_sound P (by decide) Rhos

end Silmaril.Wasm.Game.HandleAccept.MemSound.Items
