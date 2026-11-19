module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Pair.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pair

/-!
# `pairMod` accepts only the list `(a b)`

For every profile, against every environment whose replies are admitted by `pairReply` (they
keep the code, may rewrite memory, return one `i32` from `symbol` and `sexp` and nothing from
`accept`):

* `pairMod_fixed_sound`: in every fixed environment `ρ` and for every policy without a failure
  sentinel, the trees `pairMod` accepts are the list `(a b)` of the symbols `a` and `b`;
* `pairMod_sound`: the same for the writer language (store semantics), for every policy without
  a sentinel and without undefined behaviour.

What is used about memory: the callout of each `symbol(16, 1)` reads the byte the module stored
right before (`a`, then `b`), and the callout of `sexp(0, 2)` reads the two handles the module
stored at `0` and `4` after both `symbol` calls returned; the handle `sexp` returns therefore
denotes `(a b)` in `ρ`. The proof is a Hoare-logic proof of the code
(`Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pair.pair_sat`) and the bridge
`memFixedLang_subset`/`memWriterLang_subset`. The statements are upper bounds (no accepting
session is exhibited).
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Pair

open Silmaril.Wasm Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Accept.Handle Silmaril.Formats
  Silmaril.Formats.Api

/-- **In a fixed environment, `pairMod` accepts only `(a b)`.** -/
theorem pairMod_fixed_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp) :
    fixedLang (sexpW MemAtom) pol {ρ} (memTraces P (ReplyEnvs pairReply) 0 pairMod {}) ⊆
      {pairTree} :=
  memFixedLang_subset
    (by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pair.pair_sat P ρ)
    (fun _ _ h => h)

/-- **`pairMod` accepts only `(a b)`.** -/
theorem pairMod_sound (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    memWriterLang P (ReplyEnvs pairReply) 0 pairMod {} pol ⊆ {pairTree} :=
  memWriterLang_subset
    (fun ρ => by rw [hs]; exact Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Pair.pair_sat P ρ)
    (fun _ _ h => h) hw ha

end Silmaril.Wasm.Game.HandleAccept.MemSound.Pair
