module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Live.Defs
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hi.Thms
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Pair.Thms
public import Silmaril.Wasm.Game.HandleAccept.MemSound.Items.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveHi
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LivePair
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveItems

/-!
# Non-vacuity of the memory-observing examples

For every profile, concrete traced sessions in admitted environments make the examples accept
their expected trees; with the soundness theorems, the languages are exactly those trees.

* `hi_traces`, `hiMod_live`: against the counting host `countEnv hiOut` (a fresh handle from
  `symbol`, nothing from `accept`, memory untouched), `hiMod`'s writer trace is
  `[enter, write hi [] q, accept q]`; the symbol `hi` is in its writer language for **every**
  policy (the handle starts past the sentinel, `base pol`). `hiMod_lang`: for policies without
  undefined behaviour the language is `{hi}`.
* `pair_traces`, `pairMod_live`, `pairMod_lang`: the same for `pairMod` and `(a b)` (the
  equality under the sentinel-free policies of `pairMod_sound`), with the
  trace `[enter, write a [] q, write b [] (q+1), write list [q, q+1] (q+2), accept (q+2)]`.
* `items_traces`, `itemsMod_live`: against `itemsEnv h₁ h₂` (the host writes the canonical-ABI
  `list<i32>` `[h₁, h₂]` through the return pointer), `itemsMod`'s reader trace on `check(h)` is
  `[enter, read (items h) (items [h₁, h₂]), accept h]`, so every two-element list denoted by `h`
  in a fixed environment of `Rhos` with children denoted by `h₁, h₂` is in the reader language,
  for every accept policy. `itemsMod_lang_univ`: over all fixed environments, the language is
  exactly `twoL` (accept policies without undefined behaviour).

The sessions are Core runs in the every-profile step relation (stores, calls, `local.set/get`,
loads, `i32.ne`, `if`, blocks), built forwards; the instances are the computed spec instances
(`Silmaril.Wasm.Verify.specInstance?`, kernel evaluation), with one memory of one page.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Live

open Silmaril.Wasm Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Accept.Handle Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Pair
  Silmaril.Wasm.Game.HandleAccept.MemSound.Items

/-- **The writer trace of `hiMod`** against a counting host started at `q`. -/
theorem hi_traces (P : Profile) (q : BitVec 32) :
    [.enter, .write (.atom hiAtom) [] q, .accept q] ∈
      memTraces P (ReplyEnvs hiReply) 0 hiMod {} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Hi.hi_traces P q

/-- **`hiMod` accepts the symbol `hi`**, for every profile and policy. -/
theorem hiMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    .atom hiAtom ∈ memWriterLang P (ReplyEnvs hiReply) 0 hiMod {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Hi.hiMod_live P pol

/-- **The writer language of `hiMod` is `{hi}`** (no undefined behaviour). -/
theorem hiMod_lang (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    memWriterLang P (ReplyEnvs hiReply) 0 hiMod {} pol = {.atom hiAtom} :=
  Set.Subset.antisymm (hiMod_sound P ha hw) (Set.singleton_subset_iff.2 (hiMod_live P pol))

/-- **The writer trace of `pairMod`** against a counting host started at `q`. -/
theorem pair_traces (P : Profile) (q : BitVec 32) :
    [.enter, .write (.atom symA) [] q, .write (.atom symB) [] (q + 1),
      .write .list [q, q + 1] (q + 1 + 1), .accept (q + 1 + 1)] ∈
      memTraces P (ReplyEnvs pairReply) 0 pairMod {} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Pair.pair_traces P q

/-- **`pairMod` accepts `(a b)`**, for every profile and policy. -/
theorem pairMod_live (P : Profile) (pol : Policy (BitVec 32)) :
    pairTree ∈ memWriterLang P (ReplyEnvs pairReply) 0 pairMod {} pol :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Pair.pairMod_live P pol

/-- **The writer language of `pairMod` is `{(a b)}`** (no sentinel, no undefined behaviour). -/
theorem pairMod_lang (P : Profile) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    memWriterLang P (ReplyEnvs pairReply) 0 pairMod {} pol = {pairTree} :=
  Set.Subset.antisymm (pairMod_sound P hs hw ha) (Set.singleton_subset_iff.2 (pairMod_live P pol))

/-- **The reader trace of `itemsMod`** on `check(h)` against `itemsEnv h₁ h₂`. -/
theorem items_traces (P : Profile) (h h₁ h₂ : BitVec 32) :
    [.enter, .read (.items h) (.items [h₁, h₂]), .accept h] ∈
      memReadTraces P (ReplyEnvs itemsReply) 0 itemsMod {} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Items.items_traces P h h₁ h₂

/-- **`itemsMod` accepts every two-element list** denoted, with its children, in a fixed
environment of `Rhos`, for every profile and accept policy. -/
theorem itemsMod_live (P : Profile) (oa : OnInvalid)
    {Rhos : Set (Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp)}
    {ρ : Silmaril.Accept.Handle.Env (BitVec 32) SymStrBytesSExp}
    (hρ : ρ ∈ Rhos) {h h₁ h₂ : BitVec 32} {c₁ c₂ : SymStrBytesSExp}
    (e : ρ h = some (SExp.ofList [c₁, c₂])) (e₁ : ρ h₁ = some c₁) (e₂ : ρ h₂ = some c₂) :
    SExp.ofList [c₁, c₂] ∈ memReaderLang P (ReplyEnvs itemsReply) 0 itemsMod {} .trap oa Rhos :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Items.itemsMod_live P oa hρ e e₁ e₂

/-- **Over all fixed environments, `itemsMod` accepts exactly the two-element lists.** -/
theorem itemsMod_lang_univ (P : Profile) {oa : OnInvalid} (hoa : oa ≠ .ub) :
    memReaderLang P (ReplyEnvs itemsReply) 0 itemsMod {} .trap oa Set.univ = twoL :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live.Items.itemsMod_lang_univ P hoa

end Silmaril.Wasm.Game.HandleAccept.MemSound.Live
