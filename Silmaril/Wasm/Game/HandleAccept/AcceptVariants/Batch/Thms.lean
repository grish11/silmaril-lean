module

public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch.Defs
public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Thms
import Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch.Link
import Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch.Lang
import Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch.Sound

/-!
# Batches through instance plays: the ghost bridge and the exact batch language

* `strategy_gag`, **the game link for ghost import specifications**: if the instance meets the
  ghost obligation (`GhostGameSat P I Gi Inv`), every play of its strategy from a store `s` with
  `Inv g s` is assume/guarantee correct read from the ghost `g` (`GAG Gi g`). The ghost moves at
  every import question (`Gi.ask`) and answer (`Gi.next`); it lives in the host code of the
  specification world's store, so the module's own steps are unaffected.
* `storeLang_subset_of_gag`, **the batch bridge**: for an instance strategy whose questions decode
  to `accept`, `acceptAll`, `acceptBatch` and whose answers decode to writes and `acceptErr`, if
  in every environment `ρ` leaving the sentinel undefined every play is assume/guarantee correct
  for the batch specification `batchGSpec … ρ L C` from the empty batch, the writer language
  (store semantics, no undefined behaviour) is included in `L`. The ghost is the current batch:
  `accept_batch(keep ≠ 0)` is only asked when the trees built since the previous batch are in
  `L`. The environment used is the final store of each run.
* `consXLang_sound_of_ghostSat`: the same from a module's ghost obligation.

**`batchAccept`** (`run(x)`: `a = word(x)`; `accept_batch(0)`; `cons(a, nil())`;
`accept_batch(1)`), for every profile and every writer policy without undefined behaviour (any
sentinel):

* `batchAccept_lang`: the language is included in `keptL` (`nil` and the one-element lists of
  words), the trees of the **kept** batch. This refines `batchAccept_sound` (the constructed set
  `allL`, `keptL_subset_allL`).
* `batchAccept_drops`: **the dropped batch is never accepted**: no word is in the language (a
  word is built only before `accept_batch(0)`, and no later batch of the same or another export
  call contains it unless it is rebuilt, which `batchAccept` never does after the drop).
* `batchAccept_fixed_lang`: the same bound over every set of fixed environments.

Non-vacuity is `Silmaril.Wasm.Game.HandleAccept.AcceptVariants.batchAccept_accepts` (the run
`run(3)` accepts `nil` and `(3)`), combined in `Batch.Examples`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.AcceptVariants Silmaril.Accept
  Silmaril.Accept.Handle Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Writers

/-- **The game link for ghost import specifications.** -/
theorem strategy_gag {I : ScalarInstance} {P : Profile} {G : Type} {Gi : GISpec I.E G}
    {Inv : G → Store Nat → Prop} (hm : GhostGameSat P I Gi Inv) {g : G} {s : Store Nat}
    (hs : Inv g s) {p : List (Move I.E I.F)} (hp : p ∈ I.strategy P s) : GAG Gi g p :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch.strategy_gag hm hs hp

/-- **The batch bridge.** -/
theorem storeLang_subset_of_gag {E F : Sig.{0}} {X Op : Type} {W : Writer Op X}
    {pol : Policy (BitVec 32)} {L C : Set X} {σ : Strategy E F}
    {dAsk : E.Op → Option (WEv Op (BitVec 32))}
    {dAns : (e : E.Op) → E.Ar e → Option (WEv Op (BitVec 32))}
    (hAG : ∀ ρ : Silmaril.Accept.Handle.Env (BitVec 32) X,
      (∀ r, pol.sentinel = some r → ρ r = none) →
      ∀ p ∈ σ, GAG (batchGSpec W pol.sentinel dAsk dAns ρ L C) ∅ p)
    (hask : ∀ e ev, dAsk e = some ev →
      (∃ h, ev = .accept h) ∨ ev = .acceptAll ∨ ∃ k, ev = .acceptBatch k)
    (hans : ∀ e v ev, dAns e v = some ev →
      (∃ op args r, ev = .write op args r) ∨ ∃ h b, ev = .acceptErr h b)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    writerLang W pol (handleTraces σ (some .enter) dAsk dAns) ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch.storeLang_subset_of_gag hAG hask
    hans hw ha

/-- **Soundness of a module with batches** from its ghost obligation in every environment
leaving the sentinel undefined, from the empty batch. -/
theorem consXLang_sound_of_ghostSat {P : Profile} {m : Module} {ix : ConsXImports}
    {pol : Policy (BitVec 32)} {L C : Set (SExp2 (BitVec 64))}
    {Inv : Set (SExp2 (BitVec 64)) → Store Nat → Prop}
    (hm : ∀ ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)),
      (∀ r, pol.sentinel = some r → ρ r = none) →
      GhostGameSat P (Verify.instOf m)
        (batchGSpec (consW (BitVec 64)) pol.sentinel (consXDecAsk ix) (consXDecAns ix) ρ L C) Inv)
    (hs : Inv ∅ (Verify.instOf m).store) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    moduleConsXLang P m ix pol ⊆ L :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch.consXLang_sound_of_ghostSat hm hs
    hw ha

/-! ## `batchAccept` -/

/-- **`batchAccept` accepts only trees of its kept batch** (`nil` and `(w)`). -/
theorem batchAccept_lang (P : Profile) {pol : Policy (BitVec 32)} (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) : moduleConsXLang P batchAccept variantsIx pol ⊆ keptL :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch.batchAccept_lang P hw ha

/-- **The dropped batch is never accepted**: no word is in the language of `batchAccept`. -/
theorem batchAccept_drops (P : Profile) {pol : Policy (BitVec 32)} (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) (w : BitVec 64) :
    SExp2.atom w ∉ moduleConsXLang P batchAccept variantsIx pol := fun h => by
  rcases batchAccept_lang P hw ha h with h | ⟨_, h⟩ <;> cases h

/-- **Over fixed environments**: the same bound, for every set of environments. -/
theorem batchAccept_fixed_lang (P : Profile) {pol : Policy (BitVec 32)} (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub)
    (Envs : Set (Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))) :
    fixedLang (consW (BitVec 64)) pol Envs
      (moduleTraces P batchAccept (consXDecAsk variantsIx) (consXDecAns variantsIx)) ⊆ keptL :=
  (fixedLang_subset pol Envs _).trans (batchAccept_lang P hw ha)

/-- The kept batch is part of the constructed set. -/
theorem keptL_subset_allL : keptL ⊆ allL := by
  rintro t (rfl | ⟨w, rfl⟩)
  exacts [.inr (.inl rfl), .inr (.inr ⟨w, rfl⟩)]

end Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch
