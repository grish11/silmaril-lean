module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch.Lang
public import Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch.Module

/-!
# Proofs: soundness of writers with batches from the ghost obligation

* `consXLang_sound_of_ghostSat`: the game link `strategy_gag` and the batch bridge
  `storeLang_subset_of_gag`, for the decoders of the cons writer API with accept variants.
* `batchAccept_lang`: `batchAccept_gsat` in every environment leaving the sentinel undefined.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.AcceptVariants Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch

/-- **Soundness of a module with batches** from its ghost obligation. -/
theorem consXLang_sound_of_ghostSat {P : Profile} {m : Module} {ix : ConsXImports}
    {pol : Policy (BitVec 32)} {L C : Set (SExp2 (BitVec 64))}
    {Inv : Set (SExp2 (BitVec 64)) → Store Nat → Prop}
    (hm : ∀ ρ : Env (BitVec 32) (SExp2 (BitVec 64)),
      (∀ r, pol.sentinel = some r → ρ r = none) →
      GhostGameSat P (Verify.instOf m)
        (batchGSpec (consW (BitVec 64)) pol.sentinel (consXDecAsk ix) (consXDecAns ix) ρ L C) Inv)
    (hs : Inv ∅ (Verify.instOf m).store) (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    moduleConsXLang P m ix pol ⊆ L :=
  storeLang_subset_of_gag (fun ρ hρ _ hp => strategy_gag (hm ρ hρ) hs hp)
    (fun e ev h => by
      rcases Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.consXDecAsk_cases ix e ev h
        with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      exacts [.inl h, .inr (.inl h), .inr (.inr h)])
    (Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.consXDecAns_cases ix) hw ha

/-- **`batchAccept` accepts only its kept batch.** -/
theorem batchAccept_lang (P : Profile) {pol : Policy (BitVec 32)} (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) : moduleConsXLang P batchAccept variantsIx pol ⊆ keptL :=
  consXLang_sound_of_ghostSat (C := allL)
    (fun ρ hρ => batchAccept_gsat P pol.sentinel ρ hρ) rfl hw ha

end Silmaril.Proofs.Wasm.Game.HandleAccept.AcceptVariants.Batch
