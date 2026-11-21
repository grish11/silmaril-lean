module

public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch.Thms
public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Examples

/-!
# Batches: the kept batch is accepted, the dropped one is not

For every profile admitting the interpreter's deterministic steps (`hP`) and a writer policy
with the sentinel `0` and without undefined behaviour, `batchAccept` accepts exactly `nil`
and every singleton word list (`batchAccept_exact`). It never accepts a dropped bare word
(`batchAccept_drops`). `batchAccept_kept` is the concrete instance for input `3`.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Verify
  Silmaril.Wasm.Resource Silmaril.Formats Silmaril.Accept.Handle
  Silmaril.Wasm.Game.HandleAccept.AcceptVariants

/-- **The kept batch is accepted and the dropped one is not.** -/
theorem batchAccept_kept {P : Profile}
    (hP : ∀ c c' : Config Nat, Step (profile refOracle) Det.noHost c c' → Step P Det.noHost c c')
    {pol : Policy (BitVec 32)} (hs : pol.sentinel = some 0) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) :
    SExp2.nil ∈ moduleConsXLang P batchAccept variantsIx pol ∧
      SExp2.cons (.atom 3) .nil ∈ moduleConsXLang P batchAccept variantsIx pol ∧
      SExp2.atom 3 ∉ moduleConsXLang P batchAccept variantsIx pol ∧
      moduleConsXLang P batchAccept variantsIx pol ⊆ keptL :=
  ⟨(batchAccept_accepts hP hs).1, (batchAccept_accepts hP hs).2, batchAccept_drops P hw ha 3,
    batchAccept_lang P hw ha⟩

/-- Every and only kept tree is accepted; dropping the word batch does not affect the
replay of the corresponding one-element list. -/
theorem batchAccept_exact {P : Profile}
    (hP : ∀ before after : Config Nat,
      Step (profile refOracle) Det.noHost before after → Step P Det.noHost before after)
    {pol : Policy (BitVec 32)} (hs : pol.sentinel = some 0) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) :
    moduleConsXLang P batchAccept variantsIx pol = keptL := by
  refine (batchAccept_lang P hw ha).antisymm fun tree member => ?_
  rcases member with rfl | ⟨word, rfl⟩
  · exact (batchAccept_accepts hP hs).1
  · simpa using batchAccept_accepts_word hP hs word.toNat

end Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch
