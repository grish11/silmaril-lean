module

public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch.Thms
public import Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Examples

/-!
# Batches: the kept batch is accepted, the dropped one is not

For every profile admitting the interpreter's deterministic steps (`hP`) and a writer policy
with the sentinel `0` and without undefined behaviour, `batchAccept` accepts `nil` and `(3)`
(the run `run(3)` of `batchAccept_accepts`), its language is included in the kept batch
(`batchAccept_lang`), and the word `3`, built in the same run before `accept_batch(0)`, is not
accepted (`batchAccept_drops`).
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

end Silmaril.Wasm.Game.HandleAccept.AcceptVariants.Batch
