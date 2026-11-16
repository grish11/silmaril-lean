module

public import Silmaril.Wasm.Examples.JsonAccept.Stream.Defs
public import Silmaril.Wasm.Examples.JsonAccept.Exact.Thms
public import Silmaril.Semantics.StreamAcceptors.Thms

/-! # The JSON-subset acceptor, incrementally: theorems

* `streamAcceptor_correctInterleaved`: the automaton of the verified module, fed chunk by chunk,
  answers every query of every interleaving of `process`, `query` and `reset` with membership
  in `intText` of the bytes since the last reset (`CorrectInterleaved`).
* **The bridge to the Wasm module** (`answer_eq_wasm`): after any chunks of total length below
  `2 ^ 32`, the incremental answer is `true` iff the concatenation is accepted and never rejected
  by `prog`'s `accept` in the export embedding (`exportAcceptedNotRejected`, the combined verdict
  of `Exact.Thms`), for every profile and every non-empty host set. `answer_eq_false_wasm`: it is
  `false` iff the module rejects it.
* On unbounded chunk streams (`boundaryAnswer_eq_wasm`), the answer after `n` chunks is the
  module's verdict on the first `n` chunks, while they total less than `2 ^ 32` bytes. Longer
  inputs are outside the module's ABI (an `i32` length), not rejected by it.

So rechunking (`Acceptor.specObs_eq_of_toSymbolTrace_eq`) and the monitor verdicts of
`Silmaril.Semantics.StreamAcceptors` apply to the language decided by the Wasm module.
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.JsonAccept

open Silmaril Silmaril.Acceptor Silmaril.Wasm.Game.Accept
open Silmaril.Wasm.Numerics (Profile)

/-- Membership in `intText` is decided by the automaton. -/
instance : DecidablePred (· ∈ intText) := fun w => decidable_of_iff _ (acc_iff w)

theorem symbolAcceptor_pure : symbolAcceptor.Pure := fun _ => rfl

theorem foldl_stepN (q : Nat) (w : List UInt8) :
    w.foldl symbolAcceptor.process q = runN q (w.map UInt8.toNat) := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih => exact ih _

theorem symbolAcceptor_correct : symbolAcceptor.SymbolCorrect intText := fun w => by
  change accepting (w.foldl symbolAcceptor.process 0) = decide (w ∈ intText)
  rw [foldl_stepN, accepting]
  exact decide_eq_decide.2 (acc_iff w)

/-- **The automaton of the verified module is a correct incremental acceptor.** -/
theorem streamAcceptor_correctInterleaved (χ : Type) [ChunkView χ UInt8] :
    (streamAcceptor χ).CorrectInterleaved intText :=
  correctInterleaved_ofSymbols symbolAcceptor_pure (fun _ => rfl) symbolAcceptor_correct

theorem streamAcceptor_correctFold (χ : Type) [ChunkView χ UInt8] :
    (streamAcceptor χ).CorrectFold intText :=
  (streamAcceptor_correctInterleaved χ).correctFold

/-- **The incremental answer is the Wasm module's combined verdict.** -/
theorem answer_eq_wasm {χ : Type} [ChunkView χ UInt8] {P : Profile}
    {Hosts : Set (Silmaril.Wasm.Execution.Core.HostSemantics Nat)}
    {host : Silmaril.Wasm.Execution.Core.HostSemantics Nat} (hh : host ∈ Hosts) (cs : List χ)
    (hl : (cs.flatMap ChunkView.toList).length < 2 ^ 32) :
    ((streamAcceptor χ).query (cs.foldl (streamAcceptor χ).process (streamAcceptor χ).init)).1 = true ↔
      cs.flatMap ChunkView.toList ∈ exportAcceptedNotRejected P Hosts prog "accept" := by
  rw [streamAcceptor_correctFold χ cs, member_eq_true, exportAcceptedNotRejected_eq hh]
  exact ⟨fun h => ⟨h, hl⟩, And.left⟩

/-- **A `false` answer is the Wasm module's rejection.** -/
theorem answer_eq_false_wasm {χ : Type} [ChunkView χ UInt8] {P : Profile}
    {Hosts : Set (Silmaril.Wasm.Execution.Core.HostSemantics Nat)}
    {host : Silmaril.Wasm.Execution.Core.HostSemantics Nat} (hh : host ∈ Hosts) (cs : List χ)
    (hl : (cs.flatMap ChunkView.toList).length < 2 ^ 32) :
    ((streamAcceptor χ).query (cs.foldl (streamAcceptor χ).process (streamAcceptor χ).init)).1 = false ↔
      cs.flatMap ChunkView.toList ∈ exportRejected P Hosts prog "accept" := by
  rw [streamAcceptor_correctFold χ cs, exportRejected_eq hh, Bool.eq_false_iff, ne_eq,
    member_eq_true]
  exact ⟨fun h => ⟨h, hl⟩, And.left⟩

/-- **On unbounded streams**: the answer after `n` chunks is the Wasm module's combined verdict
on them, while they total less than `2 ^ 32` bytes. -/
theorem boundaryAnswer_eq_wasm {χ : Type} [ChunkView χ UInt8] {P : Profile}
    {Hosts : Set (Silmaril.Wasm.Execution.Core.HostSemantics Nat)}
    {host : Silmaril.Wasm.Execution.Core.HostSemantics Nat} (hh : host ∈ Hosts)
    (cs : Cslib.ωSequence χ) (n : ℕ) (hl : ((view cs).prefixAt n).length < 2 ^ 32) :
    (streamAcceptor χ).boundaryAnswer cs n = true ↔
      (view cs).prefixAt n ∈ exportAcceptedNotRejected P Hosts prog "accept" := by
  rw [boundaryAnswer_eq (streamAcceptor_correctFold χ), member_eq_true,
    exportAcceptedNotRejected_eq hh]
  exact ⟨fun h => ⟨h, hl⟩, And.left⟩

end Silmaril.Wasm.Examples.JsonAccept
