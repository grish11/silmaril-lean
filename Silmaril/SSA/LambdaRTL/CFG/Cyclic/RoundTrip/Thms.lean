module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Thms
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.RoundTrip

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip

open Silmaril.Elgot

universe v w

variable {V W K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [Monad M] [LawfulMonad M]

/-- A hit in a packet-closed table observes only the incoming packet. A miss
returns the original label and payload. -/
theorem step_packetClosed_obs (model : Model F M α) (table : List (K × Block V K F))
    (closed : PacketClosedTable table) (input : V → α) (transfer : Transfer V K α) :
    Sum.map obs obs <$> Cyclic.step model table transfer =
      Cyclic.stepSSA model table input (obs transfer) :=
  Proofs.SSA.LambdaRTL.CFG.CyclicRoundTrip.step_packetClosed model table closed input transfer

/-- After a table lookup, the lexical block and its mutable renaming agree on
the next label and payload from any carried store. The packet supplies every
free register of a hit, so the lexical base environment is arbitrary. -/
theorem step_rename_obs (model : Model F M α) (graph : CFG V K F) {rename : V → W}
    (injective : Set.InjOn rename (support graph)) (closed : PacketClosed graph)
    (input : V → α) (transfer : Transfer W K α) :
    Sum.map obs obs <$> Cyclic.step model (renameGraph rename graph).blocks transfer =
      Cyclic.stepSSA model graph.blocks input (obs transfer) :=
  Proofs.SSA.LambdaRTL.CFG.CyclicRoundTrip.step_rename model graph injective closed input transfer

variable [Iterate M] [LawfulElgotMonad M]

/-- An already packet-closed table has the same ordered transfer when
run mutably at the same input and projected to its exit and payload. -/
theorem run_packetClosed_obs (model : Model F M α) (graph : CFG V K F)
    (closed : PacketClosed graph) (input : V → α) :
    obs <$> Cyclic.run model graph input = Cyclic.runSSA model graph input :=
  Proofs.SSA.LambdaRTL.CFG.CyclicRoundTrip.run_packetClosed_obs model graph closed input

/-- Reading a packet-closed lexical table as mutable RTL preserves the Elgot
observation whenever the initial environments agree on entry reads. This
preserves the packet representation and needs no laws for its encoding. -/
theorem run_rename_obs (model : Model F M α) (graph : CFG V K F) {rename : V → W}
    (injective : Set.InjOn rename (support graph)) (closed : PacketClosed graph)
    (input : V → α) (store : W → α)
    (entry_agrees : ∀ reg ∈ graph.entry.toRegion.fv, store (rename reg) = input reg) :
    obs <$> Cyclic.run model (renameGraph rename graph) store = Cyclic.runSSA model graph input :=
  Proofs.SSA.LambdaRTL.CFG.CyclicRoundTrip.run_rename model graph injective closed input store entry_agrees

/-- Re-versioning the mutable readback preserves the original lexical
computation. The version-zero inputs of the recompiled graph must agree with
the original free entry inputs after renaming. -/
theorem runSSA_rename_reversion (model : Model F M α) (pairs : model.PairLawful) (graph : CFG V K F)
    {rename : V → W} (injective : Set.InjOn rename (support graph)) (closed : PacketClosed graph)
    (input : V → α) (recompiledInput : W × Nat → α)
    (entry_agrees : ∀ reg ∈ graph.entry.toRegion.fv, recompiledInput (rename reg, 0) = input reg) :
    Cyclic.runSSA model (Versioning.compile (renameGraph rename graph)) recompiledInput =
      Cyclic.runSSA model graph input :=
  (Versioning.run_commutes model pairs _ recompiledInput).symm.trans
    (run_rename_obs model graph injective closed input _ entry_agrees)

/-- The finite-support deversioning can use the same lexical environment at
both endpoints when the free entry registers are version zero. The original
graph may have any packet layout that closes its labelled bodies. -/
theorem runSSA_deversion_reversion [Infinite V] (model : Model F M α) (pairs : model.PairLawful)
    (graph : CFG (V × Nat) K F) (closed : PacketClosed graph)
    (entry_zero : ∀ reg ∈ graph.entry.toRegion.fv, reg.2 = 0) (input : V × Nat → α) :
    Cyclic.runSSA model (Versioning.compile (deversionGraph graph)) input =
      Cyclic.runSSA model graph input :=
  Proofs.SSA.LambdaRTL.CFG.CyclicRoundTrip.runSSA_deversion_reversion model pairs graph closed entry_zero input

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Versioning

open Silmaril.Elgot

universe v w

variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq V] [DecidableEq K] [Infinite V]
  [Monad M] [LawfulMonad M] [Iterate M] [LawfulElgotMonad M]

/-- The reconstructed mutable graph agrees with the source on the whole
Elgot computation of the exit label and payload, at the same initial store.
The pair law justifies packet decoding, and the infinite name supply gives
fresh names for the finitely many nonzero versions. -/
theorem roundTrip_run_obs (model : Model F M α) (pairs : model.PairLawful)
    (graph : CFG V K F) (store : V → α) :
    obs <$> Cyclic.run model (roundTrip graph) store = obs <$> Cyclic.run model graph store :=
  Proofs.SSA.LambdaRTL.CFG.CyclicRoundTrip.roundTrip_run_obs model pairs graph store

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Versioning
