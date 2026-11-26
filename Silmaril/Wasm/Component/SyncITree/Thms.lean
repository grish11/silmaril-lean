module

public import Silmaril.Wasm.Component.SyncITree.Defs
public import Silmaril.Wasm.Component.Reference.SessionDiv.Defs
import Silmaril.Proofs.Wasm.Component.SyncITree.Session

public section

namespace Silmaril.Wasm.Component.SyncITree

open Silmaril.Games
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Elgot

variable {c : Simple} {o : GrowOracle} {r : Ready c} {q : Question c}
  {s s' : Store Nat} {a : q.Answer}
  {qs : List (Question c)} {outs : List (Option (List Val))}

/-- The abstract body observer recovers exactly the terminal Core/ABI
judgements, including the final store of a trapped call. -/
theorem responds_iff : Responds o r q s a s' ↔ Finishes o r q s a s' :=
  Silmaril.Proofs.Wasm.Component.SyncITree.responds_iff

/-- Silent divergence of the tree is equivalent to an actual infinite internal
Core run. A missing result with no such run has the separate `noOutcome` tag. -/
theorem diverges_iff :
    ((body o r q).run ⟨s⟩).run = ITree.diverge ↔
      DivAt (profile o) r.inst c.exports[q.exportIdx] q.args.val s :=
  Silmaril.Proofs.Wasm.Component.SyncITree.diverges_iff

/-- Exact agreement in both directions for completed typed sessions of the
resumable reference machine, which includes successful instantiation.
The Core profile is deterministic. The component choice profile is arbitrary. -/
theorem completes_iff_reference (prof : ProfileKind) :
    Completes o r qs outs ↔ refOuts outs ∈ sessObs (profile o) prof c (qs.map Question.erase) :=
  Silmaril.Proofs.Wasm.Component.SyncITree.completes_iff_reference prof

/-- Exact agreement with the game's completed typed plays. The length premise
ensures that `sessMoves` reads the entire session. -/
theorem completes_iff_game (hlen : qs.length = outs.length) :
    Completes o r qs outs ↔
      sessMoves c (qs.map Question.erase) outs ∈ c.toComp.den (modSem (profile o)) :=
  Silmaril.Proofs.Wasm.Component.SyncITree.completes_iff_game hlen

/-- A finite game prefix ending in the next typed export question exists
exactly when its preceding rounds complete. An outstanding question makes
no assertion about the answer or divergence of its activation. -/
theorem pending_iff_game (hlen : qs.length = outs.length) (q : Question c) :
    Completes o r qs outs ↔
      sessMoves c (qs.map Question.erase) outs ++ [.inr (.ask q.gameOp)] ∈
        c.toComp.den (modSem (profile o)) :=
  Silmaril.Proofs.Wasm.Component.SyncITree.pending_iff_game hlen q

/-- Exact agreement with reference quiescent divergence after a finite
sequence of completed rounds. -/
theorem quiet_iff_reference (prof : ProfileKind) (q : Question c) :
    Quiet o r qs outs q ↔
      outs ∈ refDivs (profile o) prof c (qs.map Question.erase) q.exportIdx q.args.val :=
  Silmaril.Proofs.Wasm.Component.SyncITree.quiet_iff_reference prof q

end Silmaril.Wasm.Component.SyncITree
