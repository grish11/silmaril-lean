module

import Silmaril.Semantics.Brookes.Word.EventSync.Thms
import Silmaril.Proofs.Semantics.Brookes.Word.Regression

namespace Silmaril.Proofs.Semantics.Brookes.Word.EventSync.Regression

open Silmaril.Semantics.Brookes
open Silmaril.Semantics.Brookes.Word
open Silmaril.Semantics.Brookes.Word.EventSync
open Silmaril.Semantics.ConcurrentTrace (Letter ofWord)

private def interpret {S : Type} (p q : Command S) : Letter Bool Unit → Command S
  | .event .. => p
  | .sync .. => q

/-- Disjoint store updates assigned to an event and a nonparticipating sync
descend at endpoints, while their open behaviors distinguish the two orders. -/
example :
    ∃ letter : Letter Bool Unit → Command (Bool × Bool),
      (∃ f : Silmaril.Semantics.ConcurrentTrace.Trace Bool Unit → (Bool × Bool) → (Bool × Bool) → Prop,
        ∀ word, f (ofWord word) = endpoints (eval letter word)) ∧
      ¬ (∃ f : Silmaril.Semantics.ConcurrentTrace.Trace Bool Unit → Command (Bool × Bool),
        ∀ word, f (ofWord word) = eval letter word) := by
  obtain ⟨p, q, endpointsEq, openNe⟩ :=
    Proofs.Semantics.Brookes.Word.Regression.disjointWrites_separate_observations
  refine ⟨interpret p q, exists_denoteEndpoints_iff.mpr ?_, ?_⟩
  · intro a b h
    cases h with
    | events => rfl
    | eventSync => exact endpointsEq
    | syncEvent => exact endpointsEq.symm
  · intro factors
    have independent : Letter.Independent (.event false ()) (.sync [true]) :=
      .eventSync (by simp)
    exact openNe ((exists_denote_iff.mp factors) independent)

end Silmaril.Proofs.Semantics.Brookes.Word.EventSync.Regression
