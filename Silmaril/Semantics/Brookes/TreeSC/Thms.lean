module

public import Silmaril.Semantics.Brookes.TreeSC.Defs
import Silmaril.Proofs.Semantics.Brookes.TreeSC.Choice
import Silmaril.Proofs.Semantics.Brookes.TreeSC.Replay

public section

namespace Silmaril.Semantics.Brookes.TreeSC

open TrackA.Interaction
open TrackA.Concurrency

variable {R : Type} [DecidableEq R]

/-- A finite tree prefix and its store frames replay in the real SC primitive,
with the same final store and a residual program represented by the final tree. -/
theorem follows_iff_machine {gap : Gap R} {p : Code R} {s last : Store R}
    {frames : List (Frame R)} {y : Tree R} :
    Follows WeakITree.unfold gap p.toTree s frames y last ↔
      ∃ q, MachineFollows gap p s frames q last ∧ y = q.toTree :=
  Proofs.Semantics.Brookes.TreeSC.follows_iff_machine

/-- Completion on the tree side corresponds to a completed SC component. -/
theorem returns_iff_machine {gap : Gap R} {p : Code R} {s last : Store R}
    {frames : List (Frame R)} :
    Returns WeakITree.unfold gap p.toTree s frames () last ↔
      MachineFollows gap p s frames .done last :=
  Proofs.Semantics.Brookes.TreeSC.returns_iff_machine

/-- A forest chooses one initial component. A root index is never a
scheduler turn. -/
theorem forest_returns_iff_machine {I : Type*} {code : I → Code R} {gap : Gap R}
    {s last : Store R} {frames : List (Frame R)} :
    ForestReturns (Code.forest code) gap s frames () last ↔
      ∃ i, MachineFollows gap (code i) s frames .done last :=
  exists_congr fun _ => returns_iff_machine

/-- For either internal choice kind, a finished observation replays exactly
one complete alternative. An arity-zero choice has no finished observations. -/
theorem choice_returns_iff_machine {n : Nat} {kind : ChoiceKind} {code : Fin n → Code R}
    {gap : Gap R} {s last : Store R} {frames : List (Frame R)} :
    ForestReturns (choose kind code) gap s frames () last ↔
      ∃ i, MachineFollows gap (code i) s frames .done last :=
  ⟨fun ⟨_, path⟩ => Proofs.Semantics.Brookes.TreeSC.choice_returns_iff_machine.mp path,
    fun run => ⟨(), Proofs.Semantics.Brookes.TreeSC.choice_returns_iff_machine.mpr run⟩⟩

/-- Contiguous store frames project to exactly the finite closed singleton
SC runs. Conversely, every such SC run admits frames with those endpoints. -/
theorem closed_iff_sc {p q : Code R} {s last : Store R} {events : List (Event Unit Empty R)} :
    sc.MTr (Config.single (p, Shared.initial s)) events (Config.single (q, Shared.initial last)) ↔
      ∃ frames, frames.map (Frame.event ()) = events ∧ MachineFollows Eq p s frames q last :=
  Proofs.Semantics.Brookes.TreeSC.closed_iff_sc

/-- The closed singleton scheduler reaches done exactly for the finished
observations of the assembled weak ITree, after projecting the frames. -/
theorem closed_returns_iff_sc {p : Code R} {s last : Store R} {events : List (Event Unit Empty R)} :
    sc.MTr (Config.single (p, Shared.initial s)) events (Config.single (.done, Shared.initial last)) ↔
      ∃ frames, frames.map (Frame.event ()) = events ∧
        Returns WeakITree.unfold Eq p.toTree s frames () last := by
  simp only [closed_iff_sc, returns_iff_machine]

end Silmaril.Semantics.Brookes.TreeSC
