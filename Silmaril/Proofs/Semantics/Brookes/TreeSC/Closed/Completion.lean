module

public import Silmaril.Semantics.Brookes.TreeSC.Closed.Defs
public import Silmaril.Semantics.Brookes.Thms
public import Silmaril.Semantics.Brookes.TreeSC.Thms

public section

namespace Silmaril.Proofs.Semantics.Brookes.TreeSC.Closed

open Silmaril.Semantics.Brookes
open Silmaril.Semantics.Brookes.TreeSC
open Silmaril.Semantics.TrackA.Interaction

variable {R : Type} [DecidableEq R]

/-- Supply continuity to a list whose individual frames are already valid. -/
private theorem stores_of_runs {initial last s t : Store R} {frames : List (Frame R)}
    (valid : StoreFollows openGap initial frames last)
    (run : Runs s (frames.map Frame.transition) t) :
    StoreFollows Eq s frames t := by
  induction valid generalizing s t with
  | nil =>
    cases run
    exact .nil _
  | @cons _ _ frame tail _ valid _ ih =>
    change Runs s ((frame.before, frame.after) :: tail.map Frame.transition) t at run
    cases run with
    | cons rest => exact .cons rfl valid (ih rest)

private theorem runs_of_stores {s t : Store R} {frames : List (Frame R)}
    (stores : StoreFollows Eq s frames t) : Runs s (frames.map Frame.transition) t := by
  induction stores with
  | nil => exact .nil _
  | cons pre _ _ ih =>
    cases pre
    exact .cons ih

private theorem open_stores {s t : Store R} {frames : List (Frame R)}
    (stores : StoreFollows Eq s frames t) : StoreFollows openGap s frames t := by
  induction stores with
  | nil => exact .nil _
  | cons _ valid _ ih => exact .cons trivial valid ih

theorem treeBehavior_completes_iff {B : Signature} {A X : Type*}
    {tree : Coalgebra (signature R) B A X} {root : X} {s t : Store R} {result : A} :
    (treeBehavior tree root).completes s t result ↔
      ∃ frames, Returns tree Eq root s frames result t := by
  rw [treeBehavior, Behavior.completes_generate_iff]
  constructor
  · rintro ⟨_, _, hseed, run⟩
    obtain ⟨initial, frames, last, ⟨y, z, ⟨path, stores⟩, silent, ret⟩, rfl⟩ := hseed
    cases frames with
    | nil =>
      change Runs s [(initial, initial)] t at run
      cases run with
      | cons rest =>
        cases rest
        exact ⟨[], y, z, ⟨path, .nil _⟩, silent, ret⟩
    | cons frame tail =>
      exact ⟨frame :: tail, y, z, ⟨path, stores_of_runs stores run⟩, silent, ret⟩
  · rintro ⟨frames, y, z, ⟨path, stores⟩, silent, ret⟩
    refine ⟨returnTrace s frames, returnTrace_ne_nil _ _,
      ⟨s, frames, t, ⟨y, z, ⟨path, open_stores stores⟩, silent, ret⟩, rfl⟩, ?_⟩
    cases frames with
    | nil =>
      cases stores
      exact .cons (.nil _)
    | cons => exact runs_of_stores stores

end Silmaril.Proofs.Semantics.Brookes.TreeSC.Closed
