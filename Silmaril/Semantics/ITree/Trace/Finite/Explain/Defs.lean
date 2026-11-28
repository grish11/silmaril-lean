module

public import Silmaril.Semantics.ITree.Trace.Finite.Defs

@[expose] public section

namespace Silmaril.Elgot.ITree.Finite

universe u v

/-- Run the same pruning rounds as `prune`. Compute explanations only for
removed pairs, using the explanations from strictly earlier rounds. -/
def pruneExplain {P : Type u} {W : Type v} [DecidableEq P]
    (keep : Finset P → P → Bool) (explain : (P → Option W) → P → Option W)
    (candidates : Finset P) (previous : P → Option W) : P → Option W :=
  let next := candidates.filter (fun p => keep candidates p = true)
  if _same : next = candidates then previous else
    pruneExplain keep explain next (fun p =>
      if p ∈ candidates ∧ p ∉ next then explain previous p else previous p)
termination_by candidates.card
decreasing_by
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, _same⟩)

variable {Q : Type} {Reply : Q → Type} {R S T : Type u}
  [DecidableEq Q] [DecidableEq R]

/-- The source has a result or pending request the target lacks, or an
actual typed reply leads to a pair with an earlier explanation. -/
def explainHead (replies : ∀ key, List (Reply key))
    (previous : S × T → Option (Trace (Event Q Reply) R)) :
    Head Q R S Reply → Head Q R T Reply → Option (Trace (Event Q Reply) R)
  | .stop, _ => none
  | .result left, .result right => if left = right then none else some (.result left)
  | .result value, _ => some (.result value)
  | .request left nextL, .request right nextR =>
    if same : left = right then
      (replies left).findSome? fun reply =>
        (previous (nextL reply, nextR (same ▸ reply))).map (Trace.exchange (.ask left) reply)
    else some (.request (.ask left))
  | .request key _, _ => some (.request (.ask key))

variable [DecidableEq S] [DecidableEq T] [∀ key, Fintype (Reply key)]

/-- Extract a finite trace of the left table missing on the right, if the
finite simulation rejects. Each reply list must cover its exact type. -/
def explain (replies : ∀ key, List (Reply key)) (statesL : Finset S) (statesR : Finset T)
    (left : S → Step Q R S Reply) (right : T → Step Q R T Reply) (startL : S) (startR : T) :
    Option (Trace (Event Q Reply) R) :=
  let headL := headFrom left statesL
  let headR := headFrom right statesR
  pruneExplain (fun pairs (l, r) => compatible pairs (headL l) (headR r))
    (fun previous (l, r) => explainHead replies previous (headL l) (headR r))
    (statesL ×ˢ statesR) (fun _ => none) (startL, startR)

end Silmaril.Elgot.ITree.Finite
