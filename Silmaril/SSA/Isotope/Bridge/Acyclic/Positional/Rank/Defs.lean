module

/-! # Rank synthesis by successive removal of local sinks -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Rank

variable {n : Nat}

/-- Record the first round in which all successors have been ranked.
Keep the current and previous rounds in vectors indexed by the original labels. -/
def rounds (targets : Fin n → List (Fin n)) : Nat → Vector (Option Nat) n
  | 0 => Vector.replicate n none
  | k + 1 =>
    let previous := rounds targets k
    Vector.ofFn fun i => (previous.get i).orElse fun _ =>
      if (targets i).all (fun j => (previous.get j).isSome) then some k else none

/-- Check that all entry targets have ranks by round `n`. -/
def checkFrom (targets : Fin n → List (Fin n)) (entry : List (Fin n)) : Bool :=
  let ranks := rounds targets n
  entry.all fun i => (ranks.get i).isSome

/-- The whole table must have ranks by round `n`. -/
def check (targets : Fin n → List (Fin n)) : Bool :=
  checkFrom targets (List.finRange n)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Rank
