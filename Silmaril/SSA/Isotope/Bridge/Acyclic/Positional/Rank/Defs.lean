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

/-- The whole table must have ranks by round `n`. -/
def check (targets : Fin n → List (Fin n)) : Bool :=
  let ranks := rounds targets n
  (List.finRange n).all fun i => (ranks.get i).isSome

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Rank
