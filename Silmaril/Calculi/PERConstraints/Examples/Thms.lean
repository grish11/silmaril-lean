module

public import Silmaril.Calculi.PERConstraints.Examples.Defs
import Silmaril.Proofs.Calculi.PERConstraints.Examples

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.Examples

open Silmaril.Formats

theorem separation_sat : Dictionary.SAT separation := Proofs.separation_sat
theorem conflict_unsat : Dictionary.UNSAT conflict := Proofs.conflict_unsat

/-- The original dictionary is satisfiable, but its constant translation is not. -/
theorem collapsed_unsat : (CNF.map (fun _ : Bool => ()) (Dictionary.toCNF separation)).UNSAT :=
  Proofs.collapsed_unsat

/-- Imaging a set can turn the very same two terms into a satisfiable singleton. -/
theorem set_distinct_collapse :
    DISTINCT (PER.equality Unit) ((fun _ : Bool => ()) '' Set.univ) ∧
      ¬DISTINCT ((PER.equality Unit).pull (fun _ : Bool => ())) Set.univ :=
  Proofs.set_distinct_collapse

end Silmaril.Calculi.PERConstraints.Examples
