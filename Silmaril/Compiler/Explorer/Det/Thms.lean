module

public import Silmaril.Compiler.Explorer.Det.Defs
public import Silmaril.Compiler.Explorer.Thms
import Silmaril.Proofs.Compiler.Explorer.Det

/-!
# The deterministic specialisation: theorems

* `DetProblem.refines_of_valid`: validity to the first return gives the generic, backward
  `Problem.Refines` (determinism makes the one run the only run).
* `DetMapping.valid_of_segments`: valid edges of a mapping that starts at the entry and relates no
  return give `DetProblem.Valid`; `DetMapping.refines_of_segments` gives `Problem.Refines`.
* `Det.discipline`: the cut-point segment discipline of a deterministic problem.
* `Det.Counterexample.edges_not_enough`: a valid listed edge, no coverage, and neither the
  problem nor its refinement.

Proofs: `Silmaril.Proofs.Compiler.Explorer.Det`.
-/

@[expose] public section

namespace Silmaril.Compiler.Explorer

variable {σ τ R : Type}

/-- **Validity to the first return is a refinement** of the generic reading. -/
theorem DetProblem.refines_of_valid (D : DetProblem σ τ R) (h : D.Valid) : D.toProblem.Refines :=
  Silmaril.Proofs.Compiler.Explorer.Det.refines_of_valid D h

/-- **Valid edges compose to the first return.** -/
theorem DetMapping.valid_of_segments {D : DetProblem σ τ R} (M : DetMapping D) (hs : M.Starts)
    (hv : M.Valid) (hnf : M.NoReturnAtPoints) : D.Valid :=
  Silmaril.Proofs.Compiler.Explorer.Det.valid_of_segments M hs hv hnf

/-- **Valid edges give the refinement.** -/
theorem DetMapping.refines_of_segments {D : DetProblem σ τ R} (M : DetMapping D) (hs : M.Starts)
    (hv : M.Valid) (hnf : M.NoReturnAtPoints) : D.toProblem.Refines :=
  D.refines_of_valid (M.valid_of_segments hs hv hnf)

/-- An edge at a point relating no states is valid. -/
theorem DetMapping.edge_vacuous {D : DetProblem σ τ R} (M : DetMapping D) (k : Nat)
    (h : M.toMapping.Unrelated k) : M.EdgeValid k :=
  Silmaril.Proofs.Compiler.Explorer.Det.edge_vacuous M k h

/-- **The cut-point segment discipline** of a deterministic problem: its mappings are
`DetMapping`s, an edge is valid when its segment is simulated, and a mapping is admissible when
no state related at a point is a return. -/
def Det.discipline (D : DetProblem σ τ R) : SegmentDiscipline D.toProblem where
  Map := DetMapping D
  toMapping M := M.toMapping
  EdgeValid M k := M.EdgeValid k
  Admissible M := M.NoReturnAtPoints
  vacuous M k h := M.edge_vacuous k h
  sound M ha hs hv :=
    M.refines_of_segments (fun x0 s he => hs s (x0, x0) ⟨rfl, he⟩) hv ha

/-- **Valid listed edges are not enough**: a deterministic problem and a mapping that starts at
the entry, whose only listed edge (point `0`) is valid, whose listed points do not cover the
mapping, and which is neither valid nor a refinement. -/
theorem Det.Counterexample.edges_not_enough :
    ∃ (D : DetProblem Nat Nat Unit) (M : DetMapping D), M.Starts ∧ (∀ k ∈ [0], M.EdgeValid k) ∧
      ¬ M.toMapping.Covers [0] ∧ ¬ D.Valid ∧ ¬ D.toProblem.Refines := by
  open Silmaril.Proofs.Compiler.Explorer.Det.Counterexample in
  exact ⟨problem, mapping, starts, by simpa using edge0, not_covers, not_valid, not_refines⟩

end Silmaril.Compiler.Explorer

end
