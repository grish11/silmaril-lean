module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Fixture

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory Silmaril.Elgot.ITree
open Silmaril.Logic.ITree.TraceInstitution (allRepliesModel)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open LetSeq.StraightLine.Structural (Log)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-! ## The two composites in the categorical class

The composites read an older capture and are different native classes. -/

private abbrev left : Operand Op Source Packet := Case.seq route route
private abbrev right : Operand Op Source Packet := Case.seq route echo

private theorem not_equiv : ¬ Equiv false Γ₀ Source left.1 right.1 Packet :=
  fun h => native_differ (Quotient.sound h)

/-- They are not valid in the existing class, with objects in `Type 1`
and homs in `Type`. The ordered trace model separates them. -/
example : ¬ LetCase.Structural.Reply.Valid left.2 right.2 :=
  fun valid => not_equiv ((categorical_valid_iff_equiv input left right).mp valid)

/-- They are not valid in the class one universe up either. The free
request tree model separates them. -/
example : ¬ CaseValidAt.{2, 2, 1, 1} left right :=
  fun valid => not_equiv ((caseValidAt_tree_iff_equiv input left right).mp valid)

/-- The separation in the class one universe up is by the two free trees
in some environment. -/
example : ∃ ρ, left.2.denote Val (model Op) (fun x => x.elim) ρ ≠
    right.2.denote Val (model Op) (fun x => x.elim) ρ := by
  by_contra none
  exact not_equiv ((treeRefines_iff_equiv input left right).mp fun ρ => by
    have same : left.2.denote Val (model Op) (fun x => x.elim) ρ =
        right.2.denote Val (model Op) (fun x => x.elim) ρ := by
      by_contra differ
      exact none ⟨ρ, differ⟩
    exact same ▸ fun _ seen => seen)

/-! ## Handled-trace models against the class -/

private abbrev allReplies : HandledModel Op := allRepliesModel (events Op)
private abbrev scriptedModel : HandledModel Op := ⟨Log Empty Op, fun _ => True, scripted Op⟩
private abbrev alternatingModel : HandledModel Op := ⟨Bool, fun _ => True, alternating⟩

/-- A model that replays every history satisfies the directed sentence
exactly when it is valid in the existing class. -/
example : (SatLe allReplies (captured left right) ↔ LetCase.Structural.Reply.Valid left.2 right.2) ∧
    (SatLe scriptedModel (captured left right) ↔ LetCase.Structural.Reply.Valid left.2 right.2) :=
  ⟨satLe_iff_valid input allReplies_exposing left right,
    satLe_iff_valid input (exposing_of_exposes scripted_exposes) left right⟩

/-- The state-flipping model satisfies the sentence although it is not
valid in the class. One fixed policy does not give categorical equality. -/
example : SatLe alternatingModel (captured left right) ∧ ¬ LetCase.Structural.Reply.Valid left.2 right.2 :=
  ⟨(satLe_iff_refines alternating left right).mpr fun w state => by
      rw [run_twice, run_crossed]
      exact (alternating_collapses state w.1 w.2).1,
    fun valid => not_equiv ((categorical_valid_iff_equiv input left right).mp valid)⟩

/-- Validity in all handled-trace models is validity in the existing class. -/
example : (∀ M : HandledModel Op, SatLe M (captured left right)) ↔ LetCase.Structural.Reply.Valid left.2 right.2 :=
  handled_valid_iff_categorical_valid input left right

/-! ## Written graphs in the existing ranked room -/

private def leftGraph : CheckedTable Op Source exits := CheckedTable.ofLetCase nonempty left.2
private def rightGraph : CheckedTable Op Source exits := CheckedTable.ofLetCase nonempty right.2

example : leftGraph.table.check = true ∧ rightGraph.table.check = true := ⟨rfl, rfl⟩

private theorem graphs_differ :
    ¬ Equiv false Γ₀ Source leftGraph.toLetCase.1 rightGraph.toLetCase.1 Packet := fun h =>
  not_equiv (((CheckedTable.ofLetCase_emit false nonempty left.2).symm.trans h).trans
    (CheckedTable.ofLetCase_emit false nonempty right.2))

/-- The existing ranked room, at the ordered trace model, rejects the
ranked sentence between the two graphs read back from the composites. -/
example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Op)) (sig Op)).Sat
    (traceRankedModel Op) (rankedOf leftGraph rightGraph) :=
  fun holds => graphs_differ ((sat_rankedOf_trace_iff_equiv input leftGraph rightGraph).mp holds)

/-- It accepts the sentence between a graph and itself. -/
example : (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Op)) (sig Op)).Sat
    (traceRankedModel Op) (rankedOf leftGraph leftGraph) :=
  (sat_rankedOf_trace_iff_equiv input leftGraph leftGraph).mpr (.refl leftGraph.toLetCase.2.toHasType)

/-- The categorical ranked room at the ordered trace model and the handled
ranked room at a model that replays every history agree on this sentence. -/
example : (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Op)) (sig Op)).Sat
    (traceRankedModel Op) (rankedOf leftGraph rightGraph) ↔
      (Institution.rankedRoom Op).Sat ⟨scriptedModel⟩ (rankedOf leftGraph rightGraph) :=
  sat_rankedOf_trace_iff_handled input (exposing_of_exposes scripted_exposes) leftGraph rightGraph

/-- The handled ranked room at the state-flipping model disagrees with
the categorical ranked room on it. -/
example : (Institution.rankedRoom Op).Sat ⟨alternatingModel⟩ (rankedOf leftGraph rightGraph) ∧
    ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Op)) (sig Op)).Sat
      (traceRankedModel Op) (rankedOf leftGraph rightGraph) := by
  refine ⟨?_, fun holds => graphs_differ ((sat_rankedOf_trace_iff_equiv input leftGraph rightGraph).mp holds)⟩
  have operands : SatLe alternatingModel (captured left right) :=
    (satLe_iff_refines alternating left right).mpr fun w state => by
      rw [run_twice, run_crossed]
      exact (alternating_collapses state w.1 w.2).1
  exact (sat_readback nonempty left right ⟨alternatingModel⟩).mpr operands

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
