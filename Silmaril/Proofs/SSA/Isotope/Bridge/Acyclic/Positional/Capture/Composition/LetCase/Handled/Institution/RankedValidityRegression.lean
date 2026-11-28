module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Fixture

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory Silmaril.Elgot.ITree
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEntry RankedEquation denoteRanked grammarCase readGrammar)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Finite (StructuralContext)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-! ## Graphs read back from the two composites -/

private abbrev left : Operand Op Source Packet := Case.seq route route
private abbrev right : Operand Op Source Packet := Case.seq route echo

private def leftGraph : CheckedTable Op Source exits := CheckedTable.ofLetCase nonempty left.2
private def rightGraph : CheckedTable Op Source exits := CheckedTable.ofLetCase nonempty right.2

example : leftGraph.table.check = true ∧ rightGraph.table.check = true := ⟨rfl, rfl⟩

private theorem graphs_differ :
    ¬ Equiv false Γ₀ Source leftGraph.toLetCase.1 rightGraph.toLetCase.1 Packet := fun h =>
  native_differ (Quotient.sound (((CheckedTable.ofLetCase_emit false nonempty left.2).symm.trans h).trans
    (CheckedTable.ofLetCase_emit false nonempty right.2)))

/-- The ranked sentence between the two graphs, with an older capture
below the literal packed input. -/
private abbrev sentence : RankedEquation (sig Op) := rankedOf leftGraph rightGraph

/-- Its emitted operands are those of the two graphs. -/
example : grammarCase (readGrammar sentence) = captured leftGraph.toLetCase rightGraph.toLetCase :=
  grammarCase_read_rankedOf leftGraph rightGraph

/-! ## Soundness and completeness on this sentence -/

/-- It is not valid in the supported models of the existing ranked room. -/
example : ¬ RankedValid false sentence :=
  fun valid => graphs_differ ((rankedValid_rankedOf_iff input leftGraph rightGraph).mp valid)

/-- The sentence between a graph and itself is valid. -/
example : RankedValid false (rankedOf leftGraph leftGraph) :=
  (rankedValid_rankedOf_iff input leftGraph leftGraph).mpr (.refl leftGraph.toLetCase.2.toHasType)

/-- Validity is decided at the ordered trace model, which is supported. -/
example : RankedValid false sentence ↔
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Op)) (sig Op)).Sat
      (traceRankedModel Op) sentence :=
  rankedValid_iff_trace sentence (by rw [grammarCase_read_rankedOf]; exact separated_snoc input _)

example : Supported false (traceRegionModel Op) := trace_supported

/-- Satisfaction at that model is equality of the original ordered-exit
arrows of the two graphs. -/
example : (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Op)) (sig Op)).Sat
    (traceRankedModel Op) sentence ↔
      denoteRanked (traceJ (α := Empty) (Φ := Op)) (traceRegionModel Op) sentence.2.1 =
        denoteRanked (traceJ (α := Empty) (Φ := Op)) (traceRegionModel Op) sentence.2.2 :=
  sat_iff_denoteRanked (traceRegionModel Op) sentence

/-- Validity agrees with validity in all handled-trace models. -/
example : RankedValid false sentence ↔ ∀ M : HandledModel Op, (Institution.rankedRoom Op).Sat ⟨M⟩ sentence :=
  rankedValid_iff_handled_valid input leftGraph rightGraph

/-! ## A structural bound context without a packed input

Two one-row tables over the capture alone. Both ask with the capture
twice, and leave by opposite exits. The entries are ranked entries of the
existing ranked equations. -/

private def ask : Operand Op (captures.snoc .unit) Bit :=
  ⟨.op .ask (.pair (.bv 1) (.bv 1)), .op (.pair .bv .bv)⟩

private def direct : RankedEntry Op captures exits :=
  ⟨0, ⟨fun _ => .unit, fun _ => .case ask (.exit (i := 0) rfl) (.exit (i := 1) rfl)⟩, rfl, 0, ⟨.unit, .unit⟩⟩

private def swapped : RankedEntry Op captures exits :=
  ⟨0, ⟨fun _ => .unit, fun _ => .case ask (.exit (i := 1) rfl) (.exit (i := 0) rfl)⟩, rfl, 0, ⟨.unit, .unit⟩⟩

private abbrev closed : RankedEquation (sig Op) := ⟨⟨1, captures, exits⟩, direct, swapped⟩

/-- The whole bound context is structural, so the theorem applies. -/
example : RankedValid false closed ↔ Derivable false (grammarCase (readGrammar closed)) :=
  rankedValid_iff closed (by rw [emitted_case]; exact separated_of_structural input)

example : Derivable false (grammarCase (readGrammar closed)) ↔
    Equiv false Γ₀ captures (emitted (P := sig Op) direct).1 (emitted (P := sig Op) swapped).1 Packet :=
  derivable_iff false closed

/-! ## An injective renaming -/

private inductive Query | probe

private def rename : Query → Op
  | .probe => .ask

private theorem rename_injective : Function.Injective rename := fun a b _ => by cases a; cases b; rfl

private def routeQuery : Operand (Pulled rename) Source Packet :=
  ⟨.let₁ (.op Query.probe (.pair (.bv 1) (.case (.bv 0) (.inl .unit) (.inr .unit))))
    (.case (.bv 0) (.inl (.bv 0)) (.inr (.inl (.bv 0)))),
    .let₁ (.op (.pair .bv (.case .bv (.inl .unit) (.inr .unit))))
      (.case .bv (.inl .bv) (.inr (.inl .bv)))⟩

private def echoQuery : Operand (Pulled rename) Source Packet :=
  ⟨.let₁ (.op Query.probe (.pair (.bv 1) (.case (.bv 0) (.inl .unit) (.inr .unit))))
    (.case (.bv 1) (.inr (.inl .unit)) (.inl .unit)),
    .let₁ (.op (.pair .bv (.case .bv (.inl .unit) (.inr .unit))))
      (.case .bv (.inr (.inl .unit)) (.inl .unit))⟩

private abbrev leftQuery : Operand (Pulled rename) Source Packet := Case.seq routeQuery routeQuery
private abbrev rightQuery : Operand (Pulled rename) Source Packet := Case.seq routeQuery echoQuery

private def leftQueryGraph : CheckedTable (Pulled rename) Source exits := CheckedTable.ofLetCase nonempty leftQuery.2
private def rightQueryGraph : CheckedTable (Pulled rename) Source exits := CheckedTable.ofLetCase nonempty rightQuery.2

/-- The operands over the renamed primitive rename to the fixture's. -/
example : renameOperand rename leftQuery = left ∧ renameOperand rename rightQuery = right := ⟨rfl, rfl⟩

private theorem query_differ :
    ¬ Equiv false Γ₀ Source leftQueryGraph.toLetCase.1 rightQueryGraph.toLetCase.1 Packet := by
  intro h
  have operands : Equiv false Γ₀ Source leftQuery.1 rightQuery.1 Packet :=
    ((CheckedTable.ofLetCase_emit false nonempty leftQuery.2).symm.trans h).trans
      (CheckedTable.ofLetCase_emit false nonempty rightQuery.2)
  exact native_differ (Quotient.sound ((equiv_rename_iff input rename_injective leftQuery rightQuery).mpr operands))

/-- The ranked sentence over the renamed primitive is not valid, and
neither is its translation by the existing ranked signature map. -/
example : ¬ RankedValid false (rankedOf leftQueryGraph rightQueryGraph) ∧
    ¬ RankedValid false (renameRanked rename (rankedOf leftQueryGraph rightQueryGraph)) := by
  have source : ¬ RankedValid false (rankedOf leftQueryGraph rightQueryGraph) :=
    fun valid => query_differ ((rankedValid_rankedOf_iff input leftQueryGraph rightQueryGraph).mp valid)
  exact ⟨source, fun valid =>
    source ((rankedValid_rename_iff input rename_injective leftQueryGraph rightQueryGraph).mp valid)⟩

/-- Validity of the reflexive sentence is carried across the renaming. -/
example : RankedValid false (renameRanked rename (rankedOf leftQueryGraph leftQueryGraph)) :=
  (rankedValid_rename_iff input rename_injective leftQueryGraph leftQueryGraph).mpr
    ((rankedValid_rankedOf_iff input leftQueryGraph leftQueryGraph).mpr
      (.refl leftQueryGraph.toLetCase.2.toHasType))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
