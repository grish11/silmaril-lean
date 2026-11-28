module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Reduct.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Fixture

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory Silmaril.Elgot.ITree
open Silmaril.Logic.ITree.TraceInstitution (allRepliesModel)
open Silmaril.Isotope.Institution.Acyclic (CoherentRegionModel mapOperand)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation grammarCase readGrammar mapRanked readGrammar_map
  grammarCase_map rankedSignatureCorridor)
open Reverse (CheckedTable)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Reply (Γ₀)
open LetSeq.StraightLine.Structural.Categorical (traceJ)
open Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

/-! ## The sentence and a relabelling into a larger signature -/

private abbrev left : Operand Op Source Packet := Case.seq route route
private abbrev right : Operand Op Source Packet := Case.seq route echo

private def leftGraph : CheckedTable Op Source exits := CheckedTable.ofLetCase nonempty left.2
private def rightGraph : CheckedTable Op Source exits := CheckedTable.ofLetCase nonempty right.2

private theorem graphs_differ :
    ¬ Equiv false Γ₀ Source leftGraph.toLetCase.1 rightGraph.toLetCase.1 Packet := fun h =>
  native_differ (Quotient.sound (((CheckedTable.ofLetCase_emit false nonempty left.2).symm.trans h).trans
    (CheckedTable.ofLetCase_emit false nonempty right.2)))

/-- The ranked sentence between the two graphs, with an older capture. -/
private abbrev sentence : RankedEquation (sig Op) := rankedOf leftGraph rightGraph

/-- A second primitive with other shapes. -/
private inductive Wide | first | second

local instance : LetCase.Structural.Finite.Signature Wide where
  source
    | .first => .pair bitShape bitShape
    | .second => .unit
  target _ := bitShape

/-- The single primitive goes to the first of two. It is not the identity
and its source is the fixture's own signature. -/
private def widen : sig Op ⟶ sig Wide :=
  ⟨fun _ => Wide.first, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

private theorem widen_injective : Function.Injective widen.instr := fun a b _ => by cases a; cases b; rfl

/-! ## The reduct of a supported model is supported -/

/-- The ordered trace model over the larger signature. -/
private noncomputable abbrev larger := traceRegionModel Wide

/-- Its reduct along the relabelling: a model of the ranked room over the
smaller signature, with the larger signature's traces. -/
private noncomputable abbrev reduced := larger.reduct widen

example : Supported false larger := trace_supported

example : Supported false reduced := supported_reduct widen larger trace_supported

/-- The reduct keeps the type interpretation. -/
example : reduced.types = larger.types := rfl

/-! ## The satisfaction square on the sentence -/

private theorem square : (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom
      (traceJ (α := Empty) (Φ := Wide)) (sig Wide)).Sat
      (ShrinkHoms.toShrinkHoms (Discrete.mk larger)) (mapRanked widen.toSignatureMap sentence) ↔
    (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom (traceJ (α := Empty) (Φ := Wide)) (sig Op)).Sat
      (ShrinkHoms.toShrinkHoms (Discrete.mk reduced)) sentence :=
  sat_reduct widen larger sentence

/-- The translated sentence is the sentence between the relabelled
emitted operands, at the same typing index. -/
private theorem translated : grammarCase (readGrammar (mapRanked widen.toSignatureMap sentence)) =
    captured (mapOperand widen leftGraph.toLetCase) (mapOperand widen rightGraph.toLetCase) := by
  rw [readGrammar_map, grammarCase_map, mapCaseSignature_primitive, grammarCase_read_rankedOf]
  rfl

private theorem translated_differ : ¬ Equiv false Γ₀ Source (mapOperand widen leftGraph.toLetCase).1
    (mapOperand widen rightGraph.toLetCase).1 Packet := by
  intro h
  have larger : SatLe (allRepliesModel (events Wide))
      (captured (mapOperand widen leftGraph.toLetCase) (mapOperand widen rightGraph.toLetCase)) := satLe_of_equiv h
  have smaller := (satLe_hom widen widen_injective (allRepliesModel (events Wide))
    (captured leftGraph.toLetCase rightGraph.toLetCase)).mp larger
  rw [reduct_allReplies_hom] at smaller
  exact graphs_differ ((satLe_iff_equiv input allReplies_exposing _ _).mp smaller)

/-- The reduct is a supported model over the smaller signature that
rejects the sentence. -/
example : ¬ (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom
    (traceJ (α := Empty) (Φ := Wide)) (sig Op)).Sat (ShrinkHoms.toShrinkHoms (Discrete.mk reduced)) sentence := by
  intro holds
  have derivable := derivable_of_trace (mapRanked widen.toSignatureMap sentence)
    (by rw [translated]; exact separated_snoc input _) (square.mpr holds)
  rw [translated] at derivable
  exact translated_differ derivable

/-- Soundness applies at the reduct because it is supported. -/
example : (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom
    (traceJ (α := Empty) (Φ := Wide)) (sig Op)).Sat (ShrinkHoms.toShrinkHoms (Discrete.mk reduced))
      (rankedOf leftGraph leftGraph) :=
  sat_of_derivable reduced (supported_reduct widen larger trace_supported) (rankedOf leftGraph leftGraph)
    (by rw [grammarCase_read_rankedOf]; exact LetCase.LocallyNameless.Equiv.refl leftGraph.toLetCase.2.toHasType)

/-! ## The restricted room and its corridor -/

private noncomputable abbrev small := supportedRankedRoom (traceJ (α := Empty) (Φ := Wide)) false (sig Op)
private noncomputable abbrev big := supportedRankedRoom (traceJ (α := Empty) (Φ := Wide)) false (sig Wide)

private noncomputable abbrev corridor : small ⟶ big :=
  supportedCorridor (traceJ (α := Empty) (Φ := Wide)) false widen

/-- The corridor sends the supported larger model to the supported reduct. -/
example : corridor.mod.obj (ShrinkHoms.toShrinkHoms (Discrete.mk ⟨larger, trace_supported⟩)) =
    ShrinkHoms.toShrinkHoms (Discrete.mk ⟨reduced, supported_reduct widen larger trace_supported⟩) := rfl

/-- Its satisfaction condition on the sentence. -/
example (N : big.Mod) : big.Sat N (corridor.sen sentence) ↔ small.Sat (corridor.mod.obj N) sentence :=
  corridor.sat N sentence

/-- Restricting models commutes with the existing ranked signature corridor. -/
example : rankedSignatureCorridor (J := traceJ (α := Empty) (Φ := Wide)) widen.toSignatureMap ≫
      includeSupported (traceJ (α := Empty) (Φ := Wide)) false (sig Wide) =
    includeSupported (traceJ (α := Empty) (Φ := Wide)) false (sig Op) ≫ corridor :=
  supported_square widen

/-- Validity of the reflexive sentence is carried along the relabelling by
the model law, with no reflection step. -/
example (valid : RankedValid false (rankedOf leftGraph leftGraph)) :
    RankedValid false (mapRanked widen.toSignatureMap (rankedOf leftGraph leftGraph)) :=
  rankedValid_mapRanked widen _ valid

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
