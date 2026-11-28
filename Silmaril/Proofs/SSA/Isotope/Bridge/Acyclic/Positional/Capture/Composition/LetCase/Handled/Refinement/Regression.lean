module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Refinement.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Reflection.Fixture

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests

open CategoryTheory Silmaril.Elgot.ITree
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.Structural.Finite (StructuralContext)
open LetCase (HandledTrace.Program HandledTrace.Arrow)
open LetIter.PaperExpression.Source.FreeTree.Response (Structured.Event)
open LetSeq.StraightLine.Structural (Log)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

/-! ## The order is discrete on the two composites

The composites are different native classes. At a policy that replays
every complete history, neither is below the other. -/

private noncomputable abbrev scriptedSemantics := handledFunctor (model Op) (scripted Op) input
private noncomputable abbrev permissiveSemantics := handledFunctor (model Op) (permissive Op) input

example : ¬ scriptedSemantics.map both ≤ scriptedSemantics.map mixed ∧
    ¬ scriptedSemantics.map mixed ≤ scriptedSemantics.map both :=
  ⟨fun below => native_differ ((handledFunctor_map_le_iff_eq input scripted_exposes both mixed).mp below),
    fun below => native_differ ((handledFunctor_map_le_iff_eq input scripted_exposes mixed both).mp below).symm⟩

example : ¬ permissiveSemantics.map both ≤ permissiveSemantics.map mixed ∧
    ¬ permissiveSemantics.map mixed ≤ permissiveSemantics.map both :=
  ⟨fun below => native_differ ((handledFunctor_map_le_iff_eq input permissive_exposes both mixed).mp below),
    fun below => native_differ ((handledFunctor_map_le_iff_eq input permissive_exposes mixed both).mp below).symm⟩

/-- On the operands themselves, without packing or a policy, neither the
tree relation nor inclusion of ordered outcomes holds in either direction. -/
example : ¬ TreeRefines (Case.seq route route) (Case.seq route echo) ∧
    ¬ TreeRefines (Case.seq route echo) (Case.seq route route) ∧
    ¬ OutcomeRefines (Case.seq route route) (Case.seq route echo) ∧
    ¬ OutcomeRefines (Case.seq route echo) (Case.seq route route) :=
  ⟨fun tree => native_differ (Quotient.sound ((treeRefines_iff_equiv input _ _).mp tree)),
    fun tree => native_differ (Quotient.sound ((treeRefines_iff_equiv input _ _).mp tree)).symm,
    fun outcomes => native_differ (Quotient.sound ((outcomeRefines_iff_equiv input _ _).mp outcomes)),
    fun outcomes => native_differ (Quotient.sound ((outcomeRefines_iff_equiv input _ _).mp outcomes)).symm⟩

/-- Natively equal arrows are comparable at every policy. -/
example : scriptedSemantics.map (term route ≫ 𝟙 native) ≤ scriptedSemantics.map (term route) :=
  handledFunctor_map_le_of_treeLE input (scripted Op)
    ((treeLE_iff_eq input (term route ≫ 𝟙 native) (term route)).mpr (Category.comp_id _))

/-! ## A pending request is replayed and separates

The script lists only the first exchange. The composite then shows its
second request pending. The single stage has already returned. -/

private abbrev firstExchange : Log Empty Op :=
  FreeMonoid.of ⟨Op.ask, request start.1 (tagOf start.2), low⟩

private abbrev pending : Trace (Events Op) Packed :=
  .exchange (.call Op.ask (request start.1 (tagOf start.2))) low
    (.request (.call Op.ask (request start.1 (tagOf (packet low)))))

example : exchanges pending = firstExchange * 1 := rfl

private theorem pending_shown :
    HandledTrace (scripted Op) firstExchange (twice start.1 start.2) pending :=
  ⟨(hasTrace_vis_exchange_iff _ _ _ _).mpr (hasTrace_vis_request _ _), 1, (mul_one _).symm, trivial⟩

private theorem pending_hidden : ¬ HasTrace (stage start.1 start.2) pending := by
  simp only [stage, hasTrace_vis_exchange_iff]
  rintro ⟨k, returned⟩
  rw [out_ret] at returned
  cases Part.some_injective returned

example : ¬ HandledTraceLE (scripted Op) firstExchange (twice start.1 start.2) (stage start.1 start.2) :=
  fun included => pending_hidden (included pending pending_shown).1

example : ¬ HandledTrace.Program.Refines (model Op) (scripted Op)
    (pack captures (Case.seq route route)) (pack captures route) := by
  intro refines
  have included := refines start firstExchange
  rw [run_twice, run_route] at included
  exact pending_hidden (included pending pending_shown).1

/-! ## Written graphs through the emitter and the readback -/

private def written : Interface Op captures input := ⟨exits, nonempty⟩
private def graph (p : CheckedTable Op Source exits) : written ⟶ written := Quotient.mk _ p

private def routeGraph : CheckedTable Op Source exits := CheckedTable.ofLetCase nonempty route.2
private def echoGraph : CheckedTable Op Source exits := CheckedTable.ofLetCase nonempty echo.2

private noncomputable abbrev writtenSemantics := ssaHandledFunctor (model Op) (scripted Op) input

example : routeGraph.table.check = true ∧ echoGraph.table.check = true := ⟨rfl, rfl⟩

/-- The hom order on the written graphs compares their emitted operands. -/
example : writtenSemantics.map (graph routeGraph) ≤ writtenSemantics.map (graph echoGraph) ↔
    TreeRefines routeGraph.toLetCase echoGraph.toLetCase :=
  ssaHandledFunctor_map_le_mk input scripted_exposes (X := written) (Y := written) routeGraph echoGraph

private theorem route_ne_echo : term route ≠ term echo := by
  intro same
  have trees := run_pack_eq_of_equiv (Quotient.exact same) start
  rw [run_route, run_echo] at trees
  have shown : HasTrace (stage start.1 start.2) (history (firstExchange * 1) (start.1, packet low)) := by
    simp only [stage, history_cons, history_one, hasTrace_vis_exchange_iff]
    exact out_ret _
  rw [trees] at shown
  simp only [history_cons, history_one, hasTrace_vis_exchange_iff] at shown
  have returned : out (ret ((start.1, other start.2) : Packed) : Tree (Events Op) Packed) =
      Part.some (.ret (start.1, packet low)) := shown
  rw [out_ret] at returned
  have exits : other start.2 = packet low := congrArg Prod.snd (Visible.ret.inj (Part.some_injective returned))
  cases exits

/-- The graphs read back from two different native classes are not
comparable, and the comparison is the one on the native classes. -/
example : ¬ writtenSemantics.map (graph routeGraph) ≤ writtenSemantics.map (graph echoGraph) := by
  have native := treeLE_iff_readback_le input scripted_exposes (term route) (term echo)
  have left : (readbackFunctor input).map (term route) = graph routeGraph := Case.readbackClass_mk nonempty route
  have right : (readbackFunctor input).map (term echo) = graph echoGraph := Case.readbackClass_mk nonempty echo
  rw [left, right] at native
  exact fun below => route_ne_echo ((treeLE_iff_eq input (term route) (term echo)).mp (native.mpr below))

example : writtenSemantics.map (graph routeGraph) ≤ writtenSemantics.map (graph echoGraph) ↔
    graph routeGraph = graph echoGraph :=
  ssaHandledFunctor_map_le_iff_eq input scripted_exposes (graph routeGraph) (graph echoGraph)

/-! ## Where the collapse stops

Both examples are trees outside the acyclic fragment or its signature. -/

/-- Silent divergence is strictly below a tree that makes a request. The
maximality of acyclic terms uses that they do not diverge. -/
example : TraceLE (diverge : Tree (Events Op) Packed) (stage start.1 start.2) ∧
    ¬ TraceLE (stage start.1 start.2) (diverge : Tree (Events Op) Packed) ∧
    ¬ Total (diverge : Tree (Events Op) Packed) := by
  refine ⟨traceLE_diverge _, fun below => ?_, fun total => ?_⟩
  · cases (hasTrace_diverge_iff _).mp (below _ (hasTrace_vis_request _ _))
  · have same := eq_of_total_traceLE total (traceLE_diverge (stage start.1 start.2))
    have shown : HasTrace (stage start.1 start.2) (.request (.call Op.ask (request start.1 (tagOf start.2)))) :=
      hasTrace_vis_request _ _
    rw [← same] at shown
    cases (hasTrace_diverge_iff _).mp shown

/-- A request whose reply type is empty. No primitive of the finite
structural signature is of this kind. -/
private inductive Stop : Type → Type where
  | stop : Stop PEmpty

private def halted : Tree Stop PUnit.{2} := vis .stop (fun reply => nomatch reply)
private def returned : Tree Stop PUnit.{2} := ret PUnit.unit

private def Completes {X : Type 1} : Trace Stop X → Prop
  | .result _ => True
  | .exchange _ _ tail => Completes tail
  | _ => False

/-- The halted tree has no divergence and no complete observation. All of
its complete observations are therefore observations of any tree, but its
pending request is lost. Inclusion of complete histories forces equality
only when reply types are inhabited. -/
example : Total halted ∧ (∀ p, Completes p → HasTrace halted p → HasTrace returned p) ∧
    ¬ TraceLE halted returned := by
  refine ⟨Total.vis _ _ (fun reply => nomatch reply), fun p complete seen => ?_, fun below => ?_⟩
  · cases p with
    | «prefix» => exact complete.elim
    | request e => exact complete.elim
    | result value =>
      have root : out halted = Part.some (.ret value) := seen
      rw [halted, out_vis] at root
      cases Part.some_injective root
    | exchange e reply tail =>
      obtain ⟨sameType, -, -⟩ := (hasTrace_vis_exchange _ _ e reply tail).mp seen
      subst sameType
      exact nomatch reply
  · obtain ⟨k, root⟩ := below (.request .stop) (hasTrace_vis_request _ _)
    rw [returned, out_ret] at root
    cases Part.some_injective root

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Free.Tests
