module

import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.MLIR.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Theta.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Theta.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Thms

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Regression

open Silmaril.SSA.SeaOfNodes
open Diamond (Val ValueSort dataPorts)
open GVN.Cyclic.Activation (Inputs headerInput headerLatch inputSlot)
open GVN.Cyclic.Builder (Built build?)
open GVN.Cyclic.Builder.Preheader (Native prepare)
open GVN.Cyclic.Pass (proposals tryProposal?)
open GVN.Cyclic.Deletion (DeletedLoop)
open GVN.Cyclic.Iteration.Preheader
open GVN.Cyclic.Iteration.Preheader.Theta (Program emit emit_entry emit_observe entryPrefix
  petri_no_completion_iff_observe_none)
open Loop (ThetaOpcode thetaRuntime)
open Silmaril.SSA.RVSDG.NestedTheta (MonadicModel Node)
open Silmaril.SSA.RVSDG.NestedTheta.Partial (observe)
open Silmaril.SSA.RVSDG.NestedTheta.Petri (Finishes activate finishes_iff primitive)
open Silmaril.SSA.RVSDG.Petri (Tokens read)
open Pure.SubZero (Opcode model word wordPort)
open Silmaril.SSA.RVSDG (Port Tuple Wires extend)
open scoped Pure.WordNormalize

private abbrev inputs : List (ValueSort Unit) := [.predicate, .predicate, word, word]
private abbrev carried : List (ValueSort Unit) := [.predicate, word, word, word]
private abbrev entrySigs : List (List (Diamond.Ty Unit)) := [[wordPort], [wordPort], [wordPort]]
private abbrev headerSigs : List (List (Diamond.Ty Unit)) := [[wordPort], [wordPort], [wordPort], [wordPort], [wordPort]]

private def y : Port inputs word := .tail (.tail .head)
private def z : Port inputs word := .tail (.tail (.tail .head))
private def firstLane : Port carried word := .tail .head
private def secondLane : Port carried word := .tail (.tail .head)
private def thirdLane : Port carried word := .tail (.tail (.tail .head))

private def increment {past : List (List (Diamond.Ty Unit))} (lane : Port carried word) :
    Wires (Loop.headerPorts inputs carried) past [wordPort, wordPort] :=
  .cons (.arg (headerLatch (inputSlot lane) (dataPorts inputs)))
    (.cons (.arg (headerInput (dataPorts carried) y)) .nil)

private def seedOperands {past : List (List (Diamond.Ty Unit))} :
    Wires (dataPorts inputs) past [wordPort, wordPort] :=
  .cons (.arg (inputSlot y)) (.cons (.arg (inputSlot z)) .nil)

private def feedback {sigs : List (List (Diamond.Ty Unit))} (same : Bool)
    (last : Fin (extend [] sigs).length) (port : Port (extend [] sigs)[last] wordPort) :
    Wires (Loop.headerPorts inputs carried) (extend [] sigs) (dataPorts carried) :=
  .cons (.arg (headerInput (dataPorts carried) (.tail .head)))
    (.cons (.output last port)
      (.cons (if same then .output last port else .arg (headerInput (dataPorts carried) y))
        (.cons (if same then .output last port else .arg (headerInput (dataPorts carried) z)) .nil)))

private def fixture (sameFeedback : Bool) : Native inputs carried entrySigs headerSigs word where
  preheader := .cons .add seedOperands (.cons .add seedOperands (.cons .add seedOperands .nil))
  header := .cons .add (increment firstLane)
    (.cons .add (increment secondLane)
      (.cons .add (increment thirdLane)
        (.cons .add (.cons (.output (0 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil))
          (.cons .add (.cons (.output (3 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil)) .nil))))
  phiInputs
    | .entry =>
      .cons (.arg .head) (.cons (.output (0 : Fin 3) .head)
        (.cons (.output (1 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil)))
    | .backedge => feedback (sigs := headerSigs) sameFeedback (4 : Fin 5) .head
  predicate := .arg (headerLatch (.head : Port (dataPorts carried) (.value .predicate)) (dataPorts inputs))
  result := .output (4 : Fin 5) .head

private def afterFirst : DeletedLoop Opcode inputs carried entrySigs word :=
  ⟨[[wordPort], [wordPort], [wordPort], [wordPort]], {
    preheader := (fixture true).preheader
    header := .cons .add (increment secondLane)
      (.cons .add (increment thirdLane)
        (.cons .add (.cons (.output (0 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil))
          (.cons .add (.cons (.output (2 : Fin 3) .head) (.cons (.output (1 : Fin 3) .head) .nil)) .nil)))
    phiInputs
      | .entry => (fixture true).phiInputs .entry
      | .backedge => feedback (sigs := [[wordPort], [wordPort], [wordPort], [wordPort]]) true (3 : Fin 4) .head
    predicate := .arg (headerLatch (.head : Port (dataPorts carried) (.value .predicate)) (dataPorts inputs))
    result := .output (3 : Fin 4) .head }⟩

private def afterSecond : DeletedLoop Opcode inputs carried entrySigs word :=
  ⟨[[wordPort], [wordPort], [wordPort]], {
    preheader := (fixture true).preheader
    header := .cons .add (increment secondLane)
      (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.output (0 : Fin 1) .head) .nil))
        (.cons .add (.cons (.output (1 : Fin 2) .head) (.cons (.output (0 : Fin 2) .head) .nil)) .nil))
    phiInputs
      | .entry => (fixture true).phiInputs .entry
      | .backedge => feedback (sigs := [[wordPort], [wordPort], [wordPort]]) true (2 : Fin 3) .head
    predicate := .arg (headerLatch (.head : Port (dataPorts carried) (.value .predicate)) (dataPorts inputs))
    result := .output (2 : Fin 3) .head }⟩

private theorem first_accepted :
    GVN.Cyclic.Builder.Preheader.optimize? (fixture true) = some afterFirst := rfl

private theorem second_accepted :
    GVN.Cyclic.Builder.Preheader.optimize? afterFirst.graph = some afterSecond := rfl

private theorem final_step : GVN.Cyclic.Builder.Preheader.optimize? afterSecond.graph = none := rfl

private theorem run_result : normalize (fixture true) = ⟨afterSecond, 2⟩ := by
  change run 5 (fixture true) = _
  rw [run_succ 4 (fixture true), first_accepted]
  dsimp only
  rw [run_succ 3 afterFirst.graph, second_accepted]
  dsimp only
  rw [run_succ 2 afterSecond.graph, final_step]

theorem two_restored_native_steps :
    (run 1 (fixture true)).rewrite = afterFirst ∧
      (normalize (fixture true)).rewrite.headerSigs.length = 3 ∧ (normalize (fixture true)).deletions = 2 := by
  rw [run_result]
  refine ⟨?_, rfl, rfl⟩
  rw [run_succ 0 (fixture true), first_accepted]
  rfl

theorem both_restored_headers_rebuild :
    (build? (prepare afterFirst.graph)).isSome = true ∧
      (build? (prepare afterSecond.graph)).isSome = true :=
  ⟨rfl, rfl⟩

theorem twice_rewritten_header_is_saturated :
    let prepared := prepare afterSecond.graph
    ∃ built : Built prepared, build? prepared = some built ∧
      ∀ proposal ∈ proposals built.view,
        tryProposal? built.view (GVN.Cyclic.FixedPoint.normalize built.graph) proposal = none := by
  have saturated := normalize_saturated (fixture true)
  dsimp only at saturated
  rw [run_result] at saturated
  exact saturated

private def input : Inputs model inputs :=
  .cons ⟨true⟩ (.cons ⟨false⟩ (.cons (3 : BitVec 64) (.cons (4 : BitVec 64) .nil)))

theorem native_observations_survive_both_rewrites :
    let final := (normalize (fixture true)).rewrite.graph
    final.step model input (final.initial model input) =
      .inr (.cons ⟨false⟩ (.cons (30 : BitVec 64) (.cons (30 : BitVec 64) (.cons (30 : BitVec 64) .nil)))) ∧
    final.evalBackedges model 0 input = none ∧ final.evalBackedges model 1 input = some (99 : BitVec 64) ∧
    (final.Returns model input (99 : BitVec 64) ↔ (fixture true).Returns model input (99 : BitVec 64)) := by
  refine ⟨?_, (normalize_evalBackedges (fixture true) input 0).trans rfl,
    (normalize_evalBackedges (fixture true) input 1).trans rfl,
    normalize_returns (fixture true) input (99 : BitVec 64)⟩
  rw [run_result]
  rfl

private theorem mismatched_feedback_step :
    GVN.Cyclic.Builder.Preheader.optimize? (fixture false) = none := rfl

theorem mismatched_feedback_is_an_admitted_fixed_point :
    (GVN.Cyclic.Builder.build? (GVN.Cyclic.Builder.Preheader.prepare (fixture false))).isSome = true ∧
      normalize (fixture false) = ⟨⟨headerSigs, fixture false⟩, 0⟩ := by
  refine ⟨rfl, ?_⟩
  change run 5 (fixture false) = _
  rw [run_succ 4 (fixture false), mismatched_feedback_step]

/-- Inspect the actual numbered θ's child signature at the end of the preheader. -/
private def emittedBodySize (program : Program inputs carried entrySigs word) : Option Nat :=
  let node := program.nodes (3 : Fin 5)
  if hasBody : 0 < node.kind.arity then some (node.childSigs ⟨0, hasBody⟩).length else none

theorem emitted_bodies_shrink_after_both_deletions :
    emittedBodySize (fixture true).lowerTheta = some 6 ∧
      emittedBodySize (run 1 (fixture true)).rewrite.graph.lowerTheta = some 5 ∧
      emittedBodySize (emit (fixture true)) = some 4 := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [two_restored_native_steps.1]
    rfl
  · unfold emit
    rw [run_result]
    rfl

theorem emitted_entry_wires_keep_every_lane :
    (entryPrefix (emit (fixture true))).map Prod.snd =
      [[.arg 2, .arg 3], [.arg 2, .arg 3], [.arg 2, .arg 3],
        [.arg 0, .arg 1, .arg 2, .arg 3, .arg 0, .output 0 0, .output 1 0, .output 2 0]] := by
  rw [emit_entry]
  rfl

theorem numbered_executions_return_99 :
    (fixture true).lowerTheta.run (thetaRuntime model) 2 input = some (.cons (99 : BitVec 64) .nil) ∧
      (emit (fixture true)).run (thetaRuntime model) 3 input = some (.cons (99 : BitVec 64) .nil) := by
  refine ⟨rfl, ?_⟩
  unfold emit
  rw [run_result]
  rfl

private def nonReturningInput : Inputs model inputs :=
  .cons ⟨true⟩ (.cons ⟨true⟩ (.cons (3 : BitVec 64) (.cons (4 : BitVec 64) .nil)))

private theorem no_native_return (value : BitVec 64) :
    ¬ (fixture true).Returns model nonReturningInput value := by
  apply (fixture true).not_returns_of_backedge_invariant model nonReturningInput value
    (fun old => (old.get .head).down = true) rfl
  intro old guard
  let next := (fixture true).latch model .backedge (Loop.appendTuple old nonReturningInput)
    ((fixture true).header.eval model (Loop.appendTuple old nonReturningInput) PUnit.unit)
  refine ⟨next, ?_, rfl⟩
  change (if (old.get .head).down then (Sum.inr next : BitVec 64 ⊕ Inputs model carried) else _) = Sum.inr next
  rw [guard]
  rfl

theorem numbered_executions_observe_absence :
    observe (MonadicModel.ofRuntime (thetaRuntime model)) (fixture true).lowerTheta nonReturningInput = Part.none ∧
      observe (MonadicModel.ofRuntime (thetaRuntime model)) (emit (fixture true)) nonReturningInput = Part.none := by
  have absent : observe (MonadicModel.ofRuntime (thetaRuntime model))
      (fixture true).lowerTheta nonReturningInput = Part.none := by
    apply Part.eq_none_iff.mpr
    intro result returned
    cases result with
    | cons value tail =>
      cases tail
      exact no_native_return value (((fixture true).lowerTheta_observe_eq_some model nonReturningInput value).mpr
        (Part.eq_some_iff.mpr returned))
  exact ⟨absent, (emit_observe (fixture true) nonReturningInput).trans absent⟩

private def publishPreheaderNode {past : List (List (Diamond.Ty Unit))} {ports : List (Diamond.Ty Unit)}
    (node : Node (ThetaOpcode Opcode) (dataPorts inputs) past ports)
    (colours : Tokens (Val model.value) past) : Option (Tokens (Val model.value) (past ++ [ports])) := do
  let ready ← read node.inputs input colours
  let published ← primitive (thetaRuntime model) node.kind ready
  return colours.snoc (published.map fun _ => some)

/-- Read the fourth root node using the colours published by the three
actual preheader primitives, then activate its existing θ child. -/
private def colouredEntry (program : Program inputs carried entrySigs word) :
    Σ ports : List (Diamond.Ty Unit), Option (Tuple (Val model.value) ports) :=
  let node := program.nodes (3 : Fin 5)
  ⟨node.kind.entry, do
    let first ← publishPreheaderNode (program.nodes (0 : Fin 5)) PUnit.unit
    let second ← publishPreheaderNode (program.nodes (1 : Fin 5)) first
    let third ← publishPreheaderNode (program.nodes (2 : Fin 5)) second
    let ready ← read node.inputs input third
    (activate (thetaRuntime model) node.kind ready).map Prod.snd⟩

private def received : Tuple (Val model.value) (Loop.headerPorts inputs carried) :=
  let latches : Inputs model carried :=
    .cons ⟨true⟩ (.cons (7 : BitVec 64) (.cons (7 : BitVec 64) (.cons (7 : BitVec 64) .nil)))
  Loop.appendTuple latches input

theorem both_coloured_entries_read_the_complete_packet :
    colouredEntry (fixture true).lowerTheta = ⟨_, some received⟩ ∧
      colouredEntry (emit (fixture true)) = ⟨_, some received⟩ := by
  refine ⟨rfl, ?_⟩
  unfold emit
  rw [run_result]
  rfl

theorem both_coloured_traces_complete_with_99 :
    Finishes (thetaRuntime model) (fixture true).lowerTheta input (.cons (99 : BitVec 64) .nil) ∧
      Finishes (thetaRuntime model) (emit (fixture true)) input (.cons (99 : BitVec 64) .nil) :=
  ⟨(finishes_iff _ _ _ _).mpr ⟨2, numbered_executions_return_99.1⟩,
    (finishes_iff _ _ _ _).mpr ⟨3, numbered_executions_return_99.2⟩⟩

theorem neither_coloured_graph_completes_on_closed_guard :
    (∀ packet, ¬ Finishes (thetaRuntime model) (fixture true).lowerTheta nonReturningInput packet) ∧
      ∀ packet, ¬ Finishes (thetaRuntime model) (emit (fixture true)) nonReturningInput packet :=
  ⟨(petri_no_completion_iff_observe_none _ _).mpr numbered_executions_observe_absence.1,
    (petri_no_completion_iff_observe_none _ _).mpr numbered_executions_observe_absence.2⟩

section CF

open GVN.Cyclic.Iteration.Preheader.MLIR
open Loop.MLIR.CF (evalOp)
open Silmaril.MLIR.Pure (Code OpSignature)
open Silmaril.MLIR.Arith (Width)

private def sourceCF : Artifact inputs carried := (emit? (fixture true)).get (by rfl)

private def firstCF : Artifact inputs carried := (emit? afterFirst.graph).get (by rfl)

private def normalizedCF : Artifact inputs carried := (emit? afterSecond.graph).get (by rfl)

private theorem sourceCF_emitted : emit? (fixture true) = some sourceCF := rfl

private theorem normalizedCF_emitted : emitNormalized? (fixture true) = some normalizedCF := by
  unfold emitNormalized?
  rw [run_result]
  rfl

private def bindingCount {Op : OpSignature} {Term : List Width → Type} {scope : List Width} :
    Code Op Term scope → Nat
  | .terminator _ => 0
  | .letOp _ _ rest => bindingCount rest + 1

theorem cf_emitted_headers_shrink_after_both_deletions :
    bindingCount (sourceCF.block .header) = 5 ∧
      bindingCount (firstCF.block .header) = 4 ∧
      bindingCount (normalizedCF.block .header) = 3 :=
  ⟨rfl, rfl, rfl⟩

theorem cf_emitted_entry_is_unchanged :
    normalizedCF.entry = sourceCF.entry :=
  emit_normalized_entry_eq sourceCF_emitted normalizedCF_emitted

theorem cf_entry_retains_captures_and_phi_packet :
    inputEnv input = .cons 1 (.cons 0 (.cons 3 (.cons 4 .nil))) ∧
      sourceCF.entry.eval evalOp (fun term env => term.eval env) (inputEnv input) =
        .inl ⟨.header, .cons 1 (.cons 7 (.cons 7 (.cons 7 .nil)))⟩ :=
  ⟨rfl, rfl⟩

theorem cf_both_return_99 :
    sourceCF.run evalOp 4 (inputEnv input) = some (.cons 99 .nil) ∧
      normalizedCF.run evalOp 5 (inputEnv input) = some (.cons 99 .nil) :=
  ⟨rfl, rfl⟩

theorem cf_neither_returns_on_closed_guard :
    sourceCF.Diverges evalOp (inputEnv nonReturningInput) ∧
      normalizedCF.Diverges evalOp (inputEnv nonReturningInput) := by
  have absent : sourceCF.Diverges evalOp (inputEnv nonReturningInput) := by
    intro fuel
    cases found : sourceCF.run evalOp fuel (inputEnv nonReturningInput) with
    | none => rfl
    | some packet =>
      cases packet with
      | cons bits tail =>
        cases tail
        exact (no_native_return bits ((emit_returns_iff sourceCF_emitted nonReturningInput bits).mp
          ⟨fuel, found⟩)).elim
  exact ⟨absent, (emit_normalized_diverges_iff sourceCF_emitted normalizedCF_emitted nonReturningInput).mpr absent⟩

private def withSub : Native inputs carried entrySigs headerSigs word :=
  { fixture true with
    preheader := .cons .sub seedOperands (.cons .add seedOperands (.cons .add seedOperands .nil)) }

theorem cf_refuses_native_subtraction : emit? withSub = none := rfl

end CF

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Iteration.Preheader.Regression
