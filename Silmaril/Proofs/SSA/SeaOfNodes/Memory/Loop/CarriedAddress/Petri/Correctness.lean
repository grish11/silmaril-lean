module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Thms
import Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri.Proofs

open RVSDG (Port Tuple)
open RVSDG.NestedTheta (Term iterate thetaResults single_vertex_results)
open RVSDG.NestedTheta.Petri (Finishes finishes_iff)
open RVSDG.OrderedRuntime.Structured (Threaded runtimePort)
open SeaOfNodes.Loop (Incoming argWires)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution (PortMap denote_mapBody pullInput)

set_option backward.isDefEq.respectTransparency false

variable {args : List ValueSort} {cells : Nat}

private theorem pull_tail {source target : List ValueSort} {sort : ValueSort}
    (rename : PortMap source target) (value : Val cells sort) (input : Tuple (Val cells) target) :
    pullInput (fun p => .tail (rename p)) (.cons value input) = pullInput rename input := by
  induction source with
  | nil => rfl
  | cons _ _ ih => simp only [pullInput, Tuple.get, ih]

private theorem pull_identity (input : Tuple (Val cells) args) :
    pullInput (fun p => p) input = input := by
  induction input with
  | nil => rfl
  | cons _ _ ih => simp only [pullInput, Tuple.get, pull_tail, ih]

private theorem operands_eq (graph : Graph args) (input : Tuple (Val cells) args) (arrival : Incoming) :
    pullInput (addressPort graph arrival) input = graph.operands input arrival := by
  change Tuple.cons (input.get (arrival.select graph.entryAddress graph.backedgeAddress))
    (pullInput (fun p => p) input) = _
  rw [pull_identity]
  rfl

private theorem stopWord_eq (graph : Graph args) (input : Tuple (Val cells) args) (arrival : Incoming) :
    graph.activation.stopWord (graph.operands input arrival) = input.get (stopPort graph) := by
  unfold Loop.Graph.stopWord stopPort
  generalize graph.activation.stop = p
  cases p
  rfl

private theorem arm_body (graph : Graph args) (input : Tuple (Val cells) args) (arrival : Incoming)
    (heap : Heap cells) :
    (arm graph arrival).body.denote input heap =
      graph.activation.body.denote (graph.operands input arrival) heap := by
  change (Memory.Diamond.Institution.mapBody (addressPort graph arrival) graph.activation.body).denote
    input PUnit.unit heap = _
  exact (denote_mapBody (addressPort graph arrival) graph.activation.body input PUnit.unit heap).trans
    (congrArg (fun inputs => graph.activation.body.denote inputs heap) (operands_eq graph input arrival))

theorem lowerBody_run (graph : Graph args) (input : Tuple (Val cells) args) (arrival : Incoming)
    (heap : Heap cells) (fuel : Nat) :
    (lowerBody graph).run (thetaRuntime cells) fuel (encodeArrival arrival heap input) =
      some (match graph.step input arrival heap with
        | .inl (_, final) => .cons ⟨0⟩ (encodeArrival .entry final input)
        | .inr next => .cons ⟨1⟩ (encodeArrival .backedge next input)) := by
  let entry := encodeArrival arrival heap input
  change ((match (argWires (carried args) []).read entry PUnit.unit with
    | .cons tag payload => (Term.ofBase (arm graph (occurrence tag.down)).thetaBody).run
        (thetaRuntime cells) fuel payload).bind fun output =>
      some (Tuple.cons (output.get .head) ((thetaResults (carried args)).read entry (output, PUnit.unit)))) = _
  rw [read_argWires]
  have arrived : occurrence (arrivalColour arrival).down = arrival := by cases arrival <;> rfl
  change ((Term.ofBase (arm graph (occurrence (arrivalColour arrival).down)).thetaBody).run
      (thetaRuntime cells) fuel (encodeInput heap input)).bind _ = _
  rw [arrived, Term.run_ofBase, Loop.Graph.thetaBody_run, Option.bind_some]
  let observed := (arm graph arrival).body.denote input heap
  let values : Tuple (WireVal cells) (carried args) :=
    .cons (continueTag observed.1 ((arm graph arrival).stopWord input)) (encodeInput observed.2 input)
  have wires : (thetaResults (carried args)).read entry (values, PUnit.unit) = values :=
    single_vertex_results entry values
  change some (Tuple.cons (values.get .head) ((thetaResults (carried args)).read entry (values, PUnit.unit))) = _
  rw [wires]
  dsimp only [values, observed]
  rw [arm_body]
  let native := graph.activation.body.denote (graph.operands input arrival) heap
  let tag := continueTag native.1 (input.get (stopPort graph))
  change some (Tuple.cons (F := WireVal cells) (t := .control 2) tag
    (Tuple.cons (F := WireVal cells) (t := .control 2) tag (encodeInput native.2 input))) = _
  rw [Graph.step, Loop.Graph.step, stopWord_eq]
  change _ = some (match (if native.1 = input.get (stopPort graph) then Sum.inl native else Sum.inr native.2) with
    | .inl (_, final) => Tuple.cons (F := WireVal cells) (t := .control 2) ⟨0⟩ (encodeArrival .entry final input)
    | .inr next => Tuple.cons (F := WireVal cells) (t := .control 2) ⟨1⟩ (encodeArrival .backedge next input))
  by_cases stopped : native.1 = input.get (stopPort graph) <;>
    simp [tag, continueTag, stopped, encodeArrival, arrivalColour, Incoming.select]

private theorem iterate_run (graph : Graph args) (input : Tuple (Val cells) args)
    (ambient budget : Nat) (arrival : Incoming) (heap : Heap cells) :
    iterate ((lowerBody graph).run (thetaRuntime cells) ambient) (fun tag => tag.down.val == 1)
        (budget + 1) (encodeArrival arrival heap input) =
      (graph.evalWithin input budget arrival heap).map (fun result => encodeArrival .entry result.2 input) := by
  induction budget generalizing arrival heap with
  | zero =>
    rw [iterate, lowerBody_run, Graph.evalWithin]
    rcases graph.step input arrival heap with ⟨word, final⟩ | next <;> rfl
  | succ budget ih =>
    rw [iterate, lowerBody_run, Graph.evalWithin]
    rcases graph.step input arrival heap with ⟨word, final⟩ | next
    · rfl
    · exact ih .backedge next

private theorem get_heap (input : Tuple (Val cells) args) (heap : Heap cells) :
    (encodeInput heap input).get (runtimePort (dataPorts args)) = heap := by
  induction input with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem step_stop_word (graph : Graph args) (input : Tuple (Val cells) args)
    (arrival : Incoming) (heap : Heap cells) {result : Word × Heap cells}
    (step : graph.step input arrival heap = .inl result) :
    result.1 = input.get (stopPort graph) := by
  rw [Graph.step, Loop.Graph.step, stopWord_eq] at step
  dsimp only at step
  split at step
  next stop => cases step; exact stop
  next => cases step

private theorem evalWithin_stop_word (graph : Graph args) (input : Tuple (Val cells) args)
    (arrival : Incoming) (heap : Heap cells) (budget : Nat) {result : Word × Heap cells}
    (run : graph.evalWithin input budget arrival heap = some result) :
    result.1 = input.get (stopPort graph) := by
  induction budget generalizing arrival heap with
  | zero =>
    cases step : graph.step input arrival heap with
    | inl observed =>
      have eq : some observed = some result := by simpa only [Graph.evalWithin, step, Sum.elim_inl] using run
      exact step_stop_word graph input arrival heap (step.trans (congrArg Sum.inl (Option.some.inj eq)))
    | inr next => simp [Graph.evalWithin, step] at run
  | succ budget ih =>
    cases step : graph.step input arrival heap with
    | inl observed =>
      have eq : some observed = some result := by simpa only [Graph.evalWithin, step, Sum.elim_inl] using run
      exact step_stop_word graph input arrival heap (step.trans (congrArg Sum.inl (Option.some.inj eq)))
    | inr next =>
      exact ih .backedge next (by simpa only [Graph.evalWithin, step, Sum.elim_inr] using run)

theorem lower_run (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) (budget : Nat) :
    (lower graph).run (thetaRuntime cells) (budget + 1) (encodeArrival .entry heap input) =
      (graph.evalWithin input budget .entry heap).map (fun (word, final) => encodeResult word final) := by
  rw [lower, ← RVSDG.NestedTheta.Graph.run_toTerm, RVSDG.NestedTheta.Term.toTerm_toGraph]
  let entry := encodeArrival .entry heap input
  let output (result : Tuple (WireVal cells) (carried args)) :=
    encodeResult (result.get (.tail (argumentPort (stopPort graph))))
      (result.get (.tail (runtimePort (dataPorts args))))
  change (iterate ((lowerBody graph).run (thetaRuntime cells) (budget + 1)) (fun tag => tag.down.val == 1)
    (budget + 1) ((argWires (carried args) []).read entry PUnit.unit)).bind
      (fun result => some (output result)) = _
  rw [read_argWires, show entry = encodeArrival .entry heap input from rfl, iterate_run]
  rcases evaluated : graph.evalWithin input budget .entry heap with _ | ⟨word, final⟩
  · rfl
  · have stop := evalWithin_stop_word graph input .entry heap budget evaluated
    change some (encodeResult ((encodeInput final input).get (argumentPort (stopPort graph)))
      ((encodeInput final input).get (runtimePort (dataPorts args)))) = some (encodeResult word final)
    rw [encodeInput_get, get_heap, ← show word = input.get (stopPort graph) from stop]

private theorem encodeResult_injective :
    Function.Injective (fun result : Word × Heap cells => encodeResult result.1 result.2) := by
  intro left right equal
  exact Prod.ext (congrArg (fun output => output.get .head) equal)
    (congrArg (fun output => output.get (.tail .head)) equal)

theorem lower_finishes_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) (word : Word) (final : Heap cells) :
    Finishes (thetaRuntime cells) (lower graph) (encodeArrival .entry heap input) (encodeResult word final) ↔
      ∃ budget, graph.evalWithin input budget .entry heap = some (word, final) := by
  rw [finishes_iff]
  change (∃ fuel, (lower graph).run (thetaRuntime cells) fuel (encodeArrival .entry heap input) =
    some (encodeResult word final)) ↔ _
  have compare (budget : Nat) :
      (lower graph).run (thetaRuntime cells) (budget + 1) (encodeArrival .entry heap input) =
        some (encodeResult word final) ↔ graph.evalWithin input budget .entry heap = some (word, final) := by
    rw [lower_run]
    rcases graph.evalWithin input budget .entry heap with _ | ⟨value, state⟩
    · simp
    · simp only [Option.map_some, Option.some.injEq]
      exact ⟨fun equal => @encodeResult_injective cells (value, state) (word, final) equal,
        fun equal => congrArg (fun result => encodeResult result.1 result.2) equal⟩
  constructor
  · rintro ⟨fuel, result⟩
    cases fuel with
    | zero =>
      have empty : (lower graph).run (thetaRuntime cells) 0 (encodeArrival .entry heap input) = none := by
        rw [lower, ← RVSDG.NestedTheta.Graph.run_toTerm, RVSDG.NestedTheta.Term.toTerm_toGraph]
        rfl
      rw [empty] at result
      cases result
    | succ budget => exact ⟨budget, (compare budget).mp result⟩
  · rintro ⟨budget, result⟩
    exact ⟨budget + 1, (compare budget).mpr result⟩

theorem finishes_iff_memref_run (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) (word : Word) (final : Heap cells) :
    Finishes (thetaRuntime cells) (lower graph) (encodeArrival .entry heap input) (encodeResult word final) ↔
      ∃ budget, MemRef.run graph input budget ⟨heap⟩ = some (word, Buffer.mk final) := by
  rw [lower_finishes_iff]
  apply exists_congr
  intro budget
  rw [MemRef.run_eq_evalWithin]
  rcases graph.evalWithin input budget .entry heap with _ | ⟨value, state⟩ <;> simp

theorem no_finishes_iff_memref_none (graph : Graph args) (input : Tuple (Val cells) args)
    (heap : Heap cells) :
    (∀ word final, ¬ Finishes (thetaRuntime cells) (lower graph) (encodeArrival .entry heap input)
      (encodeResult word final)) ↔
      ∀ budget, MemRef.run graph input budget ⟨heap⟩ = none := by
  constructor
  · intro missing budget
    rcases observed : MemRef.run graph input budget ⟨heap⟩ with _ | ⟨word, ⟨final⟩⟩
    · rfl
    · exact False.elim (missing word final ((finishes_iff_memref_run graph input heap word final).mpr
        ⟨budget, observed⟩))
  · intro missing word final complete
    obtain ⟨budget, observed⟩ := (finishes_iff_memref_run graph input heap word final).mp complete
    rw [missing budget] at observed
    cases observed

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Petri.Proofs
