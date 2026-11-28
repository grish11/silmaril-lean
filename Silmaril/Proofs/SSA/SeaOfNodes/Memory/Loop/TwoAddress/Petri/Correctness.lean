module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.RVSDG.OrderedRuntime.Structured.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Thms
import Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Proofs

open RVSDG (Locals Port Tuple Wires)
open RVSDG.NestedTheta (Term iterate)
open RVSDG.NestedTheta.Petri (Finishes finishes_iff)
open RVSDG.OrderedRuntime.Structured (Ty readOrigin read_cons runtimePort)

set_option backward.isDefEq.respectTransparency false

variable {args : List ValueSort} {cells : Nat}

private theorem get_read {entry ports : List (Ty ValueSort)}
    {past : List (List (Ty ValueSort))} {t : Ty ValueSort}
    (p : Port ports t) (wires : Wires entry past ports) (entryValues : Tuple (WireVal cells) entry)
    (locals : Locals (WireVal cells) past) :
    (wires.read entryValues locals).get p = readOrigin (wires.get p) entryValues locals := by
  induction p with
  | head => cases wires with | cons source rest => rw [read_cons]; rfl
  | tail _ ih => cases wires with | cons source rest => rw [read_cons]; exact ih rest

private theorem read_route (graph : Graph args) {entry : List (Ty ValueSort)}
    {past : List (List (Ty ValueSort))} (wires : Wires entry past (Packet args))
    (entryValues : Tuple (WireVal cells) entry) (locals : Locals (WireVal cells) past) :
    Wires.read (route graph wires) entryValues locals = route graph (wires.read entryValues locals) := by
  cases wires with
  | cons tag payload =>
    cases payload with
    | cons first payload =>
      cases payload with
      | cons second rest =>
        let wires : Wires entry past (Packet args) := .cons tag (.cons first (.cons second rest))
        conv_rhs => rw [read_cons, read_cons, read_cons]
        change Wires.read (.cons tag (.cons (wires.get (.tail (argumentPort graph.feedbackFirst)))
          (.cons (wires.get (.tail (argumentPort graph.feedbackSecond))) rest))) entryValues locals = _
        rw [read_cons, read_cons, read_cons]
        have firstRead := get_read (.tail (argumentPort graph.feedbackFirst)) wires entryValues locals
        have secondRead := get_read (.tail (argumentPort graph.feedbackSecond)) wires entryValues locals
        simp only [wires, read_cons] at firstRead secondRead
        exact congrArg₂ (fun a b =>
          Tuple.cons (F := WireVal cells) (t := .control 2) (readOrigin tag entryValues locals)
            (.cons a (.cons b (Wires.read rest entryValues locals))))
          firstRead.symm secondRead.symm

private theorem eval_routeReturns (graph : Graph args)
    (entry : Tuple (WireVal cells) (carrier (activationArgs args))) :
    {past sigs : List (List (Ty ValueSort))} →
    (term : RVSDG.Term ThetaOpcode (carrier (activationArgs args)) past sigs (Packet args)) →
    (locals : Locals (WireVal cells) past) →
    (routeReturns graph term).eval (thetaRuntime cells) entry locals =
      route graph (term.eval (thetaRuntime cells) entry locals)
  | _, _, .ret wires, locals => read_route graph wires entry locals
  | _, _, .bind _ _ rest, _ => eval_routeReturns graph entry rest _

private theorem lowerBody_run (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells)
    (fuel : Nat) :
    (Term.ofBase (lowerBody graph)).run (thetaRuntime cells) fuel (encodeHeader header input) =
      some (activationPacket graph input header) := by
  rw [Term.run_ofBase]
  have routed := eval_routeReturns graph (encodeHeader header input) graph.activation.thetaBody PUnit.unit
  change (some (RVSDG.Term.run (lowerBody graph) (thetaRuntime cells) (encodeHeader header input))) = _
  rw [show (lowerBody graph).run (thetaRuntime cells) (encodeHeader header input) =
      route graph (graph.activation.thetaBody.run (thetaRuntime cells) (encodeHeader header input)) from routed,
    encodeHeader, Loop.Graph.thetaBody_run]
  let operands := header.operands input
  let result := graph.activation.body.denote operands header.heap
  let tag := continueTag result.1 (graph.activation.stopWord operands)
  have first := encodeInput_get graph.feedbackFirst operands result.2
  have second := encodeInput_get graph.feedbackSecond operands result.2
  change some (Tuple.cons (F := WireVal cells) (t := .control 2) tag
    (.cons ((encodeInput result.2 operands).get (argumentPort graph.feedbackFirst))
      (.cons ((encodeInput result.2 operands).get (argumentPort graph.feedbackSecond))
        (encodeInput result.2 input)))) = _
  rw [first, second]
  by_cases stop : result.1 = graph.activation.stopWord operands <;>
    simp [activationPacket, Graph.step, Loop.Graph.step, tag, continueTag, result, operands, stop] <;>
    rfl

theorem lowerActivation_run (graph : Graph args) (input : Tuple (Val cells) args) (header : Header cells)
    (fuel : Nat) :
    (lowerActivation graph).run (thetaRuntime cells) fuel (encodeHeader header input) =
      some (activationPacket graph input header) := by
  rw [lowerActivation, ← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph, lowerBody_run]

theorem lowerActivation_finishes_iff (graph : Graph args) (input : Tuple (Val cells) args)
    (header : Header cells) (packet : Tuple (WireVal cells) (Packet args)) :
    Finishes (thetaRuntime cells) (lowerActivation graph) (encodeHeader header input) packet ↔
      packet = activationPacket graph input header := by
  rw [finishes_iff]
  change (∃ fuel, (lowerActivation graph).run (thetaRuntime cells) fuel (encodeHeader header input) =
    some packet) ↔ _
  simp only [lowerActivation_run, Option.some.injEq, exists_const]
  exact eq_comm

theorem read_entryWires (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    (entryWires graph).read (encodeInput heap input) PUnit.unit =
      encodeHeader (graph.seed input heap) input := by
  rw [entryWires, read_cons, read_cons, Loop.read_argWires]
  simp only [readOrigin, encodeHeader, Graph.seed, Header.operands, encodeInput, encodeInput_get]

private def output (graph : Graph args)
    (result : Tuple (WireVal cells) (carrier (activationArgs args))) : Word × Heap cells :=
  (result.get (argumentPort graph.activation.stop),
    result.get (runtimePort (dataPorts (activationArgs args))))

private theorem get_heap (input : Tuple (Val cells) args) (heap : Heap cells) :
    (encodeInput heap input).get (runtimePort (dataPorts args)) = heap := by
  induction input with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem stopWord_feedback (graph : Graph args) (input : Tuple (Val cells) args)
    (header : Header cells) (heap : Heap cells) :
    graph.activation.stopWord ((graph.feedback input header heap).operands input) =
      graph.activation.stopWord (header.operands input) := by
  unfold Loop.Graph.stopWord Header.operands
  generalize graph.activation.stop = port
  cases port with
  | tail port => cases port; rfl

private theorem output_feedback (graph : Graph args) (input : Tuple (Val cells) args)
    (header : Header cells) (heap : Heap cells) :
    output graph (encodeHeader (graph.feedback input header heap) input) =
      (graph.activation.stopWord (header.operands input), heap) := by
  unfold output encodeHeader
  rw [encodeInput_get, get_heap]
  exact Prod.ext (stopWord_feedback graph input header heap) rfl

private theorem iterate_run (graph : Graph args) (input : Tuple (Val cells) args)
    (ambient budget : Nat) (header : Header cells) :
    (iterate ((Term.ofBase (lowerBody graph)).run (thetaRuntime cells) ambient)
        (fun tag => tag.down.val == 1) (budget + 1) (encodeHeader header input)).map (output graph) =
      graph.evalWithin input budget header := by
  induction budget generalizing header with
  | zero =>
    rw [iterate, lowerBody_run, Graph.evalWithin]
    by_cases stop : (graph.activation.body.denote (header.operands input) header.heap).1 =
        graph.activation.stopWord (header.operands input)
    · simp [activationPacket, Graph.step, Loop.Graph.step, stop, output_feedback]
      exact Prod.ext stop.symm rfl
    · simp [activationPacket, Graph.step, Loop.Graph.step, stop, iterate]
  | succ budget ih =>
    rw [iterate, lowerBody_run, Graph.evalWithin]
    by_cases stop : (graph.activation.body.denote (header.operands input) header.heap).1 =
        graph.activation.stopWord (header.operands input)
    · simp [activationPacket, Graph.step, Loop.Graph.step, stop, output_feedback]
      exact Prod.ext stop.symm rfl
    · simpa [activationPacket, Graph.step, Loop.Graph.step, stop] using
        ih (graph.feedback input header (graph.activation.body.denote (header.operands input) header.heap).2)

theorem lower_run (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells)
    (budget : Nat) :
    (lower graph).run (thetaRuntime cells) (budget + 1) (encodeInput heap input) =
      (graph.evalWithin input budget (graph.seed input heap)).map
        (fun (word, final) => encodeResult word final) := by
  rw [lower, ← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  let encode : Word × Heap cells → Tuple (WireVal cells) _ := fun result =>
    encodeResult result.1 result.2
  change (iterate ((Term.ofBase (lowerBody graph)).run (thetaRuntime cells) (budget + 1))
    (fun tag => tag.down.val == 1) (budget + 1)
    ((entryWires graph).read (encodeInput heap input) PUnit.unit)).bind
      (some ∘ encode ∘ output graph) = _
  rw [← Option.map_eq_bind, ← Option.map_map, read_entryWires, iterate_run]

private theorem lower_run_zero (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    (lower graph).run (thetaRuntime cells) 0 (encodeInput heap input) = none := by
  rw [lower, ← RVSDG.NestedTheta.Graph.run_toTerm, Term.toTerm_toGraph]
  rfl

theorem lower_finishes_iff (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells)
    (word : Word) (final : Heap cells) :
    Finishes (thetaRuntime cells) (lower graph) (encodeInput heap input) (encodeResult word final) ↔
      graph.Returns input heap word final := by
  rw [finishes_iff]
  change (∃ fuel, (lower graph).run (thetaRuntime cells) fuel (encodeInput heap input) =
    some (encodeResult word final)) ↔ _
  have compare (budget : Nat) :
      (lower graph).run (thetaRuntime cells) (budget + 1) (encodeInput heap input) =
        some (encodeResult word final) ↔
      graph.evalWithin input budget (graph.seed input heap) = some (word, final) := by
    rw [lower_run]
    rcases graph.evalWithin input budget (graph.seed input heap) with _ | ⟨value, state⟩
    · simp
    · simp only [Option.map_some, Option.some.injEq]
      exact ⟨fun equal => Prod.ext (congrArg (fun result => result.get .head) equal)
        (congrArg (fun result => result.get (.tail .head)) equal), congrArg (fun result : Word × Heap cells =>
          encodeResult result.1 result.2)⟩
  constructor
  · rintro ⟨fuel, result⟩
    cases fuel with
    | zero => simp [lower_run_zero] at result
    | succ budget => exact ⟨budget, (compare budget).mp result⟩
  · rintro ⟨budget, result⟩
    exact ⟨budget + 1, (compare budget).mpr result⟩

theorem no_finishes_iff (graph : Graph args) (input : Tuple (Val cells) args) (heap : Heap cells) :
    (∀ output, ¬ Finishes (thetaRuntime cells) (lower graph) (encodeInput heap input) output) ↔
      ∀ budget, graph.evalWithin input budget (graph.seed input heap) = none := by
  constructor
  · intro missing budget
    rcases observed : graph.evalWithin input budget (graph.seed input heap) with _ | ⟨word, final⟩
    · rfl
    · exact False.elim (missing (encodeResult word final)
        ((lower_finishes_iff graph input heap word final).mpr ⟨budget, observed⟩))
  · intro missing output completion
    obtain ⟨fuel, observed⟩ := (finishes_iff _ _ _ _).mp completion
    cases fuel with
    | zero => simp [lower_run_zero] at observed
    | succ budget => simp [lower_run, missing] at observed

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Proofs
