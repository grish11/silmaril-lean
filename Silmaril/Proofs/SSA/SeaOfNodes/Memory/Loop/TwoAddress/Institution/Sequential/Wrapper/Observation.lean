module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Wrapper.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Memory.RVSDG.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Wrapper.Proofs

open RVSDG (Locals Origin Tuple Wires)
open RVSDG.NestedTheta.Institution
open RVSDG.OrderedRuntime.Structured (runtime runtimePort withRuntime read_cons read_appended readOrigin)
open Memory.Diamond.Institution (PortMap pullInput pullInput_get)

variable {args entry outs : List ValueSort} {cells : Nat}

set_option backward.isDefEq.respectTransparency false

private theorem heap_get (input : Tuple (Val cells) entry) (heap : Heap cells) :
    (encodeInput heap input).get (runtimePort (dataPorts entry)) = heap := by
  induction input with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem read_captures {past : List (List (RVSDG.OrderedRuntime.Structured.Ty ValueSort))}
    (lift : ∀ {t}, Origin (carrier entry) [] t → Origin (carrier entry) past t)
    (ports : PortMap outs entry) (input : Tuple (Val cells) entry) (initial final : Heap cells)
    (live : Origin (carrier entry) past runtime) (locals : Locals (WireVal cells) past)
    (argsAgree : ∀ {t} p, readOrigin (lift (.arg (t := t) p)) (encodeInput initial input) locals =
      (encodeInput initial input).get p)
    (heapAgree : readOrigin live (encodeInput initial input) locals = final) :
    Wires.read (withRuntime live ((Boundary.captureWires entry outs ports).map (fun _ o => lift o)))
      (encodeInput initial input) locals = encodeInput final (pullInput ports input) := by
  induction outs with
  | nil =>
    simp only [Boundary.captureWires, Tuple.map, withRuntime, read_cons, heapAgree, pullInput, encodeInput]
    rfl
  | cons _ _ ih =>
    simp only [Boundary.captureWires, Tuple.map, withRuntime, read_cons, argsAgree, encodeInput_get, pullInput, encodeInput]
    rw [ih]

private theorem seed_read (graph : Graph args) (ports : PortMap args entry)
    (input : Tuple (Val cells) entry) (heap : Heap cells) :
    Wires.read (withRuntime (.arg (runtimePort (dataPorts entry))) (seedWires graph ports))
      (encodeInput heap input) PUnit.unit =
    Petri.encodeHeader (graph.seed (pullInput ports input) heap) (pullInput ports input) := by
  have dataRead := read_captures (fun o => o) ports input heap heap
    (.arg (runtimePort (dataPorts entry))) PUnit.unit (fun _ => rfl) (heap_get input heap)
  have identity : ∀ {sorts : List (RVSDG.OrderedRuntime.Structured.Ty ValueSort)}
      (ws : Wires (carrier entry) [] sorts), ws.map (fun _ o => o) = ws := by
    intro _ wires
    induction wires with
    | nil => rfl
    | cons _ _ ih => simp only [Tuple.map, ih]
  rw [identity] at dataRead
  simp only [seedWires, withRuntime, read_cons, readOrigin, encodeInput_get, Petri.encodeHeader,
    Header.operands, Graph.seed, encodeInput, pullInput_get]
  rw [dataRead]

private theorem pull_under {sort : ValueSort} (reserved : Val cells sort) (input : Tuple (Val cells) entry)
    (ports : PortMap args entry) :
    pullInput (fun p => .tail (ports p)) (Tuple.cons (F := Val cells) reserved input) =
      pullInput ports input := by
  induction args with
  | nil => rfl
  | cons _ _ ih =>
    simp only [pullInput, ih]
    rfl

private theorem pull_identity (input : Tuple (Val cells) args) : pullInput (fun p => p) input = input := by
  induction input with
  | nil => rfl
  | cons head tail ih =>
    simp only [pullInput, Tuple.get]
    rw [pull_under, ih]

private theorem wrap_observe (graph : Graph args) (ports : PortMap args entry)
    (wires : Wires (carrier entry) [carrier (activationArgs args)] (dataPorts outs))
    (input : Tuple (Val cells) entry) (initial : Heap cells)
    (keep : Tuple (WireVal cells) (carrier [.word]) → Tuple (WireVal cells) (carrier outs))
    (retEq : ∀ exit : Tuple (WireVal cells) (carrier (activationArgs args)),
      Wires.read (withRuntime (RVSDG.OrderedRuntime.Structured.nextRuntime [] (dataPorts (activationArgs args))) wires)
        (encodeInput initial input) (exit, PUnit.unit) =
      keep (encodeResult (exit.get (argumentPort graph.activation.stop))
        (exit.get (runtimePort (dataPorts (activationArgs args)))))) :
    RuntimeObservation.observe (P := target) (thetaRuntime cells) (wrapTerm graph ports wires).toGraph
        (encodeInput initial input) =
      (RuntimeObservation.observe (P := target) (thetaRuntime cells) (Petri.lower graph)
        (encodeInput initial (pullInput ports input))).map keep := by
  simp only [RuntimeObservation.observe, RVSDG.NestedTheta.Partial.observe, Petri.lower,
    RVSDG.NestedTheta.Term.toTerm_toGraph, wrapTerm, Petri.lowerTerm, RVSDG.NestedTheta.Term.denoteOpenWith,
    RVSDG.NestedTheta.ExplicitRuntime.thetaNode]
  rw [seed_read, Petri.read_entryWires]
  simp only [Part.bind_eq_bind, Part.map_bind]
  congr 1
  funext exit
  change Part.some _ = (Part.some _).map keep
  rw [Part.map_some]
  exact congrArg Part.some (retEq exit)

theorem forwarding_observe (graph : Graph args) (ports : PortMap args entry)
    (input : Tuple (Val cells) entry) (initial : Heap cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime cells) (forwarding graph ports) (encodeInput initial input) =
      (RuntimeObservation.observe (P := target) (thetaRuntime cells) (Petri.lower graph)
        (encodeInput initial (pullInput ports input))).map (producerOutput input) := by
  unfold forwarding
  rw [wrap_observe]
  · intro exit
    let live : Origin (carrier entry) [carrier (activationArgs args)] runtime :=
      RVSDG.OrderedRuntime.Structured.nextRuntime [] (dataPorts (activationArgs args))
    have dataRead := read_captures
      (RVSDG.NestedTheta.ExplicitRuntime.Splice.weaken (carrier (activationArgs args))) (fun p => p)
      input initial (exit.get (runtimePort (dataPorts (activationArgs args)))) live (exit, PUnit.unit)
      (fun p => rfl) rfl
    rw [pull_identity] at dataRead
    simp only [forwardingWires, withRuntime, read_cons]
    rw [dataRead]
    rfl

theorem producer_observe (graph : Graph args) (input : Tuple (Val cells) args) (initial : Heap cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime cells) (producer graph) (encodeInput initial input) =
      (RuntimeObservation.observe (P := target) (thetaRuntime cells) (Petri.lower graph)
        (encodeInput initial input)).map (producerOutput input) := by
  unfold producer
  rw [forwarding_observe, pull_identity]

theorem consumer_observe (graph : Graph args) (first : Word) (input : Tuple (Val cells) args) (initial : Heap cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime cells) (consumer graph) (Boundary.packet first input initial) =
      (RuntimeObservation.observe (P := target) (thetaRuntime cells) (Petri.lower graph)
        (encodeInput initial input)).map (consumerOutput first) := by
  unfold consumer Boundary.packet
  rw [wrap_observe]
  · rw [pull_under, pull_identity]
  · intro exit
    rfl

theorem third_observe (graph : Graph args) (first second : Word)
    (input : Tuple (Val cells) args) (initial : Heap cells) :
    RuntimeObservation.observe (P := target) (thetaRuntime cells) (third graph)
        (Boundary.packet second (.cons (t := .word) first input) initial) =
      (RuntimeObservation.observe (P := target) (thetaRuntime cells) (Petri.lower graph)
        (encodeInput initial input)).map (thirdOutput first second) := by
  unfold third Boundary.packet
  rw [wrap_observe]
  · rw [pull_under, pull_under, pull_identity]
  · intro exit
    rfl

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Wrapper.Proofs
