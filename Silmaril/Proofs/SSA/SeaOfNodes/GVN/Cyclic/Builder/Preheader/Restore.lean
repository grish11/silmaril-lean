module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Prepare

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader

open Silmaril.SSA.SeaOfNodes
open Diamond (Dataflow Ty Val ValueSort)
open GVN.Cyclic.Activation (Inputs)
open GVN.Cyclic.Builder.Preheader
open GVN.Cyclic.Deletion (DeletedLoop)
open Pure.SubZero (Opcode model)
open Silmaril.SSA.RVSDG (Locals Origin Port Tuple Wires)
open Loop (appendTuple headerPorts)

variable {inputs carried added : List (ValueSort Unit)} {entrySigs headerSigs past : List (List (Ty Unit))}
variable {out : ValueSort Unit}
variable {loop : Native inputs carried entrySigs headerSigs out}
variable {edited : DeletedLoop Opcode (carried ++ inputs) carried [] out}
variable {result : DeletedLoop Opcode inputs carried entrySigs out}

private theorem lifted_of_dropped {t : Ty Unit}
    {port : Port (headerPorts (added ++ inputs) carried) t} {kept : Port (headerPorts inputs carried) t}
    (dropped : dropHeaderPort? added port = some kept) :
    liftHeaderPort added kept = port := by
  induction added with
  | nil => exact (Option.some.inj dropped).symm
  | cons _ _ ih =>
    cases port with
    | head => cases dropped
    | tail inner => exact congrArg Port.tail (ih dropped)

private theorem strip_wire_read (caps : Inputs model added) (input : Inputs model inputs) (old : Inputs model carried)
    (locals : Locals (Val model.value) past) {t : Ty Unit}
    {wire : Origin (headerPorts (added ++ inputs) carried) past t}
    {mapped : Origin (headerPorts inputs carried) past t}
    (accepted : stripWire? added wire = some mapped) :
    Diamond.read model mapped (appendTuple old input) locals =
      Diamond.read model wire (appendTuple old (prependValues caps input)) locals := by
  cases wire with
  | output i port =>
    have same : Origin.output i port = mapped := Option.some.inj accepted
    cases same
    rfl
  | arg port =>
    cases dropped : dropHeaderPort? added port with
    | none => simp [stripWire?, dropped] at accepted
    | some kept =>
      have same : Origin.arg kept = mapped := by simpa [stripWire?, dropped] using accepted
      cases same
      change (appendTuple old input).get kept = (appendTuple old (prependValues caps input)).get port
      rw [← lifted_of_dropped dropped]
      exact (lift_read caps input old kept).symm

private theorem strip_wires_read (caps : Inputs model added) (input : Inputs model inputs) (old : Inputs model carried)
    (locals : Locals (Val model.value) past) {ports : List (Ty Unit)}
    {wires : Wires (headerPorts (added ++ inputs) carried) past ports}
    {mapped : Wires (headerPorts inputs carried) past ports}
    (accepted : stripWires? added wires = some mapped) :
    mapped.read (appendTuple old input) locals =
      wires.read (appendTuple old (prependValues caps input)) locals := by
  induction wires with
  | nil => cases mapped; rfl
  | cons wire tail ih =>
    obtain ⟨head, routedHead, next⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨rest, routedTail, eq⟩ := Option.bind_eq_some_iff.mp next
    have same := Option.some.inj eq
    subst mapped
    exact congrArg₂ Tuple.cons (strip_wire_read caps input old locals routedHead) (ih routedTail)

private theorem strip_flow_eval (caps : Inputs model added) (input : Inputs model inputs) (old : Inputs model carried)
    (locals : Locals (Val model.value) past)
    {flow : Dataflow Opcode (headerPorts (added ++ inputs) carried) past headerSigs}
    {mapped : Dataflow Opcode (headerPorts inputs carried) past headerSigs}
    (accepted : stripFlow? added flow = some mapped) :
    mapped.eval model (appendTuple old input) locals =
      flow.eval model (appendTuple old (prependValues caps input)) locals := by
  induction flow with
  | nil =>
    have same := Option.some.inj accepted
    subst mapped
    rfl
  | cons op wires rest ih =>
    obtain ⟨mappedWires, routed, next⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨mappedTail, routedTail, eq⟩ := Option.bind_eq_some_iff.mp next
    have same := Option.some.inj eq
    subst mapped
    simp only [Dataflow.eval]
    rw [strip_wires_read caps input old locals routed]
    exact ih _ routedTail

theorem restore_entry (accepted : restore? loop edited = some result) :
    result.graph.preheader = loop.preheader ∧ result.graph.phiInputs .entry = loop.phiInputs .entry ∧
      result.headerSigs = edited.headerSigs := by
  obtain ⟨_, _, next⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨_, _, eq⟩ := Option.bind_eq_some_iff.mp next
  have same := Option.some.inj eq
  subst result
  exact ⟨rfl, rfl, rfl⟩

theorem restore_packet (accepted : restore? loop edited = some result)
    (input : Inputs model inputs) (old : Inputs model carried) :
    let args := appendTuple old input
    let expanded := appendTuple old (preparedInput loop input)
    (observations result.graph).read args (result.graph.header.eval model args PUnit.unit) =
      (observations edited.graph).read expanded (edited.graph.header.eval model expanded PUnit.unit) := by
  obtain ⟨body, routedBody, next⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨packet, routedPacket, eq⟩ := Option.bind_eq_some_iff.mp next
  have same := Option.some.inj eq
  subst result
  let args := appendTuple old input
  let expanded := appendTuple old (preparedInput loop input)
  have packed := observations_eq packet
  change _ = packet at packed
  change Wires.read (Tuple.cons (packet.get .head) (.cons (packet.get (.tail .head)) (observationTail packet))) args
    (body.eval model args PUnit.unit) =
      (observations edited.graph).read expanded (edited.graph.header.eval model expanded PUnit.unit)
  have sameBody := strip_flow_eval (past := []) (loop.initial model input) input old PUnit.unit routedBody
  change body.eval model args PUnit.unit = edited.graph.header.eval model expanded PUnit.unit at sameBody
  rw [packed, sameBody]
  exact strip_wires_read (loop.initial model input) input old _ routedPacket

theorem restore_step (accepted : restore? loop edited = some result)
    (input : Inputs model inputs) (old : Inputs model carried) :
    result.graph.step model input old = edited.graph.step model (preparedInput loop input) old :=
  (step_packet _ _ _).trans ((congrArg packetOutcome (restore_packet accepted input old)).trans (step_packet _ _ _).symm)

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader
