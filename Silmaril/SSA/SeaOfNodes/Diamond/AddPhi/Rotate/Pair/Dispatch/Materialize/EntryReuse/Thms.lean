module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Defs
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse

open Pure.SubZero (model word)
open GVN (keepOrigin)
open GVN.Elimination (Routing)
open RVSDG (Tuple Wires)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p : Program inputs sigs [word]} {rep : EntryAdd p} {target : Program inputs sigs [word, word]}

theorem findEntry?_exact {address : RVSDG.Address} (found : findEntry? p address = some rep) :
    rep.origin.address = address :=
  of_decide_eq_true (List.find?_some (p := fun node : EntryAdd p => decide (node.origin.address = address)) found)

/-- Address resolution can only nominate a producer from the shared table. -/
theorem rewriteAt?_eq_some_iff {address : RVSDG.Address} :
    rewriteAt? p address = some target ↔
      ∃ rep, findEntry? p address = some rep ∧ rewrite? p rep = some target :=
  Option.bind_eq_some_iff

/-- An ordered check gives the exact capture and incoming Phi wire. -/
theorem matchesAt_exact {lhs rhs : SharedWord inputs sigs} {slot : Slot}
    (checked : matchesAt p lhs rhs slot = true) :
    lhs = .arg p.residual ∧
      (p.diamond.arms slot).outputs.get .head = keepOrigin (p.diamond.arms slot).dataflow rhs :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.matchesAt_exact checked

/-- An incoming Phi operand from the entry reads that entry value. -/
theorem read_forwarded {rhs : SharedWord inputs sigs}
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot)
    (forwarded : (p.diamond.arms slot).outputs.get .head = keepOrigin (p.diamond.arms slot).dataflow rhs) :
    let shared := p.diamond.shared.eval model entry PUnit.unit
    ((p.diamond.arms slot).eval model entry shared).get .head = read model rhs entry shared :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.read_forwarded entry slot forwarded

/-- The exact ordered entry key is linked to both original predecessor wires. -/
theorem check_provenance (accepted : check p rep = true) :
    ∃ rhs : SharedWord inputs sigs, rep.key = addKey (.arg p.residual) rhs ∧
      ∀ slot : Slot, ((p.diamond.arms slot).outputs.get .head) =
        keepOrigin (p.diamond.arms slot).dataflow rhs :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.check_provenance accepted

/-- The old inner sum reads the added boundary value, the old Phi is
still available, and the surviving outer result shifts down one slot. -/
theorem route_exact :
    route (.output (1 : Fin 3) .head) = .arg (.tail .head) ∧
      route (.arg (.tail .head)) = .arg (.tail (.tail .head)) ∧
      route (.output (2 : Fin 3) .head) = .output (1 : Fin 2) .head :=
  ⟨rfl, rfl, rfl⟩

/-- Complete admission and exact emitted graph for the nominated shape. -/
theorem rewrite?_eq_some_iff :
    rewrite? p rep = some target ↔
      ∃ value, p.suffix = suffix .right value ∧ check p rep = true ∧ target = emit p rep value :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.rewrite?_eq_some_iff

/-- All original reads survive along the typed route in each actual occurrence. -/
theorem emit_agrees (certified : check p rep = true) (value : BitVec 64)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    let before := slotArgs p entry slot
    let after := slotArgs (emit p rep value) entry slot
    route.AgreesBetween model before after
      ((suffix .right value).dataflow.eval model before PUnit.unit)
      ((shortened value).dataflow.eval model after PUnit.unit) :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.emit_agrees_of
    (Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.check_agrees certified) value entry slot

/-- Every routed read of a complete packet is preserved by an agreeing representative. -/
theorem emit_packet_eq_of {ports : List (Ty Unit)} (agrees : RepresentativeAgrees p rep) (value : BitVec 64)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot)
    (packet : Wires OldArgs [Row, Row, Row] ports) :
    let before := slotArgs p entry slot
    let after := slotArgs (emit p rep value) entry slot
    (Routing.wires route packet).read after ((shortened value).dataflow.eval model after PUnit.unit) =
      packet.read before ((suffix .right value).dataflow.eval model before PUnit.unit) :=
  (Routing.wires_read_between model _ _ _ _
    (Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.emit_agrees_of
      agrees value entry slot) packet).symm

/-- Preserve an entire ordered outgoing packet, including any additional
uses of the elided add or of the original Phi argument. -/
theorem emit_packet_eq {ports : List (Ty Unit)} (certified : check p rep = true) (value : BitVec 64)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot)
    (packet : Wires OldArgs [Row, Row, Row] ports) :
    let before := slotArgs p entry slot
    let after := slotArgs (emit p rep value) entry slot
    (Routing.wires route packet).read after ((shortened value).dataflow.eval model after PUnit.unit) =
      packet.read before ((suffix .right value).dataflow.eval model before PUnit.unit) :=
  emit_packet_eq_of
    (Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.check_agrees certified)
    value entry slot packet

theorem rewrite?_slot_eq (accepted : rewrite? p rep = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    target.atSlot entry slot = p.atSlot entry slot :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.rewrite?_slot_eq accepted entry slot

/-- The same emitter preserves finite returns for any agreeing representative of this suffix. -/
theorem emit_returns_iff_of (agrees : RepresentativeAgrees p rep) {value : BitVec 64}
    (shape : p.suffix = suffix .right value)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    (emit p rep value).Returns entry returned ↔ p.Returns entry returned :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.emit_returns_iff_of
    agrees shape entry returned

theorem rewrite?_returns_iff (accepted : rewrite? p rep = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ p.Returns entry returned :=
  let ⟨_, shape, checked, emitted⟩ := rewrite?_eq_some_iff.mp accepted
  emitted.symm ▸ emit_returns_iff_of
    (Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.check_agrees checked)
    shape entry returned

/-- Compose actual materialization and checked entry reuse for every typed input. -/
theorem materialize_then_reuse_returns_iff {g : AddPhi.Pair.Source inputs sigs}
    {x : InputWord inputs} {first : Column} {value : BitVec 64}
    (emitted : Materialize.rewrite g x first = .ok (.materialized .right value p))
    (accepted : rewrite? p rep = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ (original g x).Returns entry returned :=
  (rewrite?_returns_iff accepted entry returned).trans (Materialize.rewrite_returns_iff emitted entry returned)

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse
