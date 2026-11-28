module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative

open Pure.SubZero (model word)
open GVN (keepOrigin)
open GVN.Elimination (Routing)
open RVSDG (Tuple Wires)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p : Program inputs sigs [word]} {rep : EntryAdd p} {target : Program inputs sigs [word, word]}

/-- On each actual occurrence the existing add key has exactly the capture
and the forwarded Phi wire, in one of the two orientations. -/
theorem check_provenance (checked : check p rep = true) (slot : Slot) :
    ∃ phi : SharedWord inputs sigs,
      (rep.key = addKey (.arg p.residual) phi ∨ rep.key = addKey phi (.arg p.residual)) ∧
      (p.diamond.arms slot).outputs.get .head = keepOrigin (p.diamond.arms slot).dataflow phi :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative.check_provenance
    checked slot

/-- Swapped operand keys preserve the wrapping sum through the typed GVN evaluation law. -/
theorem check_agrees (checked : check p rep = true) : RepresentativeAgrees p rep :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative.check_agrees checked

theorem findRepresentative?_checked (found : findRepresentative? p = some rep) : check p rep = true :=
  List.find?_some found

/-- A successful search uses the first admitted representative and the
existing emitter for exactly the right-materialized suffix. -/
theorem discoverAndRewrite?_eq_some_iff :
    discoverAndRewrite? p = some target ↔
      ∃ value rep, p.suffix = suffix .right value ∧
        findRepresentative? p = some rep ∧ target = emit p rep value :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative.discover_eq_some_iff

/-- The discovered result preserves each complete routed packet at either
actual predecessor occurrence, using the same route as ordered reuse. -/
theorem discoverAndRewrite?_packet_eq (accepted : discoverAndRewrite? p = some target) :
    ∃ value, p.suffix = suffix .right value ∧ target.suffix = shortened value ∧
      ∀ (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot)
        {ports : List (Ty Unit)} (packet : Wires OldArgs [Row, Row, Row] ports),
        let before := slotArgs p entry slot
        let after := slotArgs target entry slot
        (Routing.wires route packet).read after ((shortened value).dataflow.eval model after PUnit.unit) =
          packet.read before ((suffix .right value).dataflow.eval model before PUnit.unit) :=
  let ⟨value, _, shape, found, emitted⟩ := discoverAndRewrite?_eq_some_iff.mp accepted
  let agrees := check_agrees (findRepresentative?_checked found)
  ⟨value, shape, emitted.symm ▸ ⟨rfl, fun entry slot {_} packet => emit_packet_eq_of agrees value entry slot packet⟩⟩

theorem discoverAndRewrite?_returns_iff (accepted : discoverAndRewrite? p = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ p.Returns entry returned :=
  let ⟨_, _, shape, found, emitted⟩ := discoverAndRewrite?_eq_some_iff.mp accepted
  emitted.symm ▸ emit_returns_iff_of (check_agrees (findRepresentative?_checked found)) shape entry returned

/-- Compose the commutative reuse with actual materialization of the original two-Phi diamond. -/
theorem materialize_then_discover_returns_iff {g : AddPhi.Pair.Source inputs sigs}
    {x : InputWord inputs} {first : Column} {value : BitVec 64}
    (emitted : Materialize.rewrite g x first = .ok (.materialized .right value p))
    (accepted : discoverAndRewrite? p = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ (original g x).Returns entry returned :=
  (discoverAndRewrite?_returns_iff accepted entry returned).trans
    (Materialize.rewrite_returns_iff emitted entry returned)

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Commutative
