module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Thms
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers

open Pure.SubZero (model word)
open GVN.Elimination (Routing)
open RVSDG (Tuple Wires)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p : Program inputs sigs [word]} {rep : EntryAdd p} {target : Program inputs sigs [word, word]}

/-- At each actual occurrence, the representative key's operands pair with
the typed capture and the incoming Phi by exact structural number. -/
theorem check_pairing (checked : check p rep = true) (slot : Slot) :
    ∃ lhs rhs, rep.key = addKey lhs rhs ∧
      operandKey (sharedKeys p) lhs = .argument p.residual ∧
      operandKey (sharedKeys p) rhs = phiKey p (sharedKeys p) slot :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.check_pairing
    checked slot

/-- The symbolic key at an actual occurrence interprets to its selected Phi value. -/
theorem phiKey_eval (p : Program inputs sigs [word])
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    (phiKey p (sharedKeys p) slot).eval entry =
      ((p.diamond.arms slot).eval model entry (p.diamond.shared.eval model entry PUnit.unit)).get .head :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.phiKey_eval
    p entry slot

/-- The accepted entry producer computes the old inner sum for every input
at either predecessor occurrence. -/
theorem check_agrees (checked : check p rep = true) : RepresentativeAgrees p rep :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.check_agrees
    checked

theorem findRepresentative?_checked (found : findRepresentative? p = some rep) : check p rep = true :=
  List.find?_some found

/-- Successful discovery uses the existing typed emitter on the admitted suffix. -/
theorem discoverAndRewrite?_eq_some_iff :
    discoverAndRewrite? p = some target ↔
      ∃ value rep, p.suffix = suffix .right value ∧
        findRepresentative? p = some rep ∧ target = emit p rep value :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.discover_eq_some_iff

/-- The emitted suffix preserves every complete routed packet on both occurrences. -/
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

/-- Compose value-number discovery with actual materialization of the original two-Phi program. -/
theorem materialize_then_discover_returns_iff {g : AddPhi.Pair.Source inputs sigs}
    {x : InputWord inputs} {first : Column} {value : BitVec 64}
    (emitted : Materialize.rewrite g x first = .ok (.materialized .right value p))
    (accepted : discoverAndRewrite? p = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ (original g x).Returns entry returned :=
  (discoverAndRewrite?_returns_iff accepted entry returned).trans
    (Materialize.rewrite_returns_iff emitted entry returned)

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers
