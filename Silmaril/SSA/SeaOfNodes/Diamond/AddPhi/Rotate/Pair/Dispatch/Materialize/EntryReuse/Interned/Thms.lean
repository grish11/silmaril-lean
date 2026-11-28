module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned.Defs
public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.ValueNumbers.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned

open Pure.SubZero (model word wordPort)
open GVN.Elimination (Routing)
open GVN.WordNumber.Intern (Decodes readId)
open RVSDG (Port Tuple Wires)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p : Program inputs sigs [word]} {target : Program inputs sigs [word, word]}

/-- Every compared ID decodes in the final common table at its original cut. -/
theorem cuts_agree (p : Program inputs sigs [word]) :
    let cuts := numberCuts p
    cuts.table.Nodup ∧
      (∀ port : Port (dataPorts inputs) wordPort, Decodes cuts.table (cuts.entry.get port) (.argument port)) ∧
      (∀ wire : SharedWord inputs sigs, Decodes cuts.table (readId cuts.entry cuts.shared wire)
        (ValueNumbers.operandKey (ValueNumbers.sharedKeys p) wire)) ∧
      ∀ slot, Decodes cuts.table (cuts.phi slot) (ValueNumbers.phiKey p (ValueNumbers.sharedKeys p) slot) :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned.cuts_agree p

/-- ID comparisons and the existing recursive key comparisons make the same decision. -/
theorem check_eq_structural (p : Program inputs sigs [word]) (rep : EntryAdd p) :
    check p rep = ValueNumbers.check p rep :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned.check_eq_structural p rep

/-- Discovery selects the same representative and emits the same program. -/
theorem discoverAndRewrite?_eq_structural (p : Program inputs sigs [word]) :
    discoverAndRewrite? p = ValueNumbers.discoverAndRewrite? p := by
  unfold discoverAndRewrite? ValueNumbers.discoverAndRewrite? findRepresentative? ValueNumbers.findRepresentative?
  rw [show check p = ValueNumbers.check p from funext (check_eq_structural p)]

/-- Preserve arbitrary complete routed packets through the actual shared emitter. -/
theorem discoverAndRewrite?_packet_eq (accepted : discoverAndRewrite? p = some target) :
    ∃ value, p.suffix = suffix .right value ∧ target.suffix = shortened value ∧
      ∀ (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot)
        {ports : List (Ty Unit)} (packet : Wires OldArgs [Row, Row, Row] ports),
        let before := slotArgs p entry slot
        let after := slotArgs target entry slot
        (Routing.wires route packet).read after ((shortened value).dataflow.eval model after PUnit.unit) =
          packet.read before ((suffix .right value).dataflow.eval model before PUnit.unit) :=
  ValueNumbers.discoverAndRewrite?_packet_eq ((discoverAndRewrite?_eq_structural p).symm.trans accepted)

theorem discoverAndRewrite?_returns_iff (accepted : discoverAndRewrite? p = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ p.Returns entry returned :=
  ValueNumbers.discoverAndRewrite?_returns_iff ((discoverAndRewrite?_eq_structural p).symm.trans accepted) entry returned

theorem materialize_then_discover_returns_iff {g : AddPhi.Pair.Source inputs sigs}
    {x : InputWord inputs} {first : Column} {value : BitVec 64}
    (emitted : Materialize.rewrite g x first = .ok (.materialized .right value p))
    (accepted : discoverAndRewrite? p = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ (original g x).Returns entry returned :=
  ValueNumbers.materialize_then_discover_returns_iff emitted
    ((discoverAndRewrite?_eq_structural p).symm.trans accepted) entry returned

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Interned
