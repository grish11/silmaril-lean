module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery

open Pure.SubZero (model word)
open Pure.RightIdentityPass (wordProducers)
open GVN.Elimination (Routing)
open RVSDG (Tuple Wires)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p : Program inputs sigs [word]} {target : Program inputs sigs [word, word]}

/-- The chosen representative passes the existing check and all shared
word producers before it in table order fail that same check. -/
theorem findRepresentative?_eq_some_iff {rep : EntryAdd p} :
    findRepresentative? p = some rep ↔
      check p rep = true ∧ ∃ before after, wordProducers p.diamond.shared = before ++ rep :: after ∧
        ∀ prior ∈ before, check p prior = false := by
  simpa only [findRepresentative?, Bool.not_eq_true'] using
    (List.find?_eq_some_iff_append (p := check p) (xs := wordProducers p.diamond.shared) (b := rep))

/-- Exhaustive for all typed word producers in the shared table. -/
theorem findRepresentative?_eq_none_iff :
    findRepresentative? p = none ↔ ∀ rep : EntryAdd p, check p rep = false :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery.find_none_iff

/-- A successful discovery emits exactly the existing checked rewrite
for the first accepted representative. -/
theorem discoverAndRewrite?_eq_some_iff :
    discoverAndRewrite? p = some target ↔
      ∃ rep, findRepresentative? p = some rep ∧ rewrite? p rep = some target :=
  Option.bind_eq_some_iff

/-- A miss rules out every rewrite accepted by the nomination API,
including when the actual suffix is outside its profile. -/
theorem discoverAndRewrite?_eq_none_iff :
    discoverAndRewrite? p = none ↔ ∀ rep : EntryAdd p, rewrite? p rep = none :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery.rewrite_none_iff

/-- The discovered result has the shortened suffix and preserves each
complete routed packet at either actual predecessor occurrence. -/
theorem discoverAndRewrite?_packet_eq (accepted : discoverAndRewrite? p = some target) :
    ∃ value, p.suffix = suffix .right value ∧ target.suffix = shortened value ∧
      ∀ (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot)
        {ports : List (Ty Unit)} (packet : Wires OldArgs [Row, Row, Row] ports),
        let before := slotArgs p entry slot
        let after := slotArgs target entry slot
        (Routing.wires route packet).read after ((shortened value).dataflow.eval model after PUnit.unit) =
          packet.read before ((suffix .right value).dataflow.eval model before PUnit.unit) :=
  let ⟨_, _, rewritten⟩ := discoverAndRewrite?_eq_some_iff.mp accepted
  let ⟨value, shape, checked, emitted⟩ := rewrite?_eq_some_iff.mp rewritten
  ⟨value, shape, emitted.symm ▸
    ⟨rfl, fun entry slot {_} packet => emit_packet_eq checked value entry slot packet⟩⟩

/-- Successful discovery preserves finite returns from the materialized program. -/
theorem discoverAndRewrite?_returns_iff (accepted : discoverAndRewrite? p = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ p.Returns entry returned :=
  let ⟨_, _, rewritten⟩ := discoverAndRewrite?_eq_some_iff.mp accepted
  rewrite?_returns_iff rewritten entry returned

/-- Compose discovery with the actual materialization of the original diamond. -/
theorem materialize_then_discover_returns_iff {g : AddPhi.Pair.Source inputs sigs}
    {x : InputWord inputs} {first : Column} {value : BitVec 64}
    (emitted : Materialize.rewrite g x first = .ok (.materialized .right value p))
    (accepted : discoverAndRewrite? p = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ (original g x).Returns entry returned :=
  let ⟨_, _, rewritten⟩ := discoverAndRewrite?_eq_some_iff.mp accepted
  materialize_then_reuse_returns_iff emitted rewritten entry returned

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery
