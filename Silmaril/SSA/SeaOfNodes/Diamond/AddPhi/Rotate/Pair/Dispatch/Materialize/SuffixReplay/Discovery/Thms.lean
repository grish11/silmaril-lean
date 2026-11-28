module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Thms
import Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery

open Pure.SubZero (model word)
open RVSDG (Tuple)

variable {inputs joined : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}

/-- Exact occurrence wires, arm scopes, original Region order and capture. -/
theorem normalize_retains (p : Program inputs sigs joined) :
    (normalize p).diamond = p.diamond ∧ (normalize p).residual = p.residual := ⟨rfl, rfl⟩

/-- Discovery preserves and reflects the emitted program's finite returns. -/
theorem normalize_returns_iff (p : Program inputs sigs joined)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    (normalize p).Returns entry returned ↔ p.Returns entry returned := by
  have same : ∀ args, (normalize p).suffix.eval model args = p.suffix.eval model args :=
    Pure.SuffixReplay.Discovery.normalize_eval_eq (blockOf p)
  simp only [Program.Returns, (normalize_retains p).1, (normalize_retains p).2, same]

variable {g : AddPhi.Pair.Source inputs sigs} {x : InputWord inputs} {first column : Column} {value : BitVec 64}
variable {emitted : Program inputs sigs [word]}

/-- Running discovery after actual materialization preserves and reflects every original finite return. -/
theorem materialize_then_normalize_returns_iff
    (emission : Materialize.rewrite g x first = .ok (.materialized column value emitted))
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    (normalize emitted).Returns entry returned ↔ (original g x).Returns entry returned :=
  (normalize_returns_iff emitted entry returned).trans (Materialize.rewrite_returns_iff emission entry returned)

/-- The original and final graph also agree on absence of any finite return. -/
theorem materialize_then_normalize_no_return_iff
    (emission : Materialize.rewrite g x first = .ok (.materialized column value emitted))
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (¬ ∃ value, (normalize emitted).Returns entry value) ↔ ¬ ∃ value, (original g x).Returns entry value :=
  not_congr (exists_congr (materialize_then_normalize_returns_iff emission entry))

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery
