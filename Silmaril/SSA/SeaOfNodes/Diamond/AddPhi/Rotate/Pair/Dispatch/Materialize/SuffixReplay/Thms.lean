module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay

open Pure.SubZero (model word)
open RVSDG (Tuple)

variable {inputs joined : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p target : Program inputs sigs joined} {requests : List (Request p)}

/-- The diamond, capture and native suffix result agree, including all live occurrence wires. -/
theorem rewrite_preserves (accepted : rewrite p requests = .ok target) :
    target.diamond = p.diamond ∧ target.residual = p.residual ∧
      ∀ entry : Tuple (Val model.value) (dataPorts (word :: joined)),
        target.suffix.eval model entry = p.suffix.eval model entry :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.rewrite_preserves accepted

theorem rewrite_returns_iff (accepted : rewrite p requests = .ok target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ p.Returns entry returned := by
  obtain ⟨diamond, capture, suffix⟩ := rewrite_preserves accepted
  simp only [Program.Returns, diamond, capture, suffix]

variable {g : AddPhi.Pair.Source inputs sigs} {x : InputWord inputs} {first column : Column} {value : BitVec 64}
variable {emitted final : Program inputs sigs [word]} {script : List (Request emitted)}

/-- Successful replay on the actual materialization preserves and reflects every original finite return. -/
theorem materialize_then_rewrite_returns_iff
    (emission : Materialize.rewrite g x first = .ok (.materialized column value emitted))
    (accepted : rewrite emitted script = .ok final)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    final.Returns entry returned ↔ (original g x).Returns entry returned :=
  (rewrite_returns_iff accepted entry returned).trans (Materialize.rewrite_returns_iff emission entry returned)

/-- Absence of a finite return is preserved and reflected as well. -/
theorem materialize_then_rewrite_no_return_iff
    (emission : Materialize.rewrite g x first = .ok (.materialized column value emitted))
    (accepted : rewrite emitted script = .ok final)
    (entry : Tuple (Val model.value) (dataPorts inputs)) :
    (¬ ∃ value, final.Returns entry value) ↔ ¬ ∃ value, (original g x).Returns entry value :=
  not_congr (exists_congr (materialize_then_rewrite_returns_iff emission accepted entry))

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay
