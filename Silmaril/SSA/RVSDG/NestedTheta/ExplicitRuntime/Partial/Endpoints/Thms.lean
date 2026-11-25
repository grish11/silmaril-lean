module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Transport
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial.Endpoints.Observations

/-! # Agreement of partial outcomes across explicit runtime erasure -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial

open OrderedRuntime.Structured
open OrderedState.Partial (Path runOpen)

universe u v w
variable {V : Type u} {P E : Dialect.{u,v} V PUnit.{u + 1}} {σ : Type (max u w)}
variable {args outs : Ports (Ty V)} {past sigs : List (Ports (Ty V))}
variable (m : Model.{u,v,w} P E σ)

/-- An admitted prefix has a finite wire derivation exactly when its erased
interpretation returns the same data and exact token. -/
theorem Checked.exec_iff {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)}
    (checked : ExplicitRuntime.Checked P E a b live t)
    (entry : Tuple (RuntimeValues m.value σ) (Threaded args))
    (locals : Locals (RuntimeValues m.value σ) past)
    (output : Tuple (RuntimeValues m.value σ) (Threaded outs)) :
    NestedTheta.Partial.exec (wireModel m) t entry locals output ↔
      boundaryResult output ∈ runOpen (erasedModel m) checked.erase (eraseTuple entry)
        (eraseLocals past locals) (readOrigin live entry locals) :=
  Proofs.exec_iff m checked entry locals output

/-- Erasure preserves and reflects an attempted primitive's diagnostic and
the existence of a productive run, beginning at the actual live token. -/
theorem Checked.abnormalAt_iff {a : Data args} {b : Data outs} {live : Origin (Threaded args) past runtime}
    {t : Term (Opcode P E) (Threaded args) past sigs (Threaded outs)}
    (checked : ExplicitRuntime.Checked P E a b live t)
    (entry : Tuple (RuntimeValues m.value σ) (Threaded args))
    (locals : Locals (RuntimeValues m.value σ) past) (path : Path) (obs : Observation m) :
    abnormalAt m path t entry locals obs ↔
      OrderedState.Partial.abnormalAt (erasedModel m) path checked.erase (eraseTuple entry)
        (eraseLocals past locals) (readOrigin live entry locals) obs :=
  Proofs.abnormalAt_iff m checked entry locals path obs

variable {a : Data args} {b : Data outs}
variable (g : Graph (Opcode P E) (Threaded args) [] sigs (Threaded outs))
variable (checked : EntryChecked (a := a) (b := b) g.toTerm)
variable (input : Tuple (RuntimeValues m.value σ) (Threaded args))

theorem returns_iff (output : Tuple (RuntimeValues m.value σ) (Threaded outs)) :
    NestedTheta.Partial.returns (wireModel m) g input output ↔
      boundaryResult output ∈ observeErased m g checked input :=
  Proofs.returns_iff m g checked input output

/-- Decode the runtime token from the established explicit graph denotation.
The resulting partial observation agrees on the entire returned boundary. -/
theorem observe_eq :
    Part.map boundaryResult (NestedTheta.Partial.observe (wireModel m) g input) =
      observeErased m g checked input :=
  Proofs.observe_eq m g checked input

/-- The graph and its erasure have the same block observations and the same
existence of productive divergence. Addresses retain the original numbering. -/
theorem abnormal_iff (obs : Observation m) :
    abnormal m g input obs ↔
      OrderedState.Partial.abnormal (erasedModel m) checked.erase.toGraph
        (boundaryResult input).1 (boundaryResult input).2 obs :=
  Proofs.abnormal_iff m g checked input obs

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Partial
