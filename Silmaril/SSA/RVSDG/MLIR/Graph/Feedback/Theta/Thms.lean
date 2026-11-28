module

public import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Theta.Defs
public import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Thms
import Silmaril.Proofs.SSA.RVSDG.MLIR.Graph.Feedback.Theta.Correctness

public section

namespace Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.WholeTheta

open NestedTheta.Institution
open OrderedRuntime.Structured (Data Values)

universe u v w
variable {V : Type u} {A : Stateless.Signature.{u,v} V}
variable {carried : Ports (PortSort V)} {sigs : List (Ports (PortSort V))}

theorem embed_noState (g : Theta.Graph A.pure carried sigs) (data : Data carried) :
    Stateless.NoState (embed g).toTerm :=
  Proofs.embed_noState g data

/-- Compile the whole-region θ through the existing scoped MLIR lowering. -/
@[expose] def lower (g : Theta.Graph A.pure carried sigs) (data : Data carried) :
    Region A carried carried :=
  Feedback.lower (embed g) (embed_noState g data)

/-- Finite returns agree on the entire ordered carry tuple. -/
theorem returns_lower_iff (m : Stateless.Model.{u,v,w} A) (g : Theta.Graph A.pure carried sigs)
    (data : Data carried) (input output : Tuple (Values m.value) carried) :
    (lower g data).Returns m input output ↔ g.Returns (runtime m) input output :=
  (Feedback.observe_eq_some_iff m (embed g) (embed_noState g data) input output).symm.trans
    (Proofs.embed_observe m g input output)

end Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.WholeTheta
