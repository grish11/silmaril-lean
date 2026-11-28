module

public import Silmaril.SSA.RVSDG.Defs
import Silmaril.Proofs.SSA.RVSDG.ValueMap.Correctness

/-! # Transport acyclic RVSDG execution between models -/

public section

namespace Silmaril.SSA.RVSDG

universe u v w
variable {V S : Type u} {Op : Dialect.{u,v} V S}
variable {args outs : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

/-- A map preserving primitive evaluation and branch selectors commutes with graph execution. -/
theorem Graph.run_map {m n : Model.{u,v,w} Op} (g : Graph Op args [] sigs outs)
    (f : ∀ t, m.Val t → n.Val t)
    (run : ∀ {ins results} (op : Op ins results) (input : Tuple m.Val ins),
      (m.run op input).map f = n.run op (input.map f))
    (control : ∀ k (x : ULift (Fin k)), f (.control k) x = x)
    (entry : Tuple m.Val args) :
    (g.run m entry).map f = g.run n (entry.map f) :=
  Proofs.graph_run_map f run control g entry

end Silmaril.SSA.RVSDG
