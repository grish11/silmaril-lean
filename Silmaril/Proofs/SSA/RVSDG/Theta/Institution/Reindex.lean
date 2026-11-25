module

public import Silmaril.SSA.RVSDG.Theta.Institution.Defs
public import Silmaril.SSA.RVSDG.Institution.Thms

public section

namespace Silmaril.SSA.RVSDG.Theta.Institution.Proofs

open RVSDG.Institution (OpcodeMap reduct mapGraph_id mapGraph_comp mapGraph_run)

universe u v w
variable {V S : Type u} {P Q R : Dialect.{u, v} V S}
variable {carried : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

set_option backward.isDefEq.respectTransparency false

private theorem steps_relabel (f : OpcodeMap P Q) (g : Graph P carried sigs)
    (m : Model.{u, v, w} Q) :
    (fun (input : Tuple m.Val carried) again (output : Tuple m.Val carried) =>
      (relabel f g).body.run m input = bodyResult m again output) =
    (fun input again output =>
      g.body.run (reduct f m) input = bodyResult (reduct f m) again output) := by
  funext input again output
  rw [relabel, mapGraph_run]
  rfl

theorem returns_relabel (f : OpcodeMap P Q) (g : Graph P carried sigs)
    (m : Model.{u, v, w} Q) (input output : Tuple m.Val carried) :
    (relabel f g).Returns m input output ↔ g.Returns (reduct f m) input output := by
  rw [Graph.Returns, Graph.Returns, steps_relabel]

theorem diverges_relabel (f : OpcodeMap P Q) (g : Graph P carried sigs)
    (m : Model.{u, v, w} Q) (input : Tuple m.Val carried) :
    (relabel f g).Diverges m input ↔ g.Diverges (reduct f m) input := by
  rw [Graph.Diverges, Graph.Diverges, steps_relabel]

theorem equation_map_id (e : Equation P) : e.map (fun f => f) = e := by
  rcases e with ⟨carried, ls, rs, ⟨left⟩, ⟨right⟩⟩
  simp only [Equation.map, relabel, mapGraph_id]

theorem equation_map_comp (f : OpcodeMap P Q) (g : OpcodeMap Q R) (e : Equation P) :
    e.map (fun op => g (f op)) = (e.map f).map g := by
  cases e
  simp only [Equation.map, relabel, mapGraph_comp]

theorem satisfaction (f : OpcodeMap P Q) (e : Equation P) (m : Model.{u, v, w} Q) :
    (e.map f).Holds m ↔ e.Holds (reduct f m) := by
  change (∀ input : Tuple m.Val e.carried,
    (∀ output, (relabel f e.lhs).Returns m input output ↔ (relabel f e.rhs).Returns m input output) ∧
      ((relabel f e.lhs).Diverges m input ↔ (relabel f e.rhs).Diverges m input)) ↔ _
  simp only [returns_relabel, diverges_relabel, Equation.Holds]
  rfl

end Silmaril.SSA.RVSDG.Theta.Institution.Proofs
