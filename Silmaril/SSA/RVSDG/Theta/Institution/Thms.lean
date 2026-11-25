module

public import Silmaril.SSA.RVSDG.Theta.Institution.Defs
public import Silmaril.SSA.RVSDG.Institution.Thms
import Silmaril.Proofs.SSA.RVSDG.Theta.Institution.Reindex

/-! # Satisfaction under relabelling whole-region θ -/

public section

namespace Silmaril.SSA.RVSDG.Theta.Institution

open CategoryTheory Silmaril.Logic.Institution
open RVSDG.Institution (OpcodeMap reduct reductFunctor)

universe u v w
variable {V S : Type u} {P Q : Dialect.{u, v} V S}
variable {carried : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

set_option backward.isDefEq.respectTransparency false

/-- Relabelling preserves and reflects every finite return in the reduct. -/
theorem relabel_returns (f : OpcodeMap P Q) (g : Graph P carried sigs)
    (m : Model.{u, v, w} Q) (input output : Tuple m.Val carried) :
    (relabel f g).Returns m input output ↔ g.Returns (reduct f m) input output :=
  Proofs.returns_relabel f g m input output

/-- Relabelling preserves and reflects infinite continuation in the reduct. -/
theorem relabel_diverges (f : OpcodeMap P Q) (g : Graph P carried sigs)
    (m : Model.{u, v, w} Q) (input : Tuple m.Val carried) :
    (relabel f g).Diverges m input ↔ g.Diverges (reduct f m) input :=
  Proofs.diverges_relabel f g m input

theorem Equation.satisfaction (f : OpcodeMap P Q) (e : Equation P) (m : Model.{u, v, w} Q) :
    (e.map f).Holds m ↔ e.Holds (reduct f m) :=
  Proofs.satisfaction f e m

@[expose] def corridor {P Q : RVSDG.Institution.Signature.{u, v} V S} (f : P ⟶ Q) :
    room.{u, v, w} P ⟶ room.{u, v, w} Q :=
  let op : OpcodeMap P.op Q.op := RVSDG.Institution.Signature.opcodeMap f
  ⟨Equation.map op, reductFunctor op, fun m e =>
    Equation.satisfaction (P := P.op) (Q := Q.op) op e m.as⟩

theorem corridor_id (P : RVSDG.Institution.Signature.{u, v} V S) :
    corridor.{u, v, w} (𝟙 P) = 𝟙 (room.{u, v, w} P) :=
  Room.hom_ext (funext (Proofs.equation_map_id (P := P.op)))
    (congrArg (fun (c : RVSDG.Institution.room.{u, v, w} P ⟶ RVSDG.Institution.room P) => c.mod)
      (RVSDG.Institution.corridor_id P))

theorem corridor_comp {P Q R : RVSDG.Institution.Signature.{u, v} V S} (f : P ⟶ Q) (g : Q ⟶ R) :
    corridor.{u, v, w} (f ≫ g) = corridor f ≫ corridor g :=
  Room.hom_ext (funext (Proofs.equation_map_comp
    (RVSDG.Institution.Signature.opcodeMap f) (RVSDG.Institution.Signature.opcodeMap g)))
    (congrArg (fun (c : RVSDG.Institution.room.{u, v, w} P ⟶ RVSDG.Institution.room R) => c.mod)
      (RVSDG.Institution.corridor_comp f g))

/-- The deterministic equation institution for whole-region θ graphs. -/
@[expose] def inst (V S : Type u) :
    Inst.{max u (v + 1), max u v, max u v, max u v (w + 1), max u v (w + 1)} where
  Sign := RVSDG.Institution.Signature.{u, v} V S
  I :=
    { obj := room.{u, v, w}
      map := corridor.{u, v, w}
      map_id := corridor_id
      map_comp := corridor_comp }

end Silmaril.SSA.RVSDG.Theta.Institution
