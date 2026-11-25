module

public import Silmaril.SSA.RVSDG.Institution.Defs
public import Silmaril.SSA.RVSDG.Categorical.Defs

/-! # Typed RVSDG equations in a Cartesian value category -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Institution

open CategoryTheory Silmaril.Logic.Institution

universe u v d h w
variable {V S : Type u} {P Q : Dialect.{u, v} V S}
variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D]

/-- The reduct preserves the chosen selector cocones and all port objects.
Each source primitive uses the arrow of its target image. -/
abbrev categoricalReduct (f : OpcodeMap P Q) (m : Categorical.Model Q D) :
    Categorical.Model P D where
  selectors := m.selectors
  value := m.value
  snapshot := m.snapshot
  primitive op := m.primitive (f op)

/-- An equation observes equality of the full result arrow, with its ordered
value, snapshot, and selector ports. -/
def Equation.HoldsCategorically (e : Equation P) (m : Categorical.Model P D) : Prop :=
  e.lhs.denote m = e.rhs.denote m

def categoricalReductFunctor (f : OpcodeMap P Q) :
    Discrete (Categorical.Model Q D) ⥤ Discrete (Categorical.Model P D) :=
  Discrete.functor fun m => Discrete.mk (categoricalReduct f m)

/-- View total runtime models as Cartesian models in the category of types. -/
def ofRuntimeFunctor (P : Dialect.{u, v} V S) :
    Discrete (Model.{u, v, w} P) ⥤ Discrete (Categorical.Model P (Type w)) :=
  Discrete.functor fun m => Discrete.mk (Categorical.Model.ofRuntime m)

/-- The room of typed equations and discrete models in a fixed Cartesian
value category. Each model supplies its own finite selector cocones. -/
def categoricalRoom (P : Signature.{u, v} V S) (D : Type d)
    [Category.{h} D] [CartesianMonoidalCategory D] :
    Room.{max u v, max u v d h, max u v d h} where
  Sen := Equation P.op
  Mod := Cat.of (Discrete (Categorical.Model P.op D))
  Sat m e := e.HoldsCategorically m.as

end Silmaril.SSA.RVSDG.Institution
