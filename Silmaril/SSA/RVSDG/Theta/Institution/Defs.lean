module

public import Silmaril.SSA.RVSDG.Theta.Defs
public import Silmaril.SSA.RVSDG.Institution.Defs

/-! # Dialect equations between whole-region θ graphs -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Theta.Institution

open CategoryTheory Silmaril.Logic.Institution
open RVSDG.Institution (OpcodeMap Signature mapGraph)

universe u v w
variable {V S : Type u} {P Q : Dialect.{u, v} V S}
variable {carried : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

/-- Relabel the body in place, preserving its selector and feedback boundary. -/
def relabel (f : OpcodeMap P Q) (g : Graph P carried sigs) : Graph Q carried sigs :=
  ⟨mapGraph f g.body⟩

/-- The sides share their carried signature, with independent numbered bodies. -/
structure Equation (P : Dialect.{u, v} V S) where
  carried : Ports (PortType V S)
  leftSigs : List (Ports (PortType V S))
  rightSigs : List (Ports (PortType V S))
  lhs : Graph P carried leftSigs
  rhs : Graph P carried rightSigs

def Equation.map (f : OpcodeMap P Q) (e : Equation P) : Equation Q :=
  ⟨e.carried, e.leftSigs, e.rightSigs, relabel f e.lhs, relabel f e.rhs⟩

/-- Compare all returned tuples and the existence of an infinite sequence
of continuing body completions, at every input. -/
def Equation.Holds (e : Equation P) (m : Model.{u, v, w} P) : Prop :=
  ∀ input : Tuple m.Val e.carried,
    (∀ output, e.lhs.Returns m input output ↔ e.rhs.Returns m input output) ∧
      (e.lhs.Diverges m input ↔ e.rhs.Diverges m input)

def room (P : Signature.{u, v} V S) :
    Room.{max u v, max u v (w + 1), max u v (w + 1)} where
  Sen := Equation P.op
  Mod := Cat.of (Discrete (Model.{u, v, w} P.op))
  Sat m e := e.Holds m.as

end Silmaril.SSA.RVSDG.Theta.Institution
