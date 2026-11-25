module

public import Silmaril.SSA.RVSDG.Defs
public import Silmaril.Logic.Institution.Morphism
public import Mathlib.CategoryTheory.Discrete.Basic

/-! # Typed RVSDG dialect equations

The value and state sort alphabets are fixed. A signature morphism sends each
opcode to an opcode with exactly the same ordered input and output ports.
Sentences are open equations between numbered graphs, with shared input and
result signatures and independent vertex signatures on the two sides.
-/

@[expose] public section

namespace Silmaril.SSA.RVSDG.Institution

open CategoryTheory Silmaril.Logic.Institution

universe u v w
variable {V S : Type u}

/-- An opcode map indexed by both ordered port signatures. -/
abbrev OpcodeMap (P Q : Dialect.{u, v} V S) :=
  ∀ {ins outs}, P ins outs → Q ins outs

/-- A dialect over fixed value and state sorts. -/
structure Signature (V S : Type u) where
  op : Dialect.{u, v} V S

structure Signature.Hom (P Q : Signature.{u, v} V S) where
  op : OpcodeMap P.op Q.op

instance : Category.{max u v} (Signature.{u, v} V S) where
  Hom := Signature.Hom
  id _ := ⟨fun f => f⟩
  comp h k := ⟨fun f => k.op (h.op f)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The indexed opcode map underlying a signature morphism. -/
def Signature.opcodeMap {P Q : Signature.{u, v} V S} (h : P ⟶ Q) : OpcodeMap P.op Q.op :=
  fun f => Signature.Hom.op (P := P) (Q := Q) h f

variable {P Q : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

/-- Relabel primitive nodes, preserving edges, branch order, and the entire
tree of typed region interfaces. -/
def mapTerm (h : OpcodeMap P Q) :
    {args outs : Ports (PortType V S)} → {past sigs : List (Ports (PortType V S))} →
    Term P args past sigs outs → Term Q args past sigs outs
  | _, _, _, _, .ret results => .ret results
  | _, _, _, _, .bind ⟨ins, .simple op, wires, childSigs⟩ _ rest =>
    .bind ⟨ins, .simple (h op), wires, childSigs⟩ (fun i => i.elim0) (mapTerm h rest)
  | _, _, _, _, .bind ⟨_, @Shape.gamma _ _ _ entry exit extra, wires, childSigs⟩ children rest =>
    .bind ⟨.control (extra + 2) :: entry, .gamma (exit := exit) extra, wires, childSigs⟩ (fun i => mapTerm h (children i)) (mapTerm h rest)

/-- Relabel the typed table through its exact, numbering-preserving linearization. -/
def mapGraph (h : OpcodeMap P Q) (g : Graph P args past sigs outs) :
    Graph Q args past sigs outs :=
  (mapTerm h g.toTerm).toGraph

/-- Restrict a target dialect model along an opcode map. State and value
carriers stay fixed and each source opcode uses its target interpretation. -/
def reduct (h : OpcodeMap P Q) (m : Model.{u, v, w} Q) : Model.{u, v, w} P where
  value := m.value
  state := m.state
  run op := m.run (h op)

/-- An equation at a common ordered input and output boundary. -/
structure Equation (P : Dialect.{u, v} V S) where
  args : Ports (PortType V S)
  outs : Ports (PortType V S)
  leftSigs : List (Ports (PortType V S))
  rightSigs : List (Ports (PortType V S))
  lhs : Graph P args [] leftSigs outs
  rhs : Graph P args [] rightSigs outs

def Equation.map (h : OpcodeMap P Q) (e : Equation P) : Equation Q :=
  ⟨e.args, e.outs, e.leftSigs, e.rightSigs, mapGraph h e.lhs, mapGraph h e.rhs⟩

/-- Satisfaction observes the entire returned tuple for every input,
including any state ports in the equation's result signature. -/
def Equation.Holds (e : Equation P) (m : Model.{u, v, w} P) : Prop :=
  ∀ input : Tuple m.Val e.args, e.lhs.run m input = e.rhs.run m input

def reductFunctor (h : OpcodeMap P Q) :
    Discrete (Model.{u, v, w} Q) ⥤ Discrete (Model.{u, v, w} P) :=
  Discrete.functor fun m => Discrete.mk (reduct h m)

/-- The room of typed equations and total deterministic dialect models. -/
def room (P : Signature.{u, v} V S) :
    Room.{max u v, max u v (w + 1), max u v (w + 1)} where
  Sen := Equation P.op
  Mod := Cat.of (Discrete (Model.{u, v, w} P.op))
  Sat m e := e.Holds m.as

end Silmaril.SSA.RVSDG.Institution
