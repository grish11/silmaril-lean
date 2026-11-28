module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.GuardedTheta.Defs

/-! Lower the checked header-tested source using an entry γ and a post-tested θ. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered

open SeaOfNodes.Diamond (Model Signature Ty ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open RVSDG (Tuple Wires)
open RVSDG.NestedTheta (Term Graph)
open Join (Block Opcode)
open Join.Finite (lastBank)
open Tail.Diamond (bodyPorts latchNodeFor thenBase)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}

/-- The preheader and first header execute before selecting the entry arm. -/
def entryBlock (p : Program Op regs out) : Block Op regs := p.preheader ++ p.header

abbrev Sigs (p : Program Op regs out) :=
  (entryBlock p).producers ++ [bodyPorts regs, [.value out]]

abbrev Target (p : Program Op regs out) :=
  Graph (Opcode Op) (dataPorts regs) [] (Sigs p) [.value out]

variable {m : Model.{u, v, w} Op} {p : Program Op regs out} [BankDecidableEq m.value (dataPorts regs)]
variable {facts : Tuple (Fact m.value) (dataPorts regs)}

/-- θ starts only from a continuing header. Each activation executes the
retained feedback block and then computes the next header bank and test. -/
def activation (checked : Checked m p facts) : Block Op regs :=
  (bypass checked 2).body ++ p.header

abbrev BodySigs (checked : Checked m p facts) :=
  (activation checked).producers ++ [bodyPorts regs]

def thetaBody (checked : Checked m p facts) :
    Term (Opcode Op) (dataPorts regs) [] (BodySigs checked) (bodyPorts regs) :=
  thenBase ((activation checked).lowerFrom (initial regs) .jump) fun current =>
    .bind (.ofBase (latchNodeFor p.again current)) (fun i => i.elim0)
      (.ret (lastBank _ (bodyPorts regs)))

/-- Arm zero reads the first header's result wire. Arm one starts θ with
the entire first header bank and reads the same port on its stopping bank. -/
def armSigs (regs : List (ValueSort Data)) : Fin 2 → List (List (Ty Data)) :=
  GuardedTheta.armSigs regs

def arm (checked : Checked m p facts) (i : Fin 2) :
    Term (Opcode Op) (dataPorts regs) [] (armSigs regs i) [.value out] :=
  GuardedTheta.arm p.result (thetaBody checked) i

def guard (checked : Checked m p facts) {past : List (List (Ty Data))}
    (current : Wires (dataPorts regs) past (dataPorts regs)) :
    Term (Opcode Op) (dataPorts regs) past [bodyPorts regs, [.value out]] [.value out] :=
  GuardedTheta.guard p.again p.result (thetaBody checked) current

def lowerTerm (checked : Checked m p facts) :
    Term (Opcode Op) (dataPorts regs) [] (Sigs p) [.value out] :=
  GuardedTheta.lowerTerm (entryBlock p) p.again p.result (thetaBody checked)

def lower (checked : Checked m p facts) : Target p := (lowerTerm checked).toGraph

/-- Reuse singleton-feedback admission and emit the numbered γ/θ graph. -/
def compile (m : Model.{u, v, w} Op) (p : Program Op regs out)
    [BankDecidableEq m.value (dataPorts regs)] (facts : Tuple (Fact m.value) (dataPorts regs)) :
    Option (Target p) :=
  (check m p facts).map lower

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered
