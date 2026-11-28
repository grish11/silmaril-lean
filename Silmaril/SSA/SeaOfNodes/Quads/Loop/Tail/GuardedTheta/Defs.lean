module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Defs

/-! Use an entry γ to bypass a post-tested θ when the first test is false. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.GuardedTheta

open SeaOfNodes.Diamond (Signature Ty ValueSort dataPorts)
open RVSDG (Port Wires)
open RVSDG.NestedTheta (Term)
open Join (Block Opcode)
open Join.Finite (lastBank)
open Tail.Diamond (bodyPorts latchNodeFor thenBase)

universe u v

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {sigs past : List (List (Ty Data))}

def armSigs (regs : List (ValueSort Data)) : Fin 2 → List (List (Ty Data)) :=
  Fin.cases [] (fun _ => [dataPorts regs])

/-- The false arm projects the current result. Only the true arm invokes θ. -/
def arm (result : Port (dataPorts regs) (.value out))
    (body : Term (Opcode Op) (dataPorts regs) [] sigs (bodyPorts regs)) (i : Fin 2) :
    Term (Opcode Op) (dataPorts regs) [] (armSigs regs i) [.value out] :=
  Fin.cases (motive := fun j => Term (Opcode Op) (dataPorts regs) [] (armSigs regs j) [.value out])
    (.ret (.cons (.arg result) .nil))
    (fun _ =>
      .bind ⟨_, .theta (dataPorts regs), initial regs, fun _ => sigs⟩
        (fun _ => body) (.ret (.cons ((lastBank [] (dataPorts regs)).get result) .nil))) i

def guard (test : Port (dataPorts regs) (.value .predicate)) (result : Port (dataPorts regs) (.value out))
    (body : Term (Opcode Op) (dataPorts regs) [] sigs (bodyPorts regs))
    (current : Wires (dataPorts regs) past (dataPorts regs)) :
    Term (Opcode Op) (dataPorts regs) past [bodyPorts regs, [.value out]] [.value out] :=
  .bind (.ofBase (latchNodeFor test current)) (fun i => i.elim0)
    (.bind ⟨_, .base (.gamma 0), lastBank past (bodyPorts regs), armSigs regs⟩
      (arm result body) (.ret (lastBank (past ++ [bodyPorts regs]) [.value out])))

def lowerTerm (entry : Block Op regs)
    (test : Port (dataPorts regs) (.value .predicate)) (result : Port (dataPorts regs) (.value out))
    (body : Term (Opcode Op) (dataPorts regs) [] sigs (bodyPorts regs)) :
    Term (Opcode Op) (dataPorts regs) [] (entry.producers ++ [bodyPorts regs, [.value out]]) [.value out] :=
  thenBase (entry.lowerFrom (initial regs) .jump) (guard test result body)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.GuardedTheta
