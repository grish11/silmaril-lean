module

public import Silmaril.SSA.PEG.Figure19.Defs

@[expose] public section

namespace Silmaril.SSA.PEG.Figure19

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}

/-- Same-index demand through ordered operands of strict primitives only.
A path can end at a θ or φ, but cannot go through it. -/
inductive StrictPath (g : Graph P params results n l) (target : Fin n) : Fin n → Prop where
  | here : StrictPath g target target
  | operand {i ins} {instr : P ins (g.sort i)} (args : RVSDG.Tuple (Ref g.sort) ins)
      (row : g.node i = .ofLabel (.op instr) args) (slot : Fin ins.length)
      (rest : StrictPath g target (args.get (portAt ins slot)).id) : StrictPath g target i

structure PathWitness (g : Graph P params results n l) (target start : Fin n) : Type where
  path : StrictPath g target start

/-- Find a strict operand path. Fuel counts operand edges. -/
def StrictPath.check (g : Graph P params results n l) (target : Fin n) :
    Nat → (start : Fin n) → Option (PathWitness g target start)
  | fuel, start =>
    if same : start = target then some ⟨same ▸ .here⟩
    else match fuel with
      | 0 => none
      | fuel + 1 =>
        match row : g.node start with
        | ⟨ins, .op _, args⟩ =>
          (List.finRange ins.length).findSome? fun slot =>
            (check g target fuel (args.get (portAt ins slot)).id).map fun tail =>
              ⟨.operand args row slot tail.path⟩
        | _ => none
termination_by structural fuel _ => fuel

end Silmaril.SSA.PEG.Figure19
