module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Silmaril.SSA.PEG.Figure19.Placement.Defs

/-! # Same-index must-demand in a PEG expression slice

One table entry is computed per row per round. Rows always demand
themselves. Primitive operands are strict, while φ demands its flag
and the intersection of the two arm sets. All other labels are
leaves of this analysis. In particular, it never follows a recurrence
or samples another iteration.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Figure19.MustEval

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}

abbrev Table (n : Nat) := Vector (Finset (Fin n)) n

/-- The analysis follows every same-index operand of a primitive or φ.
Other labels are leaves, regardless of their graph edges. -/
def follows {ins : List (Ty Data)} {out : Ty Data} :
    Label P params (Fin l) ins out → Bool
  | .op _ | .phi => true
  | _ => false

def Decreases {sort : Fin n → Ty Data} {out : Ty Data}
    (rank : Fin n → Nat) (i : Fin n) (row : Node P params (Fin l) sort out) : Prop :=
  follows row.label → ∀ slot : Fin row.inputs.length, rank (row.arg slot).id < rank i

def Ranked (g : Graph P params results n l) (rank : Fin n → Nat) : Prop :=
  ∀ i, Decreases rank i (g.node i)

def transfer (g : Graph P params results n l) (previous : Table n) (i : Fin n) : Finset (Fin n) :=
  insert i <| match g.node i with
  | ⟨ins, .op _, args⟩ =>
    Finset.univ.biUnion fun slot : Fin ins.length =>
      previous[(args.get (portAt ins slot)).id.val]
  | ⟨_, .phi, args⟩ =>
    previous[(args.get .head).id.val] ∪
      (previous[(args.get (.tail .head)).id.val] ∩
       previous[(args.get (.tail (.tail .head))).id.val])
  | _ => ∅

/-- All reads are from the previous round, including when several users
share the same child. The initial table contains only singleton sets. -/
def rounds (g : Graph P params results n l) : Nat → Table n
  | 0 => Vector.ofFn fun i => {i}
  | k + 1 =>
    let previous := rounds g k
    Vector.ofFn (transfer g previous)

/-- Use table-size fuel for the loop-local expression DAG. The semantic
soundness result also applies at any smaller round bound. -/
def analyze (g : Graph P params results n l) : Table n :=
  rounds g n

end Silmaril.SSA.PEG.Figure19.MustEval
