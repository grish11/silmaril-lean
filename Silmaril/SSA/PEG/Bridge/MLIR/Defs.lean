module

public import Silmaril.SSA.PEG.Bridge.RVSDG.Defs
public import Silmaril.SSA.RVSDG.MLIR.Regionless.Defs

/-! # The regionless MLIR image of the PEG value fragment -/

@[expose] public section

namespace Silmaril.SSA.PEG.Bridge

open RVSDG (Tuple)
open Silmaril.MLIR.Institution (Signature Profile OpArity)
open Silmaril.SSA.RVSDG.MLIR

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {params results : List (Ty Data)} {n : Nat}

/-- One regionless symbol for each typed bridge operation. -/
inductive Symbol (P : InstructionSet.{0,0} Data) :
    {a : OpArity false} → Profile a (Ty Data) → Type
  | apply {ins out} (op : Operation P ins out) : Symbol P (Regionless.profile id ins [out])

def signature (P : InstructionSet.{0,0} Data) : Signature false :=
  ⟨Ty Data, Symbol P⟩

def profileMap (P : InstructionSet.{0,0} Data) :
    Regionless.ProfileMap (Opcode P) (signature P) :=
  ⟨id, fun | .apply op => .symbol (.apply op)⟩

def TotalModel.toMLIR (m : TotalModel P) : Silmaril.MLIR.Institution.Model (signature P) where
  carrier := m.toPEG.Value
  op
    | .apply (ins := ins) (out := out) op, input, _ =>
      let args := Regionless.ofAssignment (F := m.toRVSDG.Val) ins input
      Regionless.toAssignment (F := m.toRVSDG.Val) [out] (.cons (op.eval m (fromPorts ins args)) .nil)

def translateMLIR (g : Graph P params results n 0) (ordered : Ordered g) :
    Silmaril.MLIR.Institution.Block (signature P)
      (Regionless.context id params) (Regionless.context id results) :=
  Regionless.translateGraph (profileMap P) (translate g ordered).2

/-- Two PEGs in the admitted fragment at the same ordered boundary. -/
structure Equation (P : InstructionSet.{0,0} Data) where
  params : List (Ty Data)
  results : List (Ty Data)
  leftCount : Nat
  rightCount : Nat
  lhs : Graph P params results leftCount 0
  rhs : Graph P params results rightCount 0
  leftOrdered : Ordered lhs
  rightOrdered : Ordered rhs

/-- Equality of the full Figure 11 observation at every defined input. -/
def Equation.Holds (e : Equation P) (m : TotalModel P) : Prop :=
  ∀ (env : Tuple m.toPEG.Value e.params) (idx : Index 0),
    e.lhs.observe m.toPEG (e.lhs.denote m.toPEG env e.leftOrdered.demandWellFounded) idx =
    e.rhs.observe m.toPEG (e.rhs.denote m.toPEG env e.rightOrdered.demandWellFounded) idx

def Equation.toRVSDG (e : Equation P) : Regionless.ValueEquation (Opcode P) :=
  let l := translate e.lhs e.leftOrdered
  let r := translate e.rhs e.rightOrdered
  ⟨e.params, e.results, l.1, r.1, l.2, r.2⟩

def Equation.toMLIR (e : Equation P) : Silmaril.MLIR.Institution.Equation (signature P) :=
  Regionless.translateEquation (profileMap P) e.toRVSDG

end Silmaril.SSA.PEG.Bridge
