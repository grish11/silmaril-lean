module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Defs
public import Silmaril.SSA.Peggy.Worked.EvalScale.Defs

/-! # Combined zero-sample and eval-scale visits -/

@[expose] public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined

open PEG
open Worked

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {site : Fin n}

structure Ops (P : InstructionSet.{u,v} Data) where
  zero : P [] .count
  factor : P [] .count
  scale : P [.count, .count] .count

inductive Action where
  | zeroSample (address : Nat)
  | evalScale (address : Nat)
  deriving DecidableEq

variable [DecidableEq Data] [DecidableEq (P [] .count)] [DecidableEq (P [.count, .count] .count)]

/-- Check the actual inner binary row at the sampled address. -/
def checkProduct {ops : Ops P} (found : EvalScale.Match g site ops.factor ops.scale) :
    Node P params (Fin l) g.sort .count → Bool
  | ⟨_, .op (ins := [.count, .count]) op, .cons left (.cons right .nil)⟩ =>
    decide (op = ops.scale) && left.id == found.constant.id && right.id == found.stream.id
  | _ => false

/-- An exact RHS is an eval with the same loop and index operand,
sampling the exact binary row with the two ordered source operands. -/
def checkRhs {ops : Ops P} (found : EvalScale.Match g site ops.factor ops.scale) (rhs : Fin n) : Bool :=
  if sort : g.sort rhs = .count then
    match typedNode (⟨rhs, sort⟩ : Ref g.sort .count) with
    | ⟨_, .eval loop, .cons inner (.cons count .nil)⟩ =>
      (loop == found.loop) && (count.id == found.count.id) && checkProduct found (typedNode inner)
    | _ => false
  else false

def checkCovered {ops : Ops P} (found : EvalScale.Match g site ops.factor ops.scale)
    (classes : Classes n) : Bool :=
  (List.finRange n).any fun rhs => checkRhs found rhs && (classes site == classes rhs)

def scaleEnabled (ops : Ops P) (s : Output P params results l) (address : Nat) : Bool :=
  if bound : address < s.1 then
    match EvalScale.Match.atSite s.2.graph ⟨address, bound⟩ ops.factor ops.scale with
    | none => false
    | some found => !checkCovered found s.2.classes
  else false

/-- An uncovered visit runs the existing two-row append and merge plan.
If an exact RHS is already in the redex class, keep the current table. -/
def scaleVisit (ops : Ops P) (s : Output P params results l) (address : Nat) :
    Output P params results l :=
  if bound : address < s.1 then
    match EvalScale.Match.atSite s.2.graph ⟨address, bound⟩ ops.factor ops.scale with
    | none => s
    | some found => if checkCovered found s.2.classes then s else (found.plan (s := s.2)).run 2
  else s

def enabled (ops : Ops P) (s : Output P params results l) : Action → Bool
  | .zeroSample address => Dedup.Worklist.enabledAt ops.zero s address
  | .evalScale address => scaleEnabled ops s address

def visit (ops : Ops P) (s : Output P params results l) : Action → Output P params results l
  | .zeroSample address => Dedup.visit ops.zero s address
  | .evalScale address => scaleVisit ops s address

/-- Both rule tags are considered at every address of the current table. -/
def actions (n : Nat) : List Action :=
  (List.range n).map Action.zeroSample ++ (List.range n).map Action.evalScale

def driver (ops : Ops P) : Driver (Output P params results l) Action :=
  ⟨fun s => (actions s.1).find? (enabled ops s), enabled ops, visit ops⟩

/-- Neither included matcher finds an enabled action on this table. -/
def Fixed (ops : Ops P) (s : Output P params results l) : Prop :=
  ∀ action, enabled ops s action = false

end Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined
