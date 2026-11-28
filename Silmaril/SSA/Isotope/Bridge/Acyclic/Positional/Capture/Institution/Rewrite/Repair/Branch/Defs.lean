module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Defs

/-! # Two-constructor inputs with independent ordered effect arms -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Branch

open Sequence (Body Sorts Normal signature)
open LambdaSSA.Acyclic (Operand)
open LambdaSSA.Region (packedExitType)
open LambdaSSA.Acyclic.Positional.Capture.Reverse (Edge Program)

abbrev Input : Sorts := .coprod .unit .unit

def inputContext : BoundCtx Sorts 1 := .snoc .nil Input

/-- An arm is a sequence or a literal constructor test between two sequences.
The latter admits different written dead branches as well as different
spellings of empty elimination. -/
inductive Arm where
  | body (seq : Body)
  | known (right : Bool) (leftArm rightArm : Body)

def Arm.selected : Arm → Body
  | .body p | .known false p _ | .known true _ p => p

def Arm.operand {n : Nat} (β : BoundCtx Sorts n) : Arm → Operand signature.Instr β Ty.unit
  | .body p => p.operand β
  | .known tag l r =>
    let lit : Operand signature.Instr β Input :=
      if tag then ⟨.inr .unit, .inr .unit⟩ else ⟨.inl .unit, .inl .unit⟩
    let lhs := l.operand (β.snoc Ty.unit)
    let rhs := r.operand (β.snoc Ty.unit)
    ⟨.case lit.1 lhs.1 rhs.1, .case lit.2 lhs.2 rhs.2⟩

structure ProgramBody where
  left : Arm
  right : Arm

/-- Keep the two input tags ordered. Swapping their traces generally
changes this normal form, even with a common output position. -/
def ProgramBody.normal (p : ProgramBody) : Normal × Normal :=
  (p.left.selected.normal, p.right.selected.normal)

def Arm.edge (tail : List Sorts) (a : Arm) : Edge signature.Instr inputContext (Ty.unit :: tail) Ty.unit :=
  .local (.jump (a.operand (inputContext.snoc Ty.unit)) (.exit (i := 0) rfl))

/-- The captured control tree tests the actual input tag. Each arm runs its
own operand and passes a successful unit value to the first outward exit. -/
def ProgramBody.program (tail : List Sorts) (p : ProgramBody) :
    Program signature.Instr inputContext (Ty.unit :: tail) :=
  ⟨Input, ⟨.bv 0, .bv⟩, .case ⟨.bv 0, .bv⟩ (p.left.edge tail) (p.right.edge tail)⟩

def equation (tail : List Sorts) (p q : ProgramBody) : GrammarEquation signature :=
  ⟨⟨1, inputContext, Ty.unit :: tail⟩, p.program tail, q.program tail⟩

/-- The scoped arm followed by the exact tag for outward position zero. -/
def Arm.packed (tail : List Sorts) {n : Nat} (β : BoundCtx Sorts n) (a : Arm) :
    Operand signature.Instr β (packedExitType (Ty.unit :: tail)) :=
  let op := a.operand β
  ⟨.let₁ op.1 (.inl (.bv 0)), .let₁ op.2 (.inl .bv)⟩

abbrev branchContext := (inputContext.snoc Input).snoc Ty.unit

/-- Explicit typing of the shape emitted by the captured grammar. -/
def ProgramBody.rendered (tail : List Sorts) (p : ProgramBody) :
    Operand signature.Instr inputContext (packedExitType (Ty.unit :: tail)) :=
  let l := p.left.packed tail branchContext
  let r := p.right.packed tail branchContext
  ⟨.let₁ (.bv 0) (.case (.bv 0) l.1 r.1), .let₁ .bv (.case .bv l.2 r.2)⟩

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Branch
