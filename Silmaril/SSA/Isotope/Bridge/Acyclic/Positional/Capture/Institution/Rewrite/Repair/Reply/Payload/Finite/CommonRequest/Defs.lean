module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Finite.Defs

/-! # Common requests under a test of a retained bit -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest

open Isotope.LetCase.LocallyNameless (Derivation)
open Kleisli (value)
open LambdaSSA (At)
open LambdaSSA.Acyclic (Operand)
open LambdaSSA.Acyclic.Positional.Capture.Reverse (Program)
open LambdaSSA.Region (packedExitType)
open LetIter.Semantics.Categorical (boundEnv boundObj)

local notation "U" => (Ty.unit : Sorts)

/-- Each continuation retains the untested bits and binds the new reply bit.
The test slot is fixed by the equation interface. -/
structure Arms (L : List Sorts) (n : Nat) where
  falseLeft : Tree L (n + 1)
  falseRight : Tree L (n + 1)
  trueLeft : Tree L (n + 1)
  trueRight : Tree L (n + 1)

structure NormalArms (L : List Sorts) (n : Nat) where
  falseLeft : Normal L (n + 1)
  falseRight : Normal L (n + 1)
  trueLeft : Normal L (n + 1)
  trueRight : Normal L (n + 1)

def Arms.normal {L : List Sorts} {n : Nat} (arms : Arms L n) : NormalArms L n :=
  ⟨arms.falseLeft.normal, arms.falseRight.normal, arms.trueLeft.normal, arms.trueRight.normal⟩

def NormalArms.render {L : List Sorts} {n : Nat} (arms : NormalArms L n) : Arms L n :=
  ⟨arms.falseLeft.render, arms.falseRight.render, arms.trueLeft.render, arms.trueRight.render⟩

structure Source (L : List Sorts) (n : Nat) where
  request : Bool
  factored : Bool
  arms : Arms L n

structure NormalSource (L : List Sorts) (n : Nat) where
  request : Bool
  arms : NormalArms L n

def Source.normal {L : List Sorts} {n : Nat} (p : Source L n) : NormalSource L n :=
  ⟨p.request, p.arms.normal⟩

def NormalSource.render {L : List Sorts} {n : Nat} (p : NormalSource L n) : Source L n :=
  ⟨p.request, false, p.arms.render⟩

def bitCase {k : Nat} {β : BoundCtx Sorts k} {A : Sorts}
    (d : Operand signature.Instr β Bit) (l r : Operand signature.Instr (β.snoc U) A) :
    Operand signature.Instr β A :=
  ⟨.case d.1 l.1 r.1, .case d.2 l.2 r.2⟩

def answerCase {k : Nat} {β : BoundCtx Sorts k} {A : Sorts}
    (l r : Operand signature.Instr (β.snoc Bit) A) : Operand signature.Instr (β.snoc Answer) A :=
  ⟨.case (.bv 0) l.1.underBinder r.1.underBinder, .case .bv l.2.underBinder r.2.underBinder⟩

def Source.operand {L : List Sorts} {n k : Nat} {β : BoundCtx Sorts k}
    (p : Source L n) (slots : Retained β (n + 1)) (test : Fin (n + 1)) :
    Operand signature.Instr β (packedExitType L) :=
  let kept := slots.without test
  if p.factored then
    let l := answerCase (p.arms.falseLeft.operand kept.bind) (p.arms.falseRight.operand kept.bind)
    let r := answerCase (p.arms.trueLeft.operand kept.bind) (p.arms.trueRight.operand kept.bind)
    let lhs := l.2.rename (BoundCtx.Renaming.succ (β.snoc Answer) U)
    let rhs := r.2.rename (BoundCtx.Renaming.succ (β.snoc Answer) U)
    let d := (slots.weaken Answer).read test
    ⟨.let₁ (.op (.ask p.request) .unit) (.case d.1 l.1.lift r.1.lift),
      .let₁ (.op .unit) (.case d.2 lhs rhs)⟩
  else
    let scope := (kept.weaken U).bind
    let l := requestOperand p.request false (p.arms.falseLeft.operand scope) (p.arms.falseRight.operand scope)
    let r := requestOperand p.request false (p.arms.trueLeft.operand scope) (p.arms.trueRight.operand scope)
    bitCase (slots.read test) l r

def bitCtx : (n : Nat) → BoundCtx Sorts n
  | 0 => .nil
  | n + 1 => (bitCtx n).snoc Bit

def bitSlots : (n : Nat) → Retained (bitCtx n) n
  | 0 => Fin.elim0
  | n + 1 => (bitSlots n).bind

def program (H : Sorts) (L : List Sorts) {n : Nat} (test : Fin (n + 1)) (p : Source (H :: L) n) :
    Program signature.Instr (bitCtx (n + 1)) (H :: L) :=
  ⟨packedExitType (H :: L), p.operand (bitSlots (n + 1)) test,
    Exits.router (rfl : At (H :: L) 0 H) (H :: L) (LambdaSSA.Ren.id (H :: L))⟩

def equation (H : Sorts) (L : List Sorts) {n : Nat} (test : Fin (n + 1)) (p q : Source (H :: L) n) :
    GrammarEquation signature :=
  ⟨⟨n + 1, bitCtx (n + 1), H :: L⟩, program H L test p, program H L test q⟩

noncomputable def packedAssignment : (n : Nat) → Assignment n → boundObj Kleisli.types (bitCtx n)
  | 0, _ => PUnit.unit
  | n + 1, env => (packedAssignment n env.tail, bit (env 0))

def NormalSource.traceTree {L : List Sorts} {n : Nat} (p : NormalSource L n)
    (test : Fin (n + 1)) (env : Assignment (n + 1)) : Reply.Normal (Exits.Exit L) :=
  let rest := env.without test
  if env test then
    requestTree p.request (fun b => p.arms.trueLeft.traceTree (rest.push b))
      (fun b => p.arms.trueRight.traceTree (rest.push b))
  else
    requestTree p.request (fun b => p.arms.falseLeft.traceTree (rest.push b))
      (fun b => p.arms.falseRight.traceTree (rest.push b))

def NormalSource.outcomes {L : List Sorts} {n : Nat} (p : NormalSource L n)
    (test : Fin (n + 1)) (env : Assignment (n + 1)) : Set (Outcome (value (packedExitType L))) :=
  (p.traceTree test env).outcomesWith Exits.Exit.packed

noncomputable def programOutcomes (H : Sorts) (L : List Sorts) {n : Nat}
    (test : Fin (n + 1)) (p : Source (H :: L) n) (env : Assignment (n + 1)) :
    Set (Outcome (value (packedExitType (H :: L)))) :=
  (Kleisli.run model (program H L test p).toLetCase.2 (boundEnv value (packedAssignment _ env))).outcomes

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite.CommonRequest
