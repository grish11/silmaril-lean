module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Reply.Payload.Defs

/-! # Finite witnessed request trees with scoped binary payloads -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite

open Kleisli (value)
open Isotope.Semantics (BoundEnv)
open LambdaSSA (At)
open LambdaSSA.Acyclic (FiniteExit Operand)
open LambdaSSA.Acyclic.Positional.Capture.Reverse (Program)
open LambdaSSA.Region (packedExitType)
open LetIter.Semantics.Categorical (boundEnv)

local notation "U" => (Ty.unit : Sorts)

/-- The retained reply slots, newest first, in the actual native context.
Other native binders may occur between these slots. -/
abbrev Retained {k : Nat} (β : BoundCtx Sorts k) (n : Nat) :=
  Fin n → {j : Fin k // β.get j = Bit}

def Retained.read {k n : Nat} {β : BoundCtx Sorts k} (slots : Retained β n) (i : Fin n) :
    Operand signature.Instr β Bit :=
  readPayload β (slots i).1 (slots i).2

def Retained.weaken {k n : Nat} {β : BoundCtx Sorts k} (slots : Retained β n) (A : Sorts) :
    Retained (β.snoc A) n :=
  fun i => ⟨(slots i).1.succ, (slots i).2⟩

def Retained.bind {k n : Nat} {β : BoundCtx Sorts k} (slots : Retained β n) :
    Retained (β.snoc Bit) (n + 1) :=
  Fin.cases ⟨0, rfl⟩ (slots.weaken Bit)

/-- Remove a tested slot from the logical arm scope while keeping the
native locations of all remaining bits. -/
def Retained.without {k n : Nat} {β : BoundCtx Sorts k} (slots : Retained β (n + 1))
    (i : Fin (n + 1)) : Retained β n :=
  fun j => slots (i.succAbove j)

abbrev Assignment (n : Nat) := Fin n → Bool

def Assignment.push {n : Nat} (env : Assignment n) (b : Bool) : Assignment (n + 1) :=
  Fin.cases b env

def Assignment.tail {n : Nat} (env : Assignment (n + 1)) : Assignment n :=
  fun i => env i.succ

def Assignment.without {n : Nat} (env : Assignment (n + 1)) (i : Fin (n + 1)) : Assignment n :=
  fun j => env (i.succAbove j)

/-- The typed slots denote the values in the logical reply assignment. -/
def Retained.Matches {k n : Nat} {β : BoundCtx Sorts k} (slots : Retained β n)
    (ρ : BoundEnv value β) (env : Assignment n) : Prop :=
  ∀ i, (slots i).2 ▸ ρ (slots i).1 = bit (env i)

/-- A return can read any retained bit, return a literal, or test the
newest bit and continue testing the older bits in its branches. -/
inductive Expr : Nat → Type where
  | literal {n : Nat} (b : Bool) : Expr n
  | read {n : Nat} (i : Fin n) : Expr n
  | split {n : Nat} (low high : Expr n) : Expr (n + 1)

abbrev Table (n : Nat) := Assignment n → Bool

def Expr.eval {n : Nat} : Expr n → Table n
  | .literal b, _ => b
  | .read i, env => env i
  | .split low high, env => if env 0 then high.eval env.tail else low.eval env.tail

def Expr.quote : (n : Nat) → Table n → Expr n
  | 0, table => .literal (table Fin.elim0)
  | n + 1, table =>
    .split (quote n (fun env => table (env.push false))) (quote n (fun env => table (env.push true)))

def Expr.operand {n : Nat} (e : Expr n) {k : Nat} {β : BoundCtx Sorts k} (slots : Retained β n) :
    Operand signature.Instr β Bit :=
  match e with
  | .literal b => bitOperand β b
  | .read i => slots.read i
  | .split low high =>
    let d := slots.read 0
    let older : Retained (β.snoc U) _ := fun i => slots.weaken U i.succ
    let l := low.operand older
    let r := high.operand older
    ⟨.case d.1 l.1 r.1, .case d.2 l.2 r.2⟩

/-- Request tags select the control subtree. Its payload extends the
available reply environment and may influence the terminal value. -/
inductive Tree (L : List Sorts) : Nat → Type where
  | ret {n : Nat} (position : Position L) (result : Expr n) : Tree L n
  | emit {n : Nat} (label : Bool) (next : Tree L n) : Tree L n
  | request {n : Nat} (label bound : Bool) (left right : Tree L (n + 1)) : Tree L n

  /-- Test a retained bit. The false arm requests `low` and the true arm
  requests its complement. Each continuation retains the untested bits
  and gains the new reply payload. -/
  | testRequest {n : Nat} (test : Fin (n + 1)) (low lowBound highBound : Bool)
      (falseLeft falseRight trueLeft trueRight : Tree L (n + 1)) : Tree L (n + 1)

inductive Normal (L : List Sorts) : Nat → Type where
  | ret {n : Nat} (position : Position L) (result : Table n) : Normal L n
  | emit {n : Nat} (label : Bool) (next : Normal L n) : Normal L n
  | request {n : Nat} (label : Bool) (left right : Normal L (n + 1)) : Normal L n

  | testRequest {n : Nat} (test : Fin (n + 1)) (low : Bool)
      (falseLeft falseRight trueLeft trueRight : Normal L (n + 1)) : Normal L (n + 1)

def Tree.normal {L : List Sorts} {n : Nat} : Tree L n → Normal L n
  | .ret p result => .ret p result.eval
  | .emit b k => .emit b k.normal
  | .request req _ l r => .request req l.normal r.normal
  | .testRequest test low _ _ falseLeft falseRight trueLeft trueRight =>
    .testRequest test low falseLeft.normal falseRight.normal trueLeft.normal trueRight.normal

def Normal.render {L : List Sorts} {n : Nat} : Normal L n → Tree L n
  | .ret p table => .ret p (Expr.quote _ table)
  | .emit b k => .emit b k.render
  | .request req l r => .request req false l.render r.render
  | .testRequest test low falseLeft falseRight trueLeft trueRight =>
    .testRequest test low false false falseLeft.render falseRight.render trueLeft.render trueRight.render

def Tree.operand {L : List Sorts} {n : Nat} (t : Tree L n)
    {k : Nat} {β : BoundCtx Sorts k} (slots : Retained β n) :
    Operand signature.Instr β (packedExitType L) :=
  match t with
  | .ret p result => FiniteExit.tag L p.1 p.typed (result.operand slots)
  | .emit b next =>
    let k := next.operand (slots.weaken U)
    ⟨.let₁ (.op (.emit b) .unit) k.1, .let₁ (.op .unit) k.2⟩
  | .request req bound l r => requestOperand req bound (l.operand slots.bind) (r.operand slots.bind)
  | .testRequest test low lowBound highBound falseLeft falseRight trueLeft trueRight =>
    let read := slots.read test
    let scope := ((slots.without test).weaken U).bind
    let l := requestOperand low lowBound (falseLeft.operand scope) (falseRight.operand scope)
    let r := requestOperand (!low) highBound (trueLeft.operand scope) (trueRight.operand scope)
    ⟨.case read.1 l.1 r.1, .case read.2 l.2 r.2⟩

def program (H : Sorts) (L : List Sorts) (p : Tree (H :: L) 0) :
    Program signature.Instr .nil (H :: L) :=
  ⟨packedExitType (H :: L), p.operand Fin.elim0,
    Exits.router (rfl : At (H :: L) 0 H) (H :: L) (LambdaSSA.Ren.id (H :: L))⟩

def equation (H : Sorts) (L : List Sorts) (p q : Tree (H :: L) 0) : GrammarEquation signature :=
  ⟨⟨0, .nil, H :: L⟩, program H L p, program H L q⟩

/-- Enumerate the paths independently of the LetCase syntax and its evaluator. -/
def Normal.traceTree {L : List Sorts} {n : Nat} (t : Normal L n) (env : Assignment n) :
    Reply.Normal (Exits.Exit L) :=
  match t with
  | .ret p table => .ret (p.result (table env))
  | .emit b k => .emit b (k.traceTree env)
  | .request req l r => requestTree req (fun b => l.traceTree (env.push b)) (fun b => r.traceTree (env.push b))
  | .testRequest test low falseLeft falseRight trueLeft trueRight =>
    let rest := env.without test
    if env test then requestTree (!low) (fun b => trueLeft.traceTree (rest.push b)) (fun b => trueRight.traceTree (rest.push b))
    else requestTree low (fun b => falseLeft.traceTree (rest.push b)) (fun b => falseRight.traceTree (rest.push b))

def Normal.outcomes {L : List Sorts} {n : Nat} (t : Normal L n) (env : Assignment n) :
    Set (Outcome (value (packedExitType L))) :=
  (t.traceTree env).outcomesWith Exits.Exit.packed

noncomputable def programOutcomes (H : Sorts) (L : List Sorts) (p : Tree (H :: L) 0) :
    Set (Outcome (value (packedExitType (H :: L)))) :=
  (Kleisli.run model (program H L p).toLetCase.2
    (boundEnv value (β := .nil) PUnit.unit)).outcomes

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite
