module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Defs

/-! # Finite Boolean request trees over the shaped overlay -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree

open TwoRequest (Exit Exits Handler Instr Tag)
open Category.FiniteIteration (Result)

/-- Branches may have different depths. Each native request has literal-unit
input and branches on its exact Boolean reply. Leaves return or expose UB. -/
inductive Tree where
  | stop (exit : Exit)
  | ask (key : Instr) (left right : Tree)

def Tree.depth : Tree → Nat
  | .stop _ => 0
  | .ask _ left right => max left.depth right.depth + 1

/-- Elaborate using the same native effectful case region as the two-request
fragment. Every selected continuation binds its unit payload. -/
def Tree.region : (p : Tree) → {Γ : List (Silmaril.Ty Empty)} → Overlay.Region Instr Γ Exits
  | .stop e, _ => e.region
  | .ask f left right, Γ =>
    .lsubst (.native (TwoRequest.request f Γ)) fun (i : Tag) =>
      if i = 0 then left.region else right.region

/-- A literal UB leaf on the right permits anything. Two requests must have
the same key and compare recursively at each reply tag. A request and an
ordinary return cannot refine one another in all shaped models. -/
def Tree.Refines : Tree → Tree → Prop
  | .stop a, .stop b => a.Refines b
  | .ask _ _ _, .stop .ub => True
  | .ask f l r, .ask g l' r' => f = g ∧ l.Refines l' ∧ r.Refines r'
  | _, _ => False

def Tree.execute {n : Nat} (h : Handler n) : Tree → Fin n → Result 2 n
  | .stop e, s => e.result s
  | .ask f l r, s =>
    match h f s with
    | .reply i t => if i = 0 then l.execute h t else r.execute h t
    | .fault t => .fault t
    | .diverge => .diverge

/-- A test fixes one common path of successful replies. At its last state,
it either diverges on all keys or faults on one designated key. -/
inductive Prefix : Nat → Type
  | stop (fault : Option Instr) : Prefix 0
  | step {n : Nat} (key : Instr) (tag : Tag) (rest : Prefix n) : Prefix (n + 1)

/-- Prefix positions are machine states. Each successful reply advances to
the next position. All nonselected requests at that position diverge. -/
def Prefix.handler : {n : Nat} → Prefix n → Handler (n + 1)
  | _, .stop fault => fun f _ => if fault = some f then .fault 0 else .diverge
  | _, .step key tag rest => fun f s =>
    Fin.cases
      (if f = key then .reply tag (Fin.succ 0) else .diverge)
      (fun t =>
        match rest.handler f t with
        | .reply i u => .reply i u.succ
        | .fault u => .fault u.succ
        | .diverge => .diverge) s

/-- Prefix states embed into the enlarged handler by successor. -/
theorem Prefix.handler_succ {n : Nat} (rest : Prefix n) (key f : Instr) (tag : Tag)
    (s : Fin (n + 1)) :
    (Prefix.step key tag rest).handler f s.succ =
      match rest.handler f s with
      | .reply i t => .reply i t.succ
      | .fault t => .fault t.succ
      | .diverge => .diverge := rfl

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree
