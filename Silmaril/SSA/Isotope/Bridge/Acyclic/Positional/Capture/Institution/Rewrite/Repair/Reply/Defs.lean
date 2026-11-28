module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Thms

/-! # A captured grammar of finite binary-reply effect trees -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply

open LambdaSSA.Acyclic (Operand)

abbrev Sorts := Ty Empty

abbrev Answer : Sorts := .coprod .unit .unit

inductive Op where
  | emit (bit : Bool)
  | ask (request : Bool)
  | stop (fault : Bool)

def signature : InstrSig Sorts Bool where
  Instr := Op
  hasTy := ⟨fun _ => .unit, fun op => match op with
    | .emit _ => .unit
    | .ask _ => Answer
    | .stop _ => .empty⟩
  hasEff := ⟨fun _ => true⟩

/-- At a request both continuations obtain a unit payload from the reply tag.
The scrutinee can be written directly or evaluated in an explicit let. -/
inductive Tree (R : Type := Unit) where
  | ret (result : R)
  | emit (bit : Bool) (next : Tree R)
  | ask (request : Bool) (bound : Bool) (left right : Tree R)
  | stop (fault : Bool) (sequenced : Bool)

abbrev Tree.returnUnit : Tree := .ret ()

/-- Keep event order and the two reply continuations. The two syntactic
choices of binders are erased. -/
inductive Normal (R : Type := Unit) where
  | ret (result : R)
  | emit (bit : Bool) (next : Normal R)
  | ask (request : Bool) (left right : Normal R)
  | stop (fault : Bool)

abbrev Normal.returnUnit : Normal := .ret ()

def Tree.normal {R : Type} : Tree R → Normal R
  | .ret r => .ret r
  | .emit bit next => .emit bit next.normal
  | .ask req _ l r => .ask req l.normal r.normal
  | .stop fault _ => .stop fault

def Normal.render {R : Type} : Normal R → Tree R
  | .ret r => .ret r
  | .emit bit next => .emit bit next.render
  | .ask req l r => .ask req false l.render r.render
  | .stop fault => .stop fault false

abbrev ReturnOperand (R : Type) (A : Sorts) :=
  ∀ {n : Nat} (β : BoundCtx Sorts n), R → Operand signature.Instr β A

def Tree.operandWith {R : Type} {A : Sorts} (ret : ReturnOperand R A)
    {n : Nat} (β : BoundCtx Sorts n) : Tree R → Operand signature.Instr β A
  | .ret r => ret β r
  | .emit bit next =>
    let b := next.operandWith ret (β.snoc Ty.unit)
    ⟨.let₁ (.op (.emit bit) .unit) b.1, .let₁ (.op .unit) b.2⟩
  | .ask req bound l r =>
    let lhs := l.operandWith ret (β.snoc Ty.unit)
    let rhs := r.operandWith ret (β.snoc Ty.unit)
    if bound then
      ⟨.let₁ (.op (.ask req) .unit) (.case (.bv 0) lhs.1.underBinder rhs.1.underBinder),
        .let₁ (.op .unit) (.case .bv lhs.2.underBinder rhs.2.underBinder)⟩
    else
      ⟨.case (.op (.ask req) .unit) lhs.1 rhs.1, .case (.op .unit) lhs.2 rhs.2⟩
  | .stop fault false => ⟨.abort (.op (.stop fault) .unit), .abort (.op .unit)⟩
  | .stop fault true =>
    ⟨.let₁ (.op (.stop fault) .unit) (.abort (.bv 0)), .let₁ (.op .unit) (.abort .bv)⟩

def unitReturn : ReturnOperand Unit Ty.unit := fun _ _ => ⟨.unit, .unit⟩

def Tree.operand {n : Nat} (β : BoundCtx Sorts n) (p : Tree) :
    Operand signature.Instr β Ty.unit :=
  p.operandWith unitReturn β

/-- Capture the finite tree as a typed entry operand and return any
successful unit result to outward position zero. -/
def equation (tail : List Sorts) (p q : Tree) : GrammarEquation signature :=
  ⟨⟨0, .nil, Ty.unit :: tail⟩, Rewrite.returnUnit tail (p.operand .nil),
    Rewrite.returnUnit tail (q.operand .nil)⟩

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply
