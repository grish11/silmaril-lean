module

public import Silmaril.Logic.Institution.Examples.Equational
public import Silmaril.Calculi.LambdaCube.STLC.Thms
public import Mathlib.Data.List.OfFn

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Algebraic.Lambda
open CategoryTheory Silmaril.Logic.Institution.Examples
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Cslib.LambdaCalculus.LocallyNameless.Stlc

/-- Convert a public finite context to the actual lambda list context. -/
def context {B : Type} : {n : Nat} → (Fin n → B) → List (Ty B)
  | 0, _ => []
  | n + 1, w => .base (w 0) :: context (fun i : Fin n => w i.succ)

def contextVar {B : Type} : {n : Nat} → (w : Fin n → B) → (i : Fin n) →
    Var (context w) (.base (w i))
  | 0, _, i => i.elim0
  | _ + 1, w, i => Fin.cases .zero (fun j => .succ (contextVar (fun i => w i.succ) j)) i

def envTuple {B : Type} : {n : Nat} → (w : Fin n → B) → (X : Ty B → Type) →
    (∀ i, X (.base (w i))) → Tuple X (context w)
  | 0, _, _, _ => Tuple.nil
  | _ + 1, w, X, ρ => Tuple.cons (ρ 0) (envTuple (fun i => w i.succ) X (fun i => ρ i.succ))

/-- First-order operators become genuine base-typed lambda operators. -/
inductive Operation (A : EQ.Signature) : List (Ty A.S) → Ty A.S → Type where
  | original {n w s} (o : A.Op n w s) : Operation A (context w) (.base s)

abbrev signature (A : EQ.Signature) : Signature := ⟨A.S, Operation A⟩

def term {A : EQ.Signature} {n : Nat} {Γ : Fin n → A.S} :
    {s : A.S} → EQ.Term A Γ s → Term (signature A) (context Γ) (.base s)
  | _, .var i => .var (contextVar Γ i)
  | _, .app o args => .op (.original o)
      (envTuple _ (fun τ => Term (signature A) (context Γ) τ) (fun i => term (args i)))

def equation {A : EQ.Signature} (e : EQ.Equation A) : STLC.Sentence (signature A) :=
  .equation (term e.lhs) (term e.rhs)

def reduct {A : EQ.Signature} (M : STLC.SetModel (signature A)) : EQ.Algebra A where
  carrier := M.base
  op o args := M.op (.original o) (envTuple _ (STLC.carrier M.base) args)

def expand {A : EQ.Signature} (M : EQ.Algebra A) : STLC.SetModel (signature A) where
  base := M.carrier
  op o args := match o with
    | .original o => M.op o (fun i => args _ (contextVar _ i))

end Silmaril.Logic.Algebraic.Lambda
