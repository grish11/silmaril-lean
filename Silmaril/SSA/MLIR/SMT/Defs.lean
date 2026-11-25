module

public import Silmaril.Logic.Smt.Uflia.Quantified.Substitution.Thms

/-! # Pure MLIR SMT blocks

A typed SSA slice of the MLIR SMT dialect. Each operation binds one result.
A quantifier body starts with its block arguments and may capture values from
the enclosing scope. The block yields exactly one result.
-/

@[expose] public section

namespace Silmaril.MLIR.SMT

open Silmaril.Logic.Smt
open Uflia (SortCode)

inductive Ty where
  | bool
  | int
  deriving DecidableEq

/-- Embed `!smt.bool` and `!smt.int` in the existing quantified SMT language. -/
abbrev Ty.toSmt : Ty → SortCode Empty
  | .bool => .bool
  | .int => .int

/-- The slice has no uninterpreted declarations. Free SSA values are variables. -/
def signature : Uflia.Signature Empty := ⟨fun _ _ _ => Empty⟩

def model : Uflia.Model signature := Uflia.Model.trivial signature

/-- The fixed SMT carriers give the source its full Bool and Int domains. -/
abbrev Ty.Value (s : Ty) : Type := model.carriers.value s.toSmt

abbrev Context := List Ty

/-- The most recent SSA definition is at index zero. -/
def Context.toSmt : (Γ : Context) → Fin Γ.length → SortCode Empty
  | [] => Fin.elim0
  | s :: Γ => Fin.cases s.toSmt (Context.toSmt Γ)

inductive Var : Context → Ty → Type where
  | here {Γ s} : Var (s :: Γ) s
  | there {Γ s t} : Var Γ s → Var (t :: Γ) s

def Var.toSmt {Γ : Context} {s : Ty} :
    Var Γ s → Uflia.Quantified.Ref (Context.toSmt Γ) s.toSmt
  | .here => .index 0
  | .there (t := t) x => x.toSmt.succ t.toSmt

abbrev Term (Γ : Context) (s : Ty) :=
  Uflia.Quantified.Term signature (Context.toSmt Γ) s.toSmt

abbrev Formula (Γ : Context) := Uflia.Quantified.Formula signature (Context.toSmt Γ)

inductive Env : Context → Type where
  | nil : Env []
  | cons {Γ s} : s.Value → Env Γ → Env (s :: Γ)

def Env.get {Γ : Context} {s : Ty} (env : Env Γ) : Var Γ s → s.Value
  | .here => let .cons x _ := env; x
  | .there i => let .cons _ rest := env; rest.get i

def Env.toSmt {Γ : Context} : Env Γ → (i : Fin Γ.length) → model.carriers.value (Context.toSmt Γ i)
  | .nil => fun i => i.elim0
  | .cons x env => Fin.cases x env.toSmt

/-- The four predicates of `smt.int.cmp` on mathematical integers. -/
inductive IntPredicate where
  | lt
  | le
  | gt
  | ge

def IntPredicate.eval (pred : IntPredicate) (x y : Int) : Bool :=
  match pred with
  | .lt => decide (x < y)
  | .le => decide (x ≤ y)
  | .gt => decide (x > y)
  | .ge => decide (x ≥ y)

def IntPredicate.toSmt {Γ : Context} (pred : IntPredicate) (x y : Term Γ .int) : Formula Γ :=
  match pred with
  | .lt => .app .lt (Fin.cases x (fun _ => y))
  | .le => .app .le (Fin.cases x (fun _ => y))
  | .gt => .app .lt (Fin.cases y (fun _ => x))
  | .ge => .app .le (Fin.cases y (fun _ => x))

/-- Pure primitive operations on already defined SSA values. Equality takes
at least two same-sort operands. Conjunction, disjunction and addition are binary here. -/
inductive Rhs (Γ : Context) : Ty → Type where
  | boolConst (b : Bool) : Rhs Γ .bool
  | intConst (n : Int) : Rhs Γ .int
  | not (x : Var Γ .bool) : Rhs Γ .bool
  | and (x y : Var Γ .bool) : Rhs Γ .bool
  | or (x y : Var Γ .bool) : Rhs Γ .bool
  | eq {s} (x y : Var Γ s) (rest : List (Var Γ s) := []) : Rhs Γ .bool
  | ite {s} (cond : Var Γ .bool) (yes no : Var Γ s) : Rhs Γ s
  | add (x y : Var Γ .int) : Rhs Γ .int
  | intCmp (pred : IntPredicate) (x y : Var Γ .int) : Rhs Γ .bool

/-- SMT-LIB equality is chainable. Every adjacent pair must be equal. -/
noncomputable def Rhs.evalEq {Γ : Context} {s : Ty} (env : Env Γ) (x y : Var Γ s) :
    List (Var Γ s) → Bool := by
  classical
  exact fun rest =>
    let equal := decide (env.get x = env.get y)
    match rest with
    | [] => equal
    | z :: zs => equal && Rhs.evalEq env y z zs

def Rhs.toSmtEq {Γ : Context} {s : Ty} (x y : Var Γ s) (rest : List (Var Γ s)) : Formula Γ :=
  let equal : Formula Γ := .app (.eq s.toSmt) (Fin.cases x.toSmt.term (fun _ => y.toSmt.term))
  match rest with
  | [] => equal
  | z :: zs => .app .and (Fin.cases equal (fun _ => Rhs.toSmtEq y z zs))

noncomputable def Rhs.eval {Γ : Context} {s : Ty} (op : Rhs Γ s) (env : Env Γ) : s.Value := by
  classical
  exact match op with
  | .boolConst b => b
  | .intConst n => n
  | .not x => !(env.get x)
  | .and x y => env.get x && env.get y
  | .or x y => env.get x || env.get y
  | .eq x y rest => Rhs.evalEq env x y rest
  | .ite c x y => if env.get c = true then env.get x else env.get y
  | .add x y => Int.add (env.get x) (env.get y)
  | .intCmp pred x y => pred.eval (env.get x) (env.get y)

def Rhs.toSmt {Γ : Context} {s : Ty} : Rhs Γ s → Term Γ s
  | .boolConst b => .app (.boolean b) (fun i => i.elim0)
  | .intConst n => .app (.integer n) (fun i => i.elim0)
  | .not x => .app .not (fun _ => x.toSmt.term)
  | .and x y => .app .and (Fin.cases x.toSmt.term (fun _ => y.toSmt.term))
  | .or x y => .app .or (Fin.cases x.toSmt.term (fun _ => y.toSmt.term))
  | .eq x y rest => Rhs.toSmtEq x y rest
  | .ite (s := t) c x y =>
      .app (.ite t.toSmt) (Fin.cases c.toSmt.term (Fin.cases x.toSmt.term (fun _ => y.toSmt.term)))
  | .add x y => .app .add (Fin.cases x.toSmt.term (fun _ => y.toSmt.term))
  | .intCmp pred x y => pred.toSmt x.toSmt.term y.toSmt.term

/-- Extend a scope with block arguments in source order. Each argument
occupies a fresh slot, with the last argument at index zero. -/
def Context.bind (Γ : Context) : List Ty → Context
  | [] => Γ
  | s :: ss => Context.bind (s :: Γ) ss

inductive Quantifier where
  | all
  | ex

/-- Evaluate a quantifier over the full carrier of each block argument. -/
noncomputable def Quantifier.eval (q : Quantifier) {Γ : Context} (env : Env Γ) :
    (ss : List Ty) → (Env (Context.bind Γ ss) → Bool) → Bool := by
  classical
  intro ss body
  exact match ss with
  | [] => body env
  | s :: ss =>
      match q with
      | .all => decide (∀ x : s.Value, Quantifier.eval q (.cons x env) ss body = true)
      | .ex => decide (∃ x : s.Value, Quantifier.eval q (.cons x env) ss body = true)

def Quantifier.toSmt (q : Quantifier) {Γ : Context} :
    (ss : List Ty) → Formula (Context.bind Γ ss) → Formula Γ
  | [], body => body
  | s :: ss, body =>
      match q with
      | .all => .all s.toSmt (Quantifier.toSmt q (Γ := s :: Γ) ss body)
      | .ex => .ex s.toSmt (Quantifier.toSmt q (Γ := s :: Γ) ss body)

/-- A quantifier binds at least one block argument. Its body yields Bool and
sees the enclosing scope plus its arguments. Its SSA result is visible only
in the continuation. -/
inductive Block : Context → Ty → Type where
  | yield {Γ s} (value : Var Γ s) : Block Γ s
  | letOp {Γ s t} (op : Rhs Γ s) (rest : Block (s :: Γ) t) : Block Γ t
  | letQuantifier {Γ t} (q : Quantifier) (first : Ty) (others : List Ty)
      (body : Block (Context.bind Γ (first :: others)) .bool) (rest : Block (.bool :: Γ) t) : Block Γ t

/-- Denotation by evaluation of the SSA bindings in order. -/
noncomputable def Block.eval {Γ : Context} {s : Ty} : Block Γ s → Env Γ → s.Value
  | .yield x, env => env.get x
  | .letOp op rest, env => rest.eval (.cons (op.eval env) env)
  | .letQuantifier q first others body rest, env =>
      rest.eval (.cons (q.eval env (first :: others) body.eval) env)

/-- Lower each SSA binding by capture-avoiding instantiation. Each quantifier
argument becomes one nested binder in the resulting SMT term. -/
def Block.toSmt {Γ : Context} {s : Ty} : Block Γ s → Term Γ s
  | .yield x => x.toSmt.term
  | .letOp op rest => rest.toSmt.instantiate op.toSmt
  | .letQuantifier q first others body rest =>
      rest.toSmt.instantiate (q.toSmt (first :: others) body.toSmt)

def Block.toFormula {Γ : Context} (block : Block Γ .bool) : Formula Γ := block.toSmt

end Silmaril.MLIR.SMT
