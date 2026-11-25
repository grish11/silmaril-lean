module

public import Silmaril.Courses.Cambridge.Concurrency.Typing

/-! # Cambridge L1 with primitive mutexes

The language on p. 92 of Sewell's 12 February 2026 notes adds `lock` and
`unlock` to concurrent L1. Both commands have type `unit`.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.Concurrency.Mutex

abbrev MutexName := String

inductive Expr where
  | int (value : Int)
  | bool (value : Bool)
  | binary (left : Expr) (op : Op) (right : Expr)
  | cond (test yes no : Expr)
  | assign (loc : Loc) (rhs : Expr)
  | deref (loc : Loc)
  | skip
  | seq (left right : Expr)
  | loop (test body : Expr)
  | parallel (left right : Expr)
  | lock (name : MutexName)
  | unlock (name : MutexName)
  deriving DecidableEq, Repr

def Expr.ofInterleaving : Concurrency.Expr → Expr
  | .int n => .int n
  | .bool b => .bool b
  | .binary left op right => .binary (ofInterleaving left) op (ofInterleaving right)
  | .cond test yes no => .cond (ofInterleaving test) (ofInterleaving yes) (ofInterleaving no)
  | .assign loc rhs => .assign loc (ofInterleaving rhs)
  | .deref loc => .deref loc
  | .skip => .skip
  | .seq left right => .seq (ofInterleaving left) (ofInterleaving right)
  | .loop test body => .loop (ofInterleaving test) (ofInterleaving body)
  | .parallel left right => .parallel (ofInterleaving left) (ofInterleaving right)

inductive IsValue : Expr → Prop where
  | int (n : Int) : IsValue (.int n)
  | bool (b : Bool) : IsValue (.bool b)
  | skip : IsValue .skip

inductive HasType (Γ : TypeEnv) : Expr → Ty → Prop where
  | int (n : Int) : HasType Γ (.int n) .int
  | bool (b : Bool) : HasType Γ (.bool b) .bool
  | add {left right : Expr} (hl : HasType Γ left .int) (hr : HasType Γ right .int) :
      HasType Γ (.binary left .add right) .int
  | ge {left right : Expr} (hl : HasType Γ left .int) (hr : HasType Γ right .int) :
      HasType Γ (.binary left .ge right) .bool
  | cond {test yes no : Expr} {T : Ty}
      (hc : HasType Γ test .bool) (hy : HasType Γ yes T) (hn : HasType Γ no T) :
      HasType Γ (.cond test yes no) T
  | assign {loc : Loc} {e : Expr} (present : loc ∈ Γ) (he : HasType Γ e .int) :
      HasType Γ (.assign loc e) .unit
  | deref {loc : Loc} (present : loc ∈ Γ) : HasType Γ (.deref loc) .int
  | skip : HasType Γ .skip .unit
  | seq {left right : Expr} {T : Ty}
      (hl : HasType Γ left .unit) (hr : HasType Γ right T) :
      HasType Γ (.seq left right) T
  | loop {test body : Expr}
      (ht : HasType Γ test .bool) (hb : HasType Γ body .unit) :
      HasType Γ (.loop test body) .unit
  | thread {e : Expr} (typing : HasType Γ e .unit) : HasType Γ e .proc
  | parallel {left right : Expr} (hl : HasType Γ left .proc) (hr : HasType Γ right .proc) :
      HasType Γ (.parallel left right) .proc
  | lock (name : MutexName) : HasType Γ (.lock name) .unit
  | unlock (name : MutexName) : HasType Γ (.unlock name) .unit

theorem HasType.ofInterleaving {Γ : TypeEnv} {e : Concurrency.Expr} {T : Ty}
    (typed : Concurrency.HasType Γ e T) : HasType Γ (Expr.ofInterleaving e) T := by
  induction typed with
  | int n => exact .int n
  | bool b => exact .bool b
  | add _ _ ihl ihr => exact .add ihl ihr
  | ge _ _ ihl ihr => exact .ge ihl ihr
  | cond _ _ _ ihc ihy ihn => exact .cond ihc ihy ihn
  | assign present _ ih => exact .assign present ih
  | deref present => exact .deref present
  | skip => exact .skip
  | seq _ _ ihl ihr => exact .seq ihl ihr
  | loop _ _ iht ihb => exact .loop iht ihb
  | thread _ ih => exact .thread ih
  | parallel _ _ ihl ihr => exact .parallel ihl ihr

end Silmaril.Courses.Cambridge.Concurrency.Mutex
