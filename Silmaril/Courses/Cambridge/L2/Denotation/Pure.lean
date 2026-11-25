module

public import Silmaril.Courses.Cambridge.L2.Typing

/-! # A compositional denotation for pure CBV L2

The judgment indexes the existing L2 expressions. It admits the ground
constructors, primitive operators, conditionals, sequences, bound variables
and functions of §§4.1–4.3, and strict nonrecursive let from §4.4 of the pinned
12 February 2026 notes. Each lambda denotes a function that closes over
its lexical environment.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.PureDenotation

/-- A computational typing derivation for the recursion-free and store-free fragment. -/
inductive Term : List Ty → Expr → Ty → Type where
  | int {Γ : List Ty} (n : Int) : Term Γ (.int n) .int
  | bool {Γ : List Ty} (b : Bool) : Term Γ (.bool b) .bool
  | skip {Γ : List Ty} : Term Γ .skip .unit
  | add {Γ : List Ty} {e f : Expr} :
      Term Γ e .int → Term Γ f .int → Term Γ (.binary e .add f) .int
  | ge {Γ : List Ty} {e f : Expr} :
      Term Γ e .int → Term Γ f .int → Term Γ (.binary e .ge f) .bool
  | cond {Γ : List Ty} {guard yes no : Expr} {T : Ty} :
      Term Γ guard .bool → Term Γ yes T → Term Γ no T → Term Γ (.cond guard yes no) T
  | seq {Γ : List Ty} {e f : Expr} {T : Ty} :
      Term Γ e .unit → Term Γ f T → Term Γ (.seq e f) T
  | bvar {Γ : List Ty} {i : Nat} {T : Ty} :
      Γ[i]? = some T → Term Γ (.bvar i) T
  | lam {Γ : List Ty} {body : Expr} {A B : Ty} :
      Term (A :: Γ) body B → Term Γ (.lam A body) (.arr A B)
  | app {Γ : List Ty} {fn arg : Expr} {A B : Ty} :
      Term Γ fn (.arr A B) → Term Γ arg A → Term Γ (.app fn arg) B
  | letE {Γ : List Ty} {value body : Expr} {A B : Ty} :
      Term Γ value A → Term (A :: Γ) body B → Term Γ (.letE A value body) B

/-- L2 typing environment for the fragment's bound variables. -/
def typingEnv (Γ : List Ty) : TypeEnv := { TypeEnv.empty with bound := Γ }

theorem Term.hasType {Γ : List Ty} {e : Expr} {T : Ty} (term : Term Γ e T) :
    HasType (typingEnv Γ) e T := by
  induction term with
  | int n => exact .int n
  | bool b => exact .bool b
  | skip => exact .skip
  | add _ _ left right => exact .add left right
  | ge _ _ left right => exact .ge left right
  | cond _ _ _ guard yes no => exact .cond guard yes no
  | seq _ _ left right => exact .seq left right
  | bvar lookup => exact .bvar lookup
  | lam _ body => exact .lam body
  | app _ _ fn arg => exact .app fn arg
  | letE _ _ value body => exact .letE value body

theorem Term.scoped {Γ : List Ty} {e : Expr} {T : Ty} (term : Term Γ e T) :
    e.Scoped Γ.length := by
  induction term with
  | int | bool | skip => trivial
  | add _ _ hl hr | ge _ _ hl hr | seq _ _ hl hr | app _ _ hl hr => exact ⟨hl, hr⟩
  | cond _ _ _ hg hy hn => exact ⟨hg, hy, hn⟩
  | bvar lookup => exact (List.getElem?_eq_some_iff.mp lookup).choose
  | lam _ ih => exact ih
  | letE _ _ hv hb => exact ⟨hv, hb⟩

theorem Term.noFreeNames {Γ : List Ty} {e : Expr} {T : Ty} (term : Term Γ e T) :
    e.freeVars = ∅ := by
  induction term <;> simp_all [Expr.freeVars]

theorem Term.closed {e : Expr} {T : Ty} (term : Term [] e T) : e.Closed :=
  ⟨term.scoped, term.noFreeNames⟩

/-- Total semantic values for the ground and function types of the fragment. -/
abbrev Value : Ty → Type
  | .int => Int
  | .bool => Bool
  | .unit => Unit
  | .arr A B => Value A → Value B

/-- A typed lexical environment, with the most recent binder first. -/
def Env : List Ty → Type
  | [] => Unit
  | A :: Γ => Value A × Env Γ

def Env.empty : Env [] := ()

def Env.push {Γ : List Ty} {A : Ty} (environment : Env Γ) (value : Value A) : Env (A :: Γ) :=
  (value, environment)

def Env.lookup : {Γ : List Ty} → Env Γ → {i : Nat} → {T : Ty} →
    Γ[i]? = some T → Value T
  | [], _, _, _, lookup => by simp at lookup
  | _ :: _, environment, 0, _, lookup => by
    cases Option.some.inj lookup
    exact environment.1
  | _ :: _, environment, _ + 1, _, lookup => Env.lookup environment.2 lookup

/-- Interpret terms compositionally. Application uses the meaning of the
argument, and the function body uses the environment saved at the lambda. -/
def Term.denote {Γ : List Ty} {e : Expr} {T : Ty} : Term Γ e T → Env Γ → Value T
  | .int n, _ => n
  | .bool b, _ => b
  | .skip, _ => ()
  | .add left right, ρ => left.denote ρ + right.denote ρ
  | .ge left right, ρ => decide (left.denote ρ ≥ right.denote ρ)
  | .cond guard yes no, ρ => if guard.denote ρ then yes.denote ρ else no.denote ρ
  | .seq left right, ρ =>
    match left.denote ρ with
    | () => right.denote ρ
  | .bvar lookup, ρ => ρ.lookup lookup
  | .lam body, ρ => fun arg => body.denote (ρ.push arg)
  | .app fn arg, ρ => fn.denote ρ (arg.denote ρ)
  | .letE value body, ρ => body.denote (ρ.push (value.denote ρ))

inductive Ground : Ty → Type where
  | int : Ground .int
  | bool : Ground .bool
  | unit : Ground .unit

def Ground.quote {T : Ty} : Ground T → Value T → Expr
  | .int, n => .int n
  | .bool, b => .bool b
  | .unit, _ => .skip

end Silmaril.Courses.Cambridge.L2.PureDenotation
