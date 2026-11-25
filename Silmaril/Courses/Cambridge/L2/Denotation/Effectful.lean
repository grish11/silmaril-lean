module

public import Silmaril.Courses.Cambridge.L2.Denotation.Pure
public import Silmaril.Courses.Cambridge.L2.Metatheory.Preservation
public import Mathlib.Data.Part

/-! # L2 CBV denotation with mutable store

This fragment uses the L2 rules of §§4.2–4.4 and §4.6 of the pinned
12 February 2026 notes. Functions are lexical closures whose applications
run in the current store. Loops and recursive bindings are outside the fragment.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L2.EffectfulDenotation

open PureDenotation (Ground)

/-- A computational typing derivation with an explicit location environment. -/
inductive Term (locations : L1.TypeEnv) : List Ty → Expr → Ty → Type where
  | int {Γ : List Ty} (n : Int) : Term locations Γ (.int n) .int
  | bool {Γ : List Ty} (b : Bool) : Term locations Γ (.bool b) .bool
  | skip {Γ : List Ty} : Term locations Γ .skip .unit
  | add {Γ : List Ty} {e f : Expr} :
      Term locations Γ e .int → Term locations Γ f .int → Term locations Γ (.binary e .add f) .int
  | ge {Γ : List Ty} {e f : Expr} :
      Term locations Γ e .int → Term locations Γ f .int → Term locations Γ (.binary e .ge f) .bool
  | cond {Γ : List Ty} {guard yes no : Expr} {T : Ty} :
      Term locations Γ guard .bool → Term locations Γ yes T → Term locations Γ no T → Term locations Γ (.cond guard yes no) T
  | seq {Γ : List Ty} {e f : Expr} {T : Ty} :
      Term locations Γ e .unit → Term locations Γ f T → Term locations Γ (.seq e f) T
  | bvar {Γ : List Ty} {i : Nat} {T : Ty} :
      Γ[i]? = some T → Term locations Γ (.bvar i) T
  | lam {Γ : List Ty} {body : Expr} {A B : Ty} :
      Term locations (A :: Γ) body B → Term locations Γ (.lam A body) (.arr A B)
  | app {Γ : List Ty} {fn arg : Expr} {A B : Ty} :
      Term locations Γ fn (.arr A B) → Term locations Γ arg A → Term locations Γ (.app fn arg) B
  | letE {Γ : List Ty} {value body : Expr} {A B : Ty} :
      Term locations Γ value A → Term locations (A :: Γ) body B → Term locations Γ (.letE A value body) B
  | deref {Γ : List Ty} {loc : Loc} (present : loc ∈ locations) :
      Term locations Γ (.deref loc) .int
  | assign {Γ : List Ty} {loc : Loc} {rhs : Expr} (present : loc ∈ locations) :
      Term locations Γ rhs .int → Term locations Γ (.assign loc rhs) .unit

/-- L2 typing environment for the fragment's bound variables. -/
def typingEnv (locations : L1.TypeEnv) (Γ : List Ty) : TypeEnv := ⟨locations, ∅, Γ⟩

abbrev Covers (locations : L1.TypeEnv) := StoreCovers (typingEnv locations [])

variable {locations : L1.TypeEnv}

theorem Term.hasType {Γ : List Ty} {e : Expr} {T : Ty} (term : Term locations Γ e T) :
    HasType (typingEnv locations Γ) e T := by
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
  | deref present => exact .deref present
  | assign present _ rhs => exact .assign present rhs

theorem Term.scoped {Γ : List Ty} {e : Expr} {T : Ty} (term : Term locations Γ e T) :
    e.Scoped Γ.length := by
  induction term with
  | int | bool | skip | deref => trivial
  | add _ _ hl hr | ge _ _ hl hr | seq _ _ hl hr | app _ _ hl hr => exact ⟨hl, hr⟩
  | cond _ _ _ hg hy hn => exact ⟨hg, hy, hn⟩
  | bvar lookup => exact (List.getElem?_eq_some_iff.mp lookup).choose
  | lam _ ih => exact ih
  | letE _ _ hv hb => exact ⟨hv, hb⟩
  | assign _ _ rhs => exact rhs

theorem Term.noFreeNames {Γ : List Ty} {e : Expr} {T : Ty} (term : Term locations Γ e T) :
    e.freeVars = ∅ := by
  induction term <;> simp_all [Expr.freeVars]

theorem Term.closed {e : Expr} {T : Ty} (term : Term locations [] e T) : e.Closed :=
  ⟨term.scoped, term.noFreeNames⟩

/-- A partial return carries both the value and the final store. -/
abbrev Computation (A : Type) := StateT Store Part A

/-- Closures are values. Applying one produces a computation in the current store. -/
abbrev Value : Ty → Type
  | .int => Int
  | .bool => Bool
  | .unit => Unit
  | .arr A B => Value A → Computation (Value B)

abbrev Env := Denotation.LexicalEnv Value

def read (loc : Loc) : Computation Int :=
  fun s => Part.ofOption ((L1.Store.lookup s loc).map (fun n => (n, s)))

def write (loc : Loc) (n : Int) : Computation Unit :=
  fun s => Part.ofOption ((L1.Store.update s loc n).map (fun t => ((), t)))

/-- Strict CBV sequencing threads the store through every operand. A lambda
saves its lexical environment and its body receives the store at application. -/
def Term.denote {Γ : List Ty} {e : Expr} {T : Ty} :
    Term locations Γ e T → Env Γ → Computation (Value T)
  | .int n, _ => pure n
  | .bool b, _ => pure b
  | .skip, _ => pure ()
  | .add left right, ρ => do
    let a ← left.denote ρ
    let b ← right.denote ρ
    pure (a + b)
  | .ge left right, ρ => do
    let a ← left.denote ρ
    let b ← right.denote ρ
    pure (decide (a ≥ b))
  | .cond guard yes no, ρ => do
    let test ← guard.denote ρ
    if test then yes.denote ρ else no.denote ρ
  | .seq first rest, ρ => do
    let _ ← first.denote ρ
    rest.denote ρ
  | .bvar lookup, ρ => pure (ρ.lookup lookup)
  | .lam body, ρ => pure (fun arg => body.denote (ρ.push arg))
  | .app fn arg, ρ => do
    let closure ← fn.denote ρ
    let value ← arg.denote ρ
    closure value
  | .letE value body, ρ => do
    let arg ← value.denote ρ
    body.denote (ρ.push arg)
  | .deref (loc := loc) _, _ => read loc
  | .assign (loc := loc) _ rhs, ρ => do
    let n ← rhs.denote ρ
    write loc n

def quoteGround {T : Ty} : Ground T → Value T → Expr
  | .int, n => .int n
  | .bool, b => .bool b
  | .unit, _ => .skip

/-- Ground value and final store, in the same shape as a CBV return. -/
def Term.observe {e : Expr} {T : Ty} (term : Term locations [] e T)
    (ground : Ground T) (s : Store) : Part Config :=
  ((term.denote Denotation.LexicalEnv.empty).run s).map
    (fun (v, finalStore) => ⟨quoteGround ground v, finalStore⟩)

end Silmaril.Courses.Cambridge.L2.EffectfulDenotation
