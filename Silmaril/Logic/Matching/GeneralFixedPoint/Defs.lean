module

public import Silmaril.Logic.Matching.FixedPoint.Thms

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.GeneralFixedPoint
open CategoryTheory Silmaril.Logic.Institution
open Algebraic.ManySorted (Signature)
variable {S : Type} (A : Signature S)

/-- General Boolean matching syntax. A sentence separately certifies that each
fixed-point body's own recursion variable has no negative occurrence. Free set
variables may occur with either polarity, including mixed occurrences. -/
inductive Pattern : {r k : Nat} → (Fin r → S) → (Fin k → S) → S → Type where
  | base {r k P Γ s} : FirstOrder.Pattern (k := k) A Γ s → Pattern (r := r) P Γ s
  | setvar {r k P Γ} (i : Fin r) : Pattern (k := k) P Γ (P i)
  | app {r k P Γ n inputs output} (op : A.operations n inputs output)
      (args : ∀ i, Pattern (r := r) (k := k) P Γ (inputs i)) : Pattern P Γ output
  | neg {r k P Γ s} : Pattern (r := r) (k := k) P Γ s → Pattern P Γ s
  | conj {r k P Γ s} : Pattern (r := r) (k := k) P Γ s → Pattern P Γ s → Pattern P Γ s
  | ex {r k P Γ s} (bound : S) (body : Pattern (r := r) (k := k+1) P (Fin.cases bound Γ) s) :
      Pattern (k := k) P Γ s
  | mu {r k} {P' : Fin (r+1) → S} {Γ : Fin k → S}
      (body : Pattern P' Γ (P' 0)) : Pattern (P' ∘ Fin.succ) Γ (P' 0)
  | nu {r k} {P' : Fin (r+1) → S} {Γ : Fin k → S}
      (body : Pattern P' Γ (P' 0)) : Pattern (P' ∘ Fin.succ) Γ (P' 0)

abbrev Model := FirstOrder.Model A
abbrev ObjEnv (M : Model A) {k : Nat} (Γ : Fin k → S) := ∀ i, M.carrier (Γ i)
abbrev SetEnv (M : Model A) {r : Nat} (P : Fin r → S) := ∀ i, Set (M.carrier (P i))

variable {A}

/-- `negative = true` asks for a negative occurrence; binders shift the queried
free index and negation reverses the requested polarity. -/
def Pattern.occurs {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S}
    (p : Pattern A P Γ s) : Bool → Fin r → Bool := by
  induction p with
  | base _ => exact fun _ _ => false
  | setvar j => exact fun negative i => !negative && i == j
  | app _ _ ih => exact fun negative i => (List.finRange _).any (fun j => ih j negative i)
  | neg _ ih => exact fun negative i => ih (!negative) i
  | conj _ _ hp hq => exact fun negative i => hp negative i || hq negative i
  | ex _ _ ih => exact ih
  | mu _ ih => exact fun negative i => ih negative i.succ
  | nu _ ih => exact fun negative i => ih negative i.succ

/-- This executable check imposes positivity locally at every μ/ν binder,
without imposing monotonicity in the sentence's free set variables. -/
def Pattern.admissible {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S}
    (p : Pattern A P Γ s) : Bool := by
  induction p with
  | base _ | setvar _ => exact true
  | app _ _ ih => exact (List.finRange _).all ih
  | neg _ ih | ex _ _ ih => exact ih
  | conj _ _ hp hq => exact hp && hq
  | mu p ih | nu p ih => exact ih && !p.occurs true 0

/-- Direct set semantics, before admission. Invalid binders receive no unfolding
or fixed-point theorem. Admitted bodies are proved monotone separately. -/
def Pattern.denote (M : Model A) {r k : Nat} {P : Fin r → S} {Γ : Fin k → S}
    {s : S} (p : Pattern A P Γ s) : ObjEnv A M Γ → SetEnv A M P → Set (M.carrier s) := by
  induction p with
  | base p => exact fun v _ => M.denote v p
  | setvar i => exact fun _ η => η i
  | app op _ ih => exact fun v η => FixedPoint.application M op (fun i => ih i v η)
  | neg _ ih => exact fun v η => (ih v η)ᶜ
  | conj _ _ hp hq => exact fun v η => hp v η ∩ hq v η
  | ex b _ ih => exact fun v η => {x | ∃ a : M.carrier b, x ∈ ih (Fin.cases a v) η}
  | mu _ ih => exact fun v η => sInf {X | ih v (Fin.cases X η) ⊆ X}
  | nu _ ih => exact fun v η => sSup {X | X ⊆ ih v (Fin.cases X η)}

def Pattern.map {B : Signature S} (f : A ⟶ B) {r k : Nat} {P : Fin r → S}
    {Γ : Fin k → S} {s : S} (p : Pattern A P Γ s) : Pattern B P Γ s := by
  induction p with
  | base p => exact .base (FirstOrder.Pattern.map f p)
  | setvar i => exact .setvar i
  | app op _ ih => exact .app (f.operations op) ih
  | neg _ ih => exact .neg ih
  | conj _ _ hp hq => exact .conj hp hq
  | ex b _ ih => exact .ex b ih
  | mu _ ih => exact .mu ih
  | nu _ ih => exact .nu ih

def Pattern.disj {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S}
    (p q : Pattern A P Γ s) : Pattern A P Γ s := .neg (.conj (.neg p) (.neg q))

def Pattern.all {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s b : S}
    (p : Pattern A P (Fin.cases b Γ) s) : Pattern A P Γ s := .neg (.ex b (.neg p))

/-- Structural embedding of the existing positive normal form. Its De Morgan
application is represented by genuine Boolean syntax. -/
def ofPositive {r k : Nat} {P : Fin r → S} {Γ : Fin k → S} {s : S}
    (p : FixedPoint.Pattern A P Γ s) : Pattern A P Γ s := by
  induction p with
  | base p => exact .base p
  | setvar i => exact .setvar i
  | app op _ ih => exact .app op ih
  | dualApp op _ ih => exact .neg (.app op (fun i => .neg (ih i)))
  | conj _ _ hp hq => exact .conj hp hq
  | disj _ _ hp hq => exact hp.disj hq
  | ex b _ ih => exact .ex b ih
  | all _ _ ih => exact ih.all
  | mu _ ih => exact .mu ih
  | nu _ ih => exact .nu ih
end Silmaril.Logic.Matching.GeneralFixedPoint
