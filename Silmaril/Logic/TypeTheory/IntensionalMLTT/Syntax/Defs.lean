module

public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# Scoped syntax for intensional cumulative MLTT

This is a source-informed extension of the scoped grammar of
`mr-ohman/logrel-mltt`, revision `9d6e290064962a1987c9e1a131c2fb967d6ef928`.
The source has one universe and no primitive identity type. Here universe
indices, annotated lambdas, identity types and based path induction are explicit.
No equality reflection or UIP rule is part of this syntax.

Index zero names the innermost variable. The motive of `j A a C d b p` binds
an endpoint and then its path from `a`; indices zero and one in `C` name the
path and endpoint. `natrec C z s t` uses a one-variable motive and an ordinary
step term, as in the source grammar. The source MIT notice is preserved in
`provenance/licenses/logrel-mltt.txt`.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Terms with exactly `n` available de Bruijn variables. -/
inductive Term : ℕ → Type
  | var {n : ℕ} (i : Fin n) : Term n
  | univ {n : ℕ} (level : ℕ) : Term n
  | empty {n : ℕ} : Term n
  | unit {n : ℕ} : Term n
  | star {n : ℕ} : Term n
  | nat {n : ℕ} : Term n
  | zero {n : ℕ} : Term n
  | succ {n : ℕ} (t : Term n) : Term n
  | pi {n : ℕ} (A : Term n) (B : Term (n + 1)) : Term n
  | sigma {n : ℕ} (A : Term n) (B : Term (n + 1)) : Term n
  | lam {n : ℕ} (A : Term n) (body : Term (n + 1)) : Term n
  | app {n : ℕ} (f : Term n) (a : Term n) : Term n
  | pair {n : ℕ} (a : Term n) (b : Term n) : Term n
  | fst {n : ℕ} (p : Term n) : Term n
  | snd {n : ℕ} (p : Term n) : Term n
  | natrec {n : ℕ} (C : Term (n + 1)) (z : Term n) (s : Term n) (t : Term n) : Term n
  | absurd {n : ℕ} (A : Term n) (e : Term n) : Term n
  | id {n : ℕ} (A : Term n) (a : Term n) (b : Term n) : Term n
  | refl {n : ℕ} (a : Term n) : Term n
  | j {n : ℕ} (A : Term n) (a : Term n) (C : Term (n + 2)) (d : Term n) (b : Term n) (p : Term n) : Term n
  deriving DecidableEq, Repr

namespace Term

/-- Lift a variable renaming beneath one binder. -/
def upRen {n m : ℕ} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cons 0 (fun i => (ρ i).succ)

/-- Capture-avoiding renaming, including the two binders of a J motive. -/
def rename {n m : ℕ} (ρ : Fin n → Fin m) : Term n → Term m
  | .var i => .var (ρ i)
  | .univ level => .univ level
  | .empty => .empty
  | .unit => .unit
  | .star => .star
  | .nat => .nat
  | .zero => .zero
  | .succ t => .succ (t.rename ρ)
  | .pi A B => .pi (A.rename ρ) (B.rename (upRen ρ))
  | .sigma A B => .sigma (A.rename ρ) (B.rename (upRen ρ))
  | .lam A body => .lam (A.rename ρ) (body.rename (upRen ρ))
  | .app f a => .app (f.rename ρ) (a.rename ρ)
  | .pair a b => .pair (a.rename ρ) (b.rename ρ)
  | .fst p => .fst (p.rename ρ)
  | .snd p => .snd (p.rename ρ)
  | .natrec C z s t => .natrec (C.rename (upRen ρ)) (z.rename ρ) (s.rename ρ) (t.rename ρ)
  | .absurd A e => .absurd (A.rename ρ) (e.rename ρ)
  | .id A a b => .id (A.rename ρ) (a.rename ρ) (b.rename ρ)
  | .refl a => .refl (a.rename ρ)
  | .j A a C d b p => .j (A.rename ρ) (a.rename ρ) (C.rename (upRen (upRen ρ))) (d.rename ρ) (b.rename ρ) (p.rename ρ)

/-- Scope extension adds an unused innermost variable. -/
def weaken {n : ℕ} (t : Term n) : Term (n + 1) := t.rename Fin.succ

/-- Lift a simultaneous substitution beneath one binder. -/
def upSub {n m : ℕ} (σ : Fin n → Term m) : Fin (n + 1) → Term (m + 1) :=
  Fin.cons (.var 0) (fun i => (σ i).weaken)

/-- Capture-avoiding simultaneous substitution. -/
def subst {n m : ℕ} (σ : Fin n → Term m) : Term n → Term m
  | .var i => σ i
  | .univ level => .univ level
  | .empty => .empty
  | .unit => .unit
  | .star => .star
  | .nat => .nat
  | .zero => .zero
  | .succ t => .succ (t.subst σ)
  | .pi A B => .pi (A.subst σ) (B.subst (upSub σ))
  | .sigma A B => .sigma (A.subst σ) (B.subst (upSub σ))
  | .lam A body => .lam (A.subst σ) (body.subst (upSub σ))
  | .app f a => .app (f.subst σ) (a.subst σ)
  | .pair a b => .pair (a.subst σ) (b.subst σ)
  | .fst p => .fst (p.subst σ)
  | .snd p => .snd (p.subst σ)
  | .natrec C z s t => .natrec (C.subst (upSub σ)) (z.subst σ) (s.subst σ) (t.subst σ)
  | .absurd A e => .absurd (A.subst σ) (e.subst σ)
  | .id A a b => .id (A.subst σ) (a.subst σ) (b.subst σ)
  | .refl a => .refl (a.subst σ)
  | .j A a C d b p => .j (A.subst σ) (a.subst σ) (C.subst (upSub (upSub σ))) (d.subst σ) (b.subst σ) (p.subst σ)

/-- Substitute one term for the innermost variable. -/
def instantiate {n : ℕ} (body : Term (n + 1)) (a : Term n) : Term n :=
  body.subst (Fin.cons a Term.var)

/-- Substitute an endpoint and path into a J motive, with path innermost. -/
def instantiate₂ {n : ℕ} (body : Term (n + 2)) (endpoint path : Term n) : Term n :=
  body.subst (Fin.cons path (Fin.cons endpoint Term.var))

/-- One more than the largest mentioned universe index, or zero when absent. -/
def universeBound : {n : ℕ} → Term n → ℕ
  | _, .var _ => 0
  | _, .univ level => level + 1
  | _, .empty => 0
  | _, .unit => 0
  | _, .star => 0
  | _, .nat => 0
  | _, .zero => 0
  | _, .succ t => t.universeBound
  | _, .pi A B => max (A.universeBound) B.universeBound
  | _, .sigma A B => max (A.universeBound) B.universeBound
  | _, .lam A body => max (A.universeBound) body.universeBound
  | _, .app f a => max (f.universeBound) a.universeBound
  | _, .pair a b => max (a.universeBound) b.universeBound
  | _, .fst p => p.universeBound
  | _, .snd p => p.universeBound
  | _, .natrec C z s t => max (max (max (C.universeBound) z.universeBound) s.universeBound) t.universeBound
  | _, .absurd A e => max (A.universeBound) e.universeBound
  | _, .id A a b => max (max (A.universeBound) a.universeBound) b.universeBound
  | _, .refl a => a.universeBound
  | _, .j A a C d b p => max (max (max (max (max (A.universeBound) a.universeBound) C.universeBound) d.universeBound) b.universeBound) p.universeBound

/-- Every universe occurrence lies below the specified available-level count. -/
def UsesBelow {n : ℕ} (t : Term n) (levels : ℕ) : Prop := t.universeBound ≤ levels

end Term

/-- A telescope: each declared type is scoped over the preceding context. -/
inductive Context : ℕ → Type
  | nil : Context 0
  | snoc {n : ℕ} (Γ : Context n) (A : Term n) : Context (n + 1)
  deriving Repr

/-- Universe bound across every declaration of a telescope. -/
def Context.universeBound : {n : ℕ} → Context n → ℕ
  | _, .nil => 0
  | _, .snoc Γ A => max Γ.universeBound A.universeBound

/-- Lookup returns a declaration weakened into the full context scope. -/
inductive Lookup : {n : ℕ} → Context n → Fin n → Term n → Prop
  | here {n : ℕ} {Γ : Context n} {A : Term n} :
      Lookup (Γ.snoc A) 0 A.weaken
  | there {n : ℕ} {Γ : Context n} {A B : Term n} {i : Fin n}
      (h : Lookup Γ i A) : Lookup (Γ.snoc B) i.succ A.weaken

end Silmaril.Logic.TypeTheory.IntensionalMLTT
