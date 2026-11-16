module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Defs

@[expose] public section

/-!
# Extensional MLTT syntax with W-types

This is an explicit extension of the existing MLTT term grammar. All original
constructors are retained, so dependent functions and the other base formers can
contain W-types. `Embedding` supplies the map from the original calculus.
The base clauses and rules are adapted from `Silmaril.Raw.Logic.TypeTheory.ExtensionalMLTT.Syntax`
at 47d0d8375263485c4b9066aae63597f2aacb8c0d; they have not been replaced in place.

Bound index zero is the innermost binder. As in the base API, `open` and `lst`
remove the outermost bound variable. W position families and elimination motives
each bind one variable.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- Terms of extensional MLTT with `k` bound variables in scope. -/
inductive Tm : ℕ → Type
  | fv {k : ℕ} (x : String) : Tm k
  | bv {k : ℕ} (i : Fin k) : Tm k
  /-- The universe `Uₙ`. -/
  | univ {k : ℕ} (n : ℕ) : Tm k
  | empty {k : ℕ} : Tm k
  | unit {k : ℕ} : Tm k
  /-- The element of `𝟏`. -/
  | star {k : ℕ} : Tm k
  | nats {k : ℕ} : Tm k
  | zero {k : ℕ} : Tm k
  | succ {k : ℕ} (n : Tm k) : Tm k
  /-- `natrec C s z n`, with motive `C` and step `s` binding the predecessor. -/
  | natrec {k : ℕ} (C s : Tm (k + 1)) (z n : Tm k) : Tm k
  | pi {k : ℕ} (A : Tm k) (B : Tm (k + 1)) : Tm k
  | sigma {k : ℕ} (A : Tm k) (B : Tm (k + 1)) : Tm k
  | abs {k : ℕ} (A : Tm k) (b : Tm (k + 1)) : Tm k
  | app {k : ℕ} (f a : Tm k) : Tm k
  | pair {k : ℕ} (a b : Tm k) : Tm k
  | fst {k : ℕ} (p : Tm k) : Tm k
  | snd {k : ℕ} (p : Tm k) : Tm k
  /-- The identity type `Id_A(a, b)`. -/
  | id {k : ℕ} (A a b : Tm k) : Tm k
  | refl {k : ℕ} (a : Tm k) : Tm k
  /-- `𝟎`-elimination `absurd_C(e)`. -/
  | absurd {k : ℕ} (C e : Tm k) : Tm k
  /-- The W-type of labels `A` and positions `B`, where `B` binds a label. -/
  | wtype {k : ℕ} (A : Tm k) (B : Tm (k + 1)) : Tm k
  /-- A W-node, with explicit label/position annotations. -/
  | sup {k : ℕ} (A : Tm k) (B : Tm (k + 1)) (a f : Tm k) : Tm k
  /-- Dependent W elimination; `C` binds the tree and `s` is the step function. -/
  | wrec {k : ℕ} (A : Tm k) (B C : Tm (k + 1)) (s t : Tm k) : Tm k

namespace Tm

/-- Weakening: shift bound variables `≥ j` up by one. -/
def wkn {k : ℕ} (j : ℕ) : Tm k → Tm (k + 1)
  | .fv x => .fv x
  | .bv i => if i < j then .bv i.castSucc else .bv i.succ
  | .univ n => .univ n
  | .empty => .empty
  | .unit => .unit
  | .star => .star
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.wkn j)
  | .natrec C s z n => .natrec (C.wkn (j + 1)) (s.wkn (j + 1)) (z.wkn j) (n.wkn j)
  | .pi A B => .pi (A.wkn j) (B.wkn (j + 1))
  | .sigma A B => .sigma (A.wkn j) (B.wkn (j + 1))
  | .abs A b => .abs (A.wkn j) (b.wkn (j + 1))
  | .app f a => .app (f.wkn j) (a.wkn j)
  | .pair a b => .pair (a.wkn j) (b.wkn j)
  | .fst p => .fst (p.wkn j)
  | .snd p => .snd (p.wkn j)
  | .id A a b => .id (A.wkn j) (a.wkn j) (b.wkn j)
  | .refl a => .refl (a.wkn j)
  | .absurd C e => .absurd (C.wkn j) (e.wkn j)
  | .wtype A B => .wtype (A.wkn j) (B.wkn (j + 1))
  | .sup A B a f => .sup (A.wkn j) (B.wkn (j + 1)) (a.wkn j) (f.wkn j)
  | .wrec A B C s t => .wrec (A.wkn j) (B.wkn (j + 1)) (C.wkn (j + 1)) (s.wkn j) (t.wkn j)

/-- Weakening under a fresh innermost variable. -/
def wk0 {k : ℕ} (t : Tm k) : Tm (k + 1) := t.wkn 0

/-- Lift a simultaneous substitution through one binder. -/
def liftSub {n m : ℕ} (σ : Fin n → Tm m) : Fin (n + 1) → Tm (m + 1) :=
  Fin.cases (.bv 0) (fun i => (σ i).wk0)

/-- Capture-avoiding simultaneous substitution for all bound variables. -/
def bsubst {n m : ℕ} (σ : Fin n → Tm m) : Tm n → Tm m
  | .fv x => .fv x
  | .bv i => σ i
  | .univ n => .univ n
  | .empty => .empty
  | .unit => .unit
  | .star => .star
  | .nats => .nats
  | .zero => .zero
  | .succ t => .succ (t.bsubst σ)
  | .natrec C s z t => .natrec (C.bsubst (liftSub σ)) (s.bsubst (liftSub σ))
      (z.bsubst σ) (t.bsubst σ)
  | .pi A B => .pi (A.bsubst σ) (B.bsubst (liftSub σ))
  | .sigma A B => .sigma (A.bsubst σ) (B.bsubst (liftSub σ))
  | .abs A b => .abs (A.bsubst σ) (b.bsubst (liftSub σ))
  | .app f a => .app (f.bsubst σ) (a.bsubst σ)
  | .pair a b => .pair (a.bsubst σ) (b.bsubst σ)
  | .fst t => .fst (t.bsubst σ)
  | .snd t => .snd (t.bsubst σ)
  | .id A a b => .id (A.bsubst σ) (a.bsubst σ) (b.bsubst σ)
  | .refl a => .refl (a.bsubst σ)
  | .absurd C e => .absurd (C.bsubst σ) (e.bsubst σ)
  | .wtype A B => .wtype (A.bsubst σ) (B.bsubst (liftSub σ))
  | .sup A B a f => .sup (A.bsubst σ) (B.bsubst (liftSub σ)) (a.bsubst σ) (f.bsubst σ)
  | .wrec A B C s t => .wrec (A.bsubst σ) (B.bsubst (liftSub σ))
      (C.bsubst (liftSub σ)) (s.bsubst σ) (t.bsubst σ)

/-- Embed a term into a larger scope (bound variables keep their indices). -/
def castLE {n m : ℕ} (h : n ≤ m) : Tm n → Tm m
  | .fv x => .fv x
  | .bv i => .bv (i.castLE h)
  | .univ l => .univ l
  | .empty => .empty
  | .unit => .unit
  | .star => .star
  | .nats => .nats
  | .zero => .zero
  | .succ t => .succ (t.castLE h)
  | .natrec C s z t => .natrec (C.castLE (by omega)) (s.castLE (by omega)) (z.castLE h)
      (t.castLE h)
  | .pi A B => .pi (A.castLE h) (B.castLE (by omega))
  | .sigma A B => .sigma (A.castLE h) (B.castLE (by omega))
  | .abs A b => .abs (A.castLE h) (b.castLE (by omega))
  | .app f a => .app (f.castLE h) (a.castLE h)
  | .pair a b => .pair (a.castLE h) (b.castLE h)
  | .fst p => .fst (p.castLE h)
  | .snd p => .snd (p.castLE h)
  | .id A a b => .id (A.castLE h) (a.castLE h) (b.castLE h)
  | .refl a => .refl (a.castLE h)
  | .absurd C e => .absurd (C.castLE h) (e.castLE h)
  | .wtype A B => .wtype (A.castLE h) (B.castLE (by omega))
  | .sup A B a f => .sup (A.castLE h) (B.castLE (by omega)) (a.castLE h) (f.castLE h)
  | .wrec A B C s t => .wrec (A.castLE h) (B.castLE (by omega)) (C.castLE (by omega))
      (s.castLE h) (t.castLE h)

/-- Instantiate the outermost bound variable with the free variable `x`. -/
def «open» {k : ℕ} (t : Tm (k + 1)) (x : String) : Tm k := match t with
  | .fv y => .fv y
  | .bv i => i.lastCases (.fv x) .bv
  | .univ n => .univ n
  | .empty => .empty
  | .unit => .unit
  | .star => .star
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.open x)
  | .natrec C s z n => .natrec (C.open x) (s.open x) (z.open x) (n.open x)
  | .pi A B => .pi (A.open x) (B.open x)
  | .sigma A B => .sigma (A.open x) (B.open x)
  | .abs A b => .abs (A.open x) (b.open x)
  | .app f a => .app (f.open x) (a.open x)
  | .pair a b => .pair (a.open x) (b.open x)
  | .fst p => .fst (p.open x)
  | .snd p => .snd (p.open x)
  | .id A a b => .id (A.open x) (a.open x) (b.open x)
  | .refl a => .refl (a.open x)
  | .absurd C e => .absurd (C.open x) (e.open x)
  | .wtype A B => .wtype (A.open x) (B.open x)
  | .sup A B a f => .sup (A.open x) (B.open x) (a.open x) (f.open x)
  | .wrec A B C s t => .wrec (A.open x) (B.open x) (C.open x) (s.open x) (t.open x)

/-- Instantiate the outermost bound variable with a closed term. -/
def lst {k : ℕ} (t : Tm (k + 1)) (v : Tm 0) : Tm k := match t with
  | .fv y => .fv y
  | .bv i => i.lastCases (v.castLE (by omega)) .bv
  | .univ n => .univ n
  | .empty => .empty
  | .unit => .unit
  | .star => .star
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (n.lst v)
  | .natrec C s z n => .natrec (C.lst v) (s.lst v) (z.lst v) (n.lst v)
  | .pi A B => .pi (A.lst v) (B.lst v)
  | .sigma A B => .sigma (A.lst v) (B.lst v)
  | .abs A b => .abs (A.lst v) (b.lst v)
  | .app f a => .app (f.lst v) (a.lst v)
  | .pair a b => .pair (a.lst v) (b.lst v)
  | .fst p => .fst (p.lst v)
  | .snd p => .snd (p.lst v)
  | .id A a b => .id (A.lst v) (a.lst v) (b.lst v)
  | .refl a => .refl (a.lst v)
  | .absurd C e => .absurd (C.lst v) (e.lst v)
  | .wtype A B => .wtype (A.lst v) (B.lst v)
  | .sup A B a f => .sup (A.lst v) (B.lst v) (a.lst v) (f.lst v)
  | .wrec A B C s t => .wrec (A.lst v) (B.lst v) (C.lst v) (s.lst v) (t.lst v)

/-- The non-dependent function type `A → B`. -/
def arr {k : ℕ} (A B : Tm k) : Tm k := .pi A B.wk0

/-- The free names that may affect a term's interpretation. -/
def fvs : {k : ℕ} → Tm k → Finset String
  | _, .fv x => {x}
  | _, .bv _ | _, .univ _ | _, .empty | _, .unit | _, .star | _, .nats | _, .zero => ∅
  | _, .succ t | _, .fst t | _, .snd t | _, .refl t => t.fvs
  | _, .pi A B | _, .sigma A B | _, .abs A B | _, .app A B | _, .pair A B |
      _, .absurd A B => A.fvs ∪ B.fvs
  | _, .natrec C s z n => C.fvs ∪ s.fvs ∪ z.fvs ∪ n.fvs
  | _, .id A a b => A.fvs ∪ a.fvs ∪ b.fvs
  | _, .wtype A B => A.fvs ∪ B.fvs
  | _, .sup A B a f => A.fvs ∪ B.fvs ∪ a.fvs ∪ f.fvs
  | _, .wrec A B C s t => A.fvs ∪ B.fvs ∪ C.fvs ∪ s.fvs ∪ t.fvs

/-- The step type for dependent W elimination.

Its binders, from outside in, are a label `a`, children `f`, and recursive
results `ih`. In the innermost result, these have indices 2, 1 and 0.
-/
def wStepType (A : Tm 0) (B C : Tm 1) : Tm 0 :=
  .pi A (.pi (.pi B ((Tm.wtype A B).castLE (by omega)))
    (.pi (.pi (B.bsubst (fun _ => .bv 1))
        (C.bsubst (fun _ => .app (.bv 1) (.bv 0))))
      (C.bsubst (fun _ => .sup (A.castLE (by omega)) (B.castLE (by omega))
        (.bv 2) (.bv 1)))))

/-- The recursive calls supplied to a W-elimination step. -/
def recChildren (A : Tm 0) (B C : Tm 1) (s a f : Tm 0) : Tm 0 :=
  .abs (B.lst a) (.wrec A.wk0 (B.wkn 1) (C.wkn 1) s.wk0 (.app f.wk0 (.bv 0)))

end Tm

/-- Contexts of extensional MLTT. -/
inductive Ctx : Type
  | nil : Ctx
  | cons (Γ : Ctx) (x : String) (A : Tm 0) : Ctx

/-- The declared variables of a context. -/
def Ctx.dv : Ctx → Finset String
  | .nil => ∅
  | .cons Γ x _ => insert x Γ.dv

/-- `x : A` is the latest declaration of `x` in `Γ`. -/
inductive Ctx.Lookup : Ctx → String → Tm 0 → Prop
  | here (Γ : Ctx) (x : String) (A : Tm 0) : Lookup (.cons Γ x A) x A
  | there (Γ : Ctx) (x y : String) (A B : Tm 0) :
      Lookup Γ x A → x ≠ y → Lookup (.cons Γ y B) x A

/-- An extensional MLTT judgment `Γ ⊢ a ≡ b : A` (type first, as in `Ctx.JEq`). -/
@[ext]
structure Jdg where
  /-- The context. -/
  Γ : Ctx
  /-- The type. -/
  A : Tm 0
  /-- The left-hand side. -/
  a : Tm 0
  /-- The right-hand side. -/
  b : Tm 0

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
