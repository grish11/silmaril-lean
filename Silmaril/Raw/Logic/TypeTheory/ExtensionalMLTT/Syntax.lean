module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# Extensional MLTT syntax and inference rules

Ported from Silmaril PR #2791, head
`9203df8258f40b4997232b481520a2b15eab8e0b`, file
`Silmaril/Logic/TypeTheory/Gt3/MLTT/Syntax.lean`.

This presentation has cumulative Russell universes indexed by natural numbers,
dependent functions and pairs, naturals, empty and unit types, and identity types.
Equality reflection, UIP and extensionality make it extensional MLTT.

Bound variables use `Fin`; index zero is the innermost binder. Opening and closed
substitution remove the outermost bound variable. Typing is the reflexive instance
of judgmental equality; context well-formedness is the judgment `⋆ ≡ ⋆ : 𝟏`.

The type formers follow Abel–Öhman–Vezzosi, POPL 2018; this presentation adds
identity types, extensionality and a natural-number-indexed hierarchy. It does not
include a choice operator.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Terms of extensional MLTT with `k` bound variables in scope. -/
inductive ETm : ℕ → Type
  | fv {k : ℕ} (x : String) : ETm k
  | bv {k : ℕ} (i : Fin k) : ETm k
  /-- The universe `Uₙ`. -/
  | univ {k : ℕ} (n : ℕ) : ETm k
  | empty {k : ℕ} : ETm k
  | unit {k : ℕ} : ETm k
  /-- The element of `𝟏`. -/
  | star {k : ℕ} : ETm k
  | nats {k : ℕ} : ETm k
  | zero {k : ℕ} : ETm k
  | succ {k : ℕ} (n : ETm k) : ETm k
  /-- `natrec C s z n`, with motive `C` and step `s` binding the predecessor. -/
  | natrec {k : ℕ} (C s : ETm (k + 1)) (z n : ETm k) : ETm k
  | pi {k : ℕ} (A : ETm k) (B : ETm (k + 1)) : ETm k
  | sigma {k : ℕ} (A : ETm k) (B : ETm (k + 1)) : ETm k
  | abs {k : ℕ} (A : ETm k) (b : ETm (k + 1)) : ETm k
  | app {k : ℕ} (f a : ETm k) : ETm k
  | pair {k : ℕ} (a b : ETm k) : ETm k
  | fst {k : ℕ} (p : ETm k) : ETm k
  | snd {k : ℕ} (p : ETm k) : ETm k
  /-- The identity type `Id_A(a, b)`. -/
  | id {k : ℕ} (A a b : ETm k) : ETm k
  | refl {k : ℕ} (a : ETm k) : ETm k
  /-- `𝟎`-elimination `absurd_C(e)`. -/
  | absurd {k : ℕ} (C e : ETm k) : ETm k

namespace ETm

/-- Weakening: shift bound variables `≥ j` up by one. -/
def wkn {k : ℕ} (j : ℕ) : ETm k → ETm (k + 1)
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

/-- Weakening under a fresh innermost variable. -/
def wk0 {k : ℕ} (t : ETm k) : ETm (k + 1) := t.wkn 0

/-- Embed a term into a larger scope (bound variables keep their indices). -/
def castLE {n m : ℕ} (h : n ≤ m) : ETm n → ETm m
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

/-- Instantiate the outermost bound variable with the free variable `x`. -/
def «open» {k : ℕ} (t : ETm (k + 1)) (x : String) : ETm k := match t with
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

/-- Instantiate the outermost bound variable with a closed term. -/
def lst {k : ℕ} (t : ETm (k + 1)) (v : ETm 0) : ETm k := match t with
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

/-- The non-dependent function type `A → B`. -/
def arr {k : ℕ} (A B : ETm k) : ETm k := .pi A B.wk0

/-- The free names that may affect a term's interpretation. -/
def fvs : {k : ℕ} → ETm k → Finset String
  | _, .fv x => {x}
  | _, .bv _ | _, .univ _ | _, .empty | _, .unit | _, .star | _, .nats | _, .zero => ∅
  | _, .succ t | _, .fst t | _, .snd t | _, .refl t => t.fvs
  | _, .pi A B | _, .sigma A B | _, .abs A B | _, .app A B | _, .pair A B |
      _, .absurd A B => A.fvs ∪ B.fvs
  | _, .natrec C s z n => C.fvs ∪ s.fvs ∪ z.fvs ∪ n.fvs
  | _, .id A a b => A.fvs ∪ a.fvs ∪ b.fvs

end ETm

/-- Contexts of extensional MLTT. -/
inductive ECtx : Type
  | nil : ECtx
  | cons (Γ : ECtx) (x : String) (A : ETm 0) : ECtx

/-- The declared variables of a context. -/
def ECtx.dv : ECtx → Finset String
  | .nil => ∅
  | .cons Γ x _ => insert x Γ.dv

/-- `x : A` is the latest declaration of `x` in `Γ`. -/
inductive ECtx.Lookup : ECtx → String → ETm 0 → Prop
  | here (Γ : ECtx) (x : String) (A : ETm 0) : Lookup (.cons Γ x A) x A
  | there (Γ : ECtx) (x y : String) (A B : ETm 0) :
      Lookup Γ x A → x ≠ y → Lookup (.cons Γ y B) x A

/-- An extensional MLTT judgment `Γ ⊢ a ≡ b : A` (type first, as in `ECtx.JEq`). -/
@[ext]
structure EJdg where
  /-- The context. -/
  Γ : ECtx
  /-- The type. -/
  A : ETm 0
  /-- The left-hand side. -/
  a : ETm 0
  /-- The right-hand side. -/
  b : ETm 0

open ETm in
/-- Derivable judgmental equality of extensional MLTT. -/
inductive ECtx.JEq : ECtx → ETm 0 → ETm 0 → ETm 0 → Prop
  -- Context well-formedness
  | nil_ok : JEq .nil .unit .star .star
  | cons_ok {Γ : ECtx} {x : String} {A : ETm 0} {n : ℕ}
    (hΓ : JEq Γ .unit .star .star) (hx : x ∉ Γ.dv) (hA : JEq Γ (.univ n) A A)
    : JEq (Γ.cons x A) .unit .star .star
  -- Variables and constants
  | var {Γ : ECtx} {x : String} {A : ETm 0} (hΓ : JEq Γ .unit .star .star) (hx : Γ.Lookup x A)
    : JEq Γ A (.fv x) (.fv x)
  | univ {Γ : ECtx} {n : ℕ} (hΓ : JEq Γ .unit .star .star)
    : JEq Γ (.univ (n + 1)) (.univ n) (.univ n)
  | empty {Γ : ECtx} {n : ℕ} (hΓ : JEq Γ .unit .star .star) : JEq Γ (.univ n) .empty .empty
  | unit {Γ : ECtx} {n : ℕ} (hΓ : JEq Γ .unit .star .star) : JEq Γ (.univ n) .unit .unit
  | nats {Γ : ECtx} {n : ℕ} (hΓ : JEq Γ .unit .star .star) : JEq Γ (.univ n) .nats .nats
  | zero {Γ : ECtx} (hΓ : JEq Γ .unit .star .star) : JEq Γ .nats .zero .zero
  -- Congruence
  | succ {Γ : ECtx} {m m' : ETm 0} (h : JEq Γ .nats m m') : JEq Γ .nats (.succ m) (.succ m')
  | pi {Γ : ECtx} {n : ℕ} {A A' : ETm 0} {B B' : ETm 1} {L : Finset String}
    (hA : JEq Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
    : JEq Γ (.univ n) (.pi A B) (.pi A' B')
  | sigma {Γ : ECtx} {n : ℕ} {A A' : ETm 0} {B B' : ETm 1} {L : Finset String}
    (hA : JEq Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
    : JEq Γ (.univ n) (.sigma A B) (.sigma A' B')
  | id {Γ : ECtx} {n : ℕ} {A A' a a' b b' : ETm 0}
    (hA : JEq Γ (.univ n) A A') (ha : JEq Γ A a a') (hb : JEq Γ A b b')
    : JEq Γ (.univ n) (.id A a b) (.id A' a' b')
  | abs {Γ : ECtx} {n : ℕ} {A A' : ETm 0} {B b b' : ETm 1} {L : Finset String}
    (hA : JEq Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hb : ∀ x ∉ L, JEq (Γ.cons x A) (B.open x) (b.open x) (b'.open x))
    : JEq Γ (.pi A B) (.abs A b) (.abs A' b')
  | app {Γ : ECtx} {n : ℕ} {A f f' a a' : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEq Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : JEq Γ (.pi A B) f f') (ha : JEq Γ A a a')
    : JEq Γ (B.lst a) (.app f a) (.app f' a')
  | pair {Γ : ECtx} {n : ℕ} {A a a' b b' : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEq Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEq Γ A a a') (hb : JEq Γ (B.lst a) b b')
    : JEq Γ (.sigma A B) (.pair a b) (.pair a' b')
  | fst {Γ : ECtx} {n : ℕ} {A p p' : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEq Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEq Γ (.sigma A B) p p')
    : JEq Γ A (.fst p) (.fst p')
  | snd {Γ : ECtx} {n : ℕ} {A p p' : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEq Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEq Γ (.sigma A B) p p')
    : JEq Γ (B.lst (.fst p)) (.snd p) (.snd p')
  | natrec {Γ : ECtx} {n : ℕ} {C C' s s' : ETm 1} {z z' m m' : ETm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEq (Γ.cons x .nats) (.univ n) (C.open x) (C'.open x))
    (hz : JEq Γ (C.lst .zero) z z')
    (hs : ∀ x ∉ L, JEq (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s'.open x))
    (hm : JEq Γ .nats m m')
    : JEq Γ (C.lst m) (.natrec C s z m) (.natrec C' s' z' m')
  | refl {Γ : ECtx} {A a a' : ETm 0} (ha : JEq Γ A a a') : JEq Γ (.id A a a) (.refl a) (.refl a')
  | absurd {Γ : ECtx} {n : ℕ} {C C' e e' : ETm 0}
    (hC : JEq Γ (.univ n) C C') (he : JEq Γ .empty e e')
    : JEq Γ C (.absurd C e) (.absurd C' e')
  -- Computation
  | beta_app {Γ : ECtx} {n : ℕ} {A a : ETm 0} {B b : ETm 1} {L : Finset String}
    (hA : JEq Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hb : ∀ x ∉ L, JEq (Γ.cons x A) (B.open x) (b.open x) (b.open x))
    (ha : JEq Γ A a a)
    : JEq Γ (B.lst a) (.app (.abs A b) a) (b.lst a)
  | beta_fst {Γ : ECtx} {n : ℕ} {A a b : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEq Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEq Γ A a a) (hb : JEq Γ (B.lst a) b b)
    : JEq Γ A (.fst (.pair a b)) a
  | beta_snd {Γ : ECtx} {n : ℕ} {A a b : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEq Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEq Γ A a a) (hb : JEq Γ (B.lst a) b b)
    : JEq Γ (B.lst a) (.snd (.pair a b)) b
  | beta_natrec_zero {Γ : ECtx} {n : ℕ} {C s : ETm 1} {z : ETm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEq (Γ.cons x .nats) (.univ n) (C.open x) (C.open x))
    (hz : JEq Γ (C.lst .zero) z z)
    (hs : ∀ x ∉ L, JEq (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s.open x))
    : JEq Γ (C.lst .zero) (.natrec C s z .zero) z
  | beta_natrec_succ {Γ : ECtx} {n : ℕ} {C s : ETm 1} {z m : ETm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEq (Γ.cons x .nats) (.univ n) (C.open x) (C.open x))
    (hz : JEq Γ (C.lst .zero) z z)
    (hs : ∀ x ∉ L, JEq (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s.open x))
    (hm : JEq Γ .nats m m)
    : JEq Γ (C.lst (.succ m)) (.natrec C s z (.succ m)) (.app (s.lst m) (.natrec C s z m))
  -- Extensionality
  | reflect {Γ : ECtx} {A a b p : ETm 0} (ha : JEq Γ A a a) (hb : JEq Γ A b b)
    (hp : JEq Γ (.id A a b) p p) : JEq Γ A a b
  | id_uip {Γ : ECtx} {A a b p : ETm 0} (ha : JEq Γ A a a) (hb : JEq Γ A b b)
    (hp : JEq Γ (.id A a b) p p) : JEq Γ (.id A a b) p (.refl a)
  | unit_ext {Γ : ECtx} {a : ETm 0} (ha : JEq Γ .unit a a) : JEq Γ .unit a .star
  | pi_ext {Γ : ECtx} {n : ℕ} {A f g : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEq Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : JEq Γ (.pi A B) f f) (hg : JEq Γ (.pi A B) g g)
    (hfg : ∀ x ∉ L, JEq (Γ.cons x A) (B.open x) (.app f (.fv x)) (.app g (.fv x)))
    : JEq Γ (.pi A B) f g
  | sigma_ext {Γ : ECtx} {n : ℕ} {A p q : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEq Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEq (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEq Γ (.sigma A B) p p) (hq : JEq Γ (.sigma A B) q q)
    (h1 : JEq Γ A (.fst p) (.fst q)) (h2 : JEq Γ (B.lst (.fst p)) (.snd p) (.snd q))
    : JEq Γ (.sigma A B) p q
  -- Equivalence, conversion and cumulativity
  | symm {Γ : ECtx} {A a b : ETm 0} (h : JEq Γ A a b) : JEq Γ A b a
  | trans {Γ : ECtx} {A a b c : ETm 0} (hab : JEq Γ A a b) (hbc : JEq Γ A b c) : JEq Γ A a c
  | conv {Γ : ECtx} {n : ℕ} {A A' a a' : ETm 0} (hA : JEq Γ (.univ n) A A') (ha : JEq Γ A a a')
    : JEq Γ A' a a'
  | cumul {Γ : ECtx} {m n : ℕ} {A A' : ETm 0} (hmn : m ≤ n) (hA : JEq Γ (.univ m) A A')
    : JEq Γ (.univ n) A A'

/-- Derivability of a judgment. -/
def EJdg.Derivable (j : EJdg) : Prop := ECtx.JEq j.Γ j.A j.a j.b

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
