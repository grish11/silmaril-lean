module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Defs

@[expose] public section

/-! # Derivations from judgment hypotheses

This extension retains every source inference rule and allows hypotheses at
leaves. Hypotheses are not restricted to an inert disjunction with closed
derivability. Context weakening and substitution for arbitrary theories are
separate admissibility properties.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

open ETm in
/-- MLTT derivations with judgment hypotheses. The inference rules are those of `ECtx.JEq`. -/
inductive ECtx.JEqH (H : Set EJdg) : ECtx → ETm 0 → ETm 0 → ETm 0 → Prop
  | hyp {Γ : ECtx} {A a b : ETm 0} (h : (⟨Γ, A, a, b⟩ : EJdg) ∈ H) :
      JEqH H Γ A a b
  -- Context well-formedness
  | nil_ok : JEqH H .nil .unit .star .star
  | cons_ok {Γ : ECtx} {x : String} {A : ETm 0} {n : ℕ}
    (hΓ : JEqH H Γ .unit .star .star) (hx : x ∉ Γ.dv) (hA : JEqH H Γ (.univ n) A A)
    : JEqH H (Γ.cons x A) .unit .star .star
  -- Variables and constants
  | var {Γ : ECtx} {x : String} {A : ETm 0} (hΓ : JEqH H Γ .unit .star .star) (hx : Γ.Lookup x A)
    : JEqH H Γ A (.fv x) (.fv x)
  | univ {Γ : ECtx} {n : ℕ} (hΓ : JEqH H Γ .unit .star .star)
    : JEqH H Γ (.univ (n + 1)) (.univ n) (.univ n)
  | empty {Γ : ECtx} {n : ℕ} (hΓ : JEqH H Γ .unit .star .star) : JEqH H Γ (.univ n) .empty .empty
  | unit {Γ : ECtx} {n : ℕ} (hΓ : JEqH H Γ .unit .star .star) : JEqH H Γ (.univ n) .unit .unit
  | nats {Γ : ECtx} {n : ℕ} (hΓ : JEqH H Γ .unit .star .star) : JEqH H Γ (.univ n) .nats .nats
  | zero {Γ : ECtx} (hΓ : JEqH H Γ .unit .star .star) : JEqH H Γ .nats .zero .zero
  -- Congruence
  | succ {Γ : ECtx} {m m' : ETm 0} (h : JEqH H Γ .nats m m') : JEqH H Γ .nats (.succ m) (.succ m')
  | pi {Γ : ECtx} {n : ℕ} {A A' : ETm 0} {B B' : ETm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
    : JEqH H Γ (.univ n) (.pi A B) (.pi A' B')
  | sigma {Γ : ECtx} {n : ℕ} {A A' : ETm 0} {B B' : ETm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
    : JEqH H Γ (.univ n) (.sigma A B) (.sigma A' B')
  | id {Γ : ECtx} {n : ℕ} {A A' a a' b b' : ETm 0}
    (hA : JEqH H Γ (.univ n) A A') (ha : JEqH H Γ A a a') (hb : JEqH H Γ A b b')
    : JEqH H Γ (.univ n) (.id A a b) (.id A' a' b')
  | abs {Γ : ECtx} {n : ℕ} {A A' : ETm 0} {B b b' : ETm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hb : ∀ x ∉ L, JEqH H (Γ.cons x A) (B.open x) (b.open x) (b'.open x))
    : JEqH H Γ (.pi A B) (.abs A b) (.abs A' b')
  | app {Γ : ECtx} {n : ℕ} {A f f' a a' : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : JEqH H Γ (.pi A B) f f') (ha : JEqH H Γ A a a')
    : JEqH H Γ (B.lst a) (.app f a) (.app f' a')
  | pair {Γ : ECtx} {n : ℕ} {A a a' b b' : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEqH H Γ A a a') (hb : JEqH H Γ (B.lst a) b b')
    : JEqH H Γ (.sigma A B) (.pair a b) (.pair a' b')
  | fst {Γ : ECtx} {n : ℕ} {A p p' : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEqH H Γ (.sigma A B) p p')
    : JEqH H Γ A (.fst p) (.fst p')
  | snd {Γ : ECtx} {n : ℕ} {A p p' : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEqH H Γ (.sigma A B) p p')
    : JEqH H Γ (B.lst (.fst p)) (.snd p) (.snd p')
  | natrec {Γ : ECtx} {n : ℕ} {C C' s s' : ETm 1} {z z' m m' : ETm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEqH H (Γ.cons x .nats) (.univ n) (C.open x) (C'.open x))
    (hz : JEqH H Γ (C.lst .zero) z z')
    (hs : ∀ x ∉ L, JEqH H (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s'.open x))
    (hm : JEqH H Γ .nats m m')
    : JEqH H Γ (C.lst m) (.natrec C s z m) (.natrec C' s' z' m')
  | refl {Γ : ECtx} {A a a' : ETm 0} (ha : JEqH H Γ A a a') : JEqH H Γ (.id A a a) (.refl a) (.refl a')
  | absurd {Γ : ECtx} {n : ℕ} {C C' e e' : ETm 0}
    (hC : JEqH H Γ (.univ n) C C') (he : JEqH H Γ .empty e e')
    : JEqH H Γ C (.absurd C e) (.absurd C' e')
  -- Computation
  | beta_app {Γ : ECtx} {n : ℕ} {A a : ETm 0} {B b : ETm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hb : ∀ x ∉ L, JEqH H (Γ.cons x A) (B.open x) (b.open x) (b.open x))
    (ha : JEqH H Γ A a a)
    : JEqH H Γ (B.lst a) (.app (.abs A b) a) (b.lst a)
  | beta_fst {Γ : ECtx} {n : ℕ} {A a b : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEqH H Γ A a a) (hb : JEqH H Γ (B.lst a) b b)
    : JEqH H Γ A (.fst (.pair a b)) a
  | beta_snd {Γ : ECtx} {n : ℕ} {A a b : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEqH H Γ A a a) (hb : JEqH H Γ (B.lst a) b b)
    : JEqH H Γ (B.lst a) (.snd (.pair a b)) b
  | beta_natrec_zero {Γ : ECtx} {n : ℕ} {C s : ETm 1} {z : ETm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEqH H (Γ.cons x .nats) (.univ n) (C.open x) (C.open x))
    (hz : JEqH H Γ (C.lst .zero) z z)
    (hs : ∀ x ∉ L, JEqH H (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s.open x))
    : JEqH H Γ (C.lst .zero) (.natrec C s z .zero) z
  | beta_natrec_succ {Γ : ECtx} {n : ℕ} {C s : ETm 1} {z m : ETm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEqH H (Γ.cons x .nats) (.univ n) (C.open x) (C.open x))
    (hz : JEqH H Γ (C.lst .zero) z z)
    (hs : ∀ x ∉ L, JEqH H (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s.open x))
    (hm : JEqH H Γ .nats m m)
    : JEqH H Γ (C.lst (.succ m)) (.natrec C s z (.succ m)) (.app (s.lst m) (.natrec C s z m))
  -- Extensionality
  | reflect {Γ : ECtx} {A a b p : ETm 0} (ha : JEqH H Γ A a a) (hb : JEqH H Γ A b b)
    (hp : JEqH H Γ (.id A a b) p p) : JEqH H Γ A a b
  | id_uip {Γ : ECtx} {A a b p : ETm 0} (ha : JEqH H Γ A a a) (hb : JEqH H Γ A b b)
    (hp : JEqH H Γ (.id A a b) p p) : JEqH H Γ (.id A a b) p (.refl a)
  | unit_ext {Γ : ECtx} {a : ETm 0} (ha : JEqH H Γ .unit a a) : JEqH H Γ .unit a .star
  | pi_ext {Γ : ECtx} {n : ℕ} {A f g : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : JEqH H Γ (.pi A B) f f) (hg : JEqH H Γ (.pi A B) g g)
    (hfg : ∀ x ∉ L, JEqH H (Γ.cons x A) (B.open x) (.app f (.fv x)) (.app g (.fv x)))
    : JEqH H Γ (.pi A B) f g
  | sigma_ext {Γ : ECtx} {n : ℕ} {A p q : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEqH H Γ (.sigma A B) p p) (hq : JEqH H Γ (.sigma A B) q q)
    (h1 : JEqH H Γ A (.fst p) (.fst q)) (h2 : JEqH H Γ (B.lst (.fst p)) (.snd p) (.snd q))
    : JEqH H Γ (.sigma A B) p q
  -- Equivalence, conversion and cumulativity
  | symm {Γ : ECtx} {A a b : ETm 0} (h : JEqH H Γ A a b) : JEqH H Γ A b a
  | trans {Γ : ECtx} {A a b c : ETm 0} (hab : JEqH H Γ A a b) (hbc : JEqH H Γ A b c) : JEqH H Γ A a c
  | conv {Γ : ECtx} {n : ℕ} {A A' a a' : ETm 0} (hA : JEqH H Γ (.univ n) A A') (ha : JEqH H Γ A a a')
    : JEqH H Γ A' a a'
  | cumul {Γ : ECtx} {m n : ℕ} {A A' : ETm 0} (hmn : m ≤ n) (hA : JEqH H Γ (.univ m) A A')
    : JEqH H Γ (.univ n) A A'


end Silmaril.Logic.TypeTheory.ExtensionalMLTT
