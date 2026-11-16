module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Defs

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Tm in
/-- Derivable judgmental equality of extensional MLTT. -/
inductive Ctx.JEqH (H : Set Jdg) : Ctx → Tm 0 → Tm 0 → Tm 0 → Prop
  | hyp {Γ : Ctx} {A a b : Tm 0} (h : (⟨Γ, A, a, b⟩ : Jdg) ∈ H) :
      JEqH H Γ A a b
  -- Context well-formedness
  | nil_ok : JEqH H .nil .unit .star .star
  | cons_ok {Γ : Ctx} {x : String} {A : Tm 0} {n : ℕ}
    (hΓ : JEqH H Γ .unit .star .star) (hx : x ∉ Γ.dv) (hA : JEqH H Γ (.univ n) A A)
    : JEqH H (Γ.cons x A) .unit .star .star
  -- Variables and constants
  | var {Γ : Ctx} {x : String} {A : Tm 0} (hΓ : JEqH H Γ .unit .star .star) (hx : Γ.Lookup x A)
    : JEqH H Γ A (.fv x) (.fv x)
  | univ {Γ : Ctx} {n : ℕ} (hΓ : JEqH H Γ .unit .star .star)
    : JEqH H Γ (.univ (n + 1)) (.univ n) (.univ n)
  | empty {Γ : Ctx} {n : ℕ} (hΓ : JEqH H Γ .unit .star .star) : JEqH H Γ (.univ n) .empty .empty
  | unit {Γ : Ctx} {n : ℕ} (hΓ : JEqH H Γ .unit .star .star) : JEqH H Γ (.univ n) .unit .unit
  | nats {Γ : Ctx} {n : ℕ} (hΓ : JEqH H Γ .unit .star .star) : JEqH H Γ (.univ n) .nats .nats
  | zero {Γ : Ctx} (hΓ : JEqH H Γ .unit .star .star) : JEqH H Γ .nats .zero .zero
  -- Congruence
  | succ {Γ : Ctx} {m m' : Tm 0} (h : JEqH H Γ .nats m m') : JEqH H Γ .nats (.succ m) (.succ m')
  | pi {Γ : Ctx} {n : ℕ} {A A' : Tm 0} {B B' : Tm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
    : JEqH H Γ (.univ n) (.pi A B) (.pi A' B')
  | sigma {Γ : Ctx} {n : ℕ} {A A' : Tm 0} {B B' : Tm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
    : JEqH H Γ (.univ n) (.sigma A B) (.sigma A' B')
  | id {Γ : Ctx} {n : ℕ} {A A' a a' b b' : Tm 0}
    (hA : JEqH H Γ (.univ n) A A') (ha : JEqH H Γ A a a') (hb : JEqH H Γ A b b')
    : JEqH H Γ (.univ n) (.id A a b) (.id A' a' b')
  | abs {Γ : Ctx} {n : ℕ} {A A' : Tm 0} {B b b' : Tm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hb : ∀ x ∉ L, JEqH H (Γ.cons x A) (B.open x) (b.open x) (b'.open x))
    : JEqH H Γ (.pi A B) (.abs A b) (.abs A' b')
  | app {Γ : Ctx} {n : ℕ} {A f f' a a' : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : JEqH H Γ (.pi A B) f f') (ha : JEqH H Γ A a a')
    : JEqH H Γ (B.lst a) (.app f a) (.app f' a')
  | pair {Γ : Ctx} {n : ℕ} {A a a' b b' : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEqH H Γ A a a') (hb : JEqH H Γ (B.lst a) b b')
    : JEqH H Γ (.sigma A B) (.pair a b) (.pair a' b')
  | fst {Γ : Ctx} {n : ℕ} {A p p' : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEqH H Γ (.sigma A B) p p')
    : JEqH H Γ A (.fst p) (.fst p')
  | snd {Γ : Ctx} {n : ℕ} {A p p' : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEqH H Γ (.sigma A B) p p')
    : JEqH H Γ (B.lst (.fst p)) (.snd p) (.snd p')
  | natrec {Γ : Ctx} {n : ℕ} {C C' s s' : Tm 1} {z z' m m' : Tm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEqH H (Γ.cons x .nats) (.univ n) (C.open x) (C'.open x))
    (hz : JEqH H Γ (C.lst .zero) z z')
    (hs : ∀ x ∉ L, JEqH H (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s'.open x))
    (hm : JEqH H Γ .nats m m')
    : JEqH H Γ (C.lst m) (.natrec C s z m) (.natrec C' s' z' m')
  | refl {Γ : Ctx} {A a a' : Tm 0} (ha : JEqH H Γ A a a') : JEqH H Γ (.id A a a) (.refl a) (.refl a')
  | absurd {Γ : Ctx} {n : ℕ} {C C' e e' : Tm 0}
    (hC : JEqH H Γ (.univ n) C C') (he : JEqH H Γ .empty e e')
    : JEqH H Γ C (.absurd C e) (.absurd C' e')
  -- Computation
  | beta_app {Γ : Ctx} {n : ℕ} {A a : Tm 0} {B b : Tm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hb : ∀ x ∉ L, JEqH H (Γ.cons x A) (B.open x) (b.open x) (b.open x))
    (ha : JEqH H Γ A a a)
    : JEqH H Γ (B.lst a) (.app (.abs A b) a) (b.lst a)
  | beta_fst {Γ : Ctx} {n : ℕ} {A a b : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEqH H Γ A a a) (hb : JEqH H Γ (B.lst a) b b)
    : JEqH H Γ A (.fst (.pair a b)) a
  | beta_snd {Γ : Ctx} {n : ℕ} {A a b : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEqH H Γ A a a) (hb : JEqH H Γ (B.lst a) b b)
    : JEqH H Γ (B.lst a) (.snd (.pair a b)) b
  | beta_natrec_zero {Γ : Ctx} {n : ℕ} {C s : Tm 1} {z : Tm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEqH H (Γ.cons x .nats) (.univ n) (C.open x) (C.open x))
    (hz : JEqH H Γ (C.lst .zero) z z)
    (hs : ∀ x ∉ L, JEqH H (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s.open x))
    : JEqH H Γ (C.lst .zero) (.natrec C s z .zero) z
  | beta_natrec_succ {Γ : Ctx} {n : ℕ} {C s : Tm 1} {z m : Tm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEqH H (Γ.cons x .nats) (.univ n) (C.open x) (C.open x))
    (hz : JEqH H Γ (C.lst .zero) z z)
    (hs : ∀ x ∉ L, JEqH H (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s.open x))
    (hm : JEqH H Γ .nats m m)
    : JEqH H Γ (C.lst (.succ m)) (.natrec C s z (.succ m)) (.app (s.lst m) (.natrec C s z m))
  -- Extensionality
  | reflect {Γ : Ctx} {A a b p : Tm 0} (ha : JEqH H Γ A a a) (hb : JEqH H Γ A b b)
    (hp : JEqH H Γ (.id A a b) p p) : JEqH H Γ A a b
  | id_uip {Γ : Ctx} {A a b p : Tm 0} (ha : JEqH H Γ A a a) (hb : JEqH H Γ A b b)
    (hp : JEqH H Γ (.id A a b) p p) : JEqH H Γ (.id A a b) p (.refl a)
  | unit_ext {Γ : Ctx} {a : Tm 0} (ha : JEqH H Γ .unit a a) : JEqH H Γ .unit a .star
  | pi_ext {Γ : Ctx} {n : ℕ} {A f g : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : JEqH H Γ (.pi A B) f f) (hg : JEqH H Γ (.pi A B) g g)
    (hfg : ∀ x ∉ L, JEqH H (Γ.cons x A) (B.open x) (.app f (.fv x)) (.app g (.fv x)))
    : JEqH H Γ (.pi A B) f g
  | sigma_ext {Γ : Ctx} {n : ℕ} {A p q : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEqH H Γ (.sigma A B) p p) (hq : JEqH H Γ (.sigma A B) q q)
    (h1 : JEqH H Γ A (.fst p) (.fst q)) (h2 : JEqH H Γ (B.lst (.fst p)) (.snd p) (.snd q))
    : JEqH H Γ (.sigma A B) p q
  -- Equivalence, conversion and cumulativity
  | symm {Γ : Ctx} {A a b : Tm 0} (h : JEqH H Γ A a b) : JEqH H Γ A b a
  | trans {Γ : Ctx} {A a b c : Tm 0} (hab : JEqH H Γ A a b) (hbc : JEqH H Γ A b c) : JEqH H Γ A a c
  | conv {Γ : Ctx} {n : ℕ} {A A' a a' : Tm 0} (hA : JEqH H Γ (.univ n) A A') (ha : JEqH H Γ A a a')
    : JEqH H Γ A' a a'
  | cumul {Γ : Ctx} {m n : ℕ} {A A' : Tm 0} (hmn : m ≤ n) (hA : JEqH H Γ (.univ m) A A')
    : JEqH H Γ (.univ n) A A'
  -- W formation, introduction, dependent elimination and computation.
  | wtype {Γ : Ctx} {n : ℕ} {A A' : Tm 0} {B B' : Tm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
    : JEqH H Γ (.univ n) (.wtype A B) (.wtype A' B')
  | sup {Γ : Ctx} {n : ℕ} {A a a' f f' : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEqH H Γ A a a') (hf : JEqH H Γ (arr (B.lst a) (.wtype A B)) f f')
    : JEqH H Γ (.wtype A B) (.sup A B a f) (.sup A B a' f')
  | wrec {Γ : Ctx} {n m : ℕ} {A s s' t t' : Tm 0} {B C C' : Tm 1}
    {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, JEqH H (Γ.cons x (.wtype A B)) (.univ m) (C.open x) (C'.open x))
    (hs : JEqH H Γ (wStepType A B C) s s') (ht : JEqH H Γ (.wtype A B) t t')
    : JEqH H Γ (C.lst t) (.wrec A B C s t) (.wrec A B C' s' t')
  | beta_wrec {Γ : Ctx} {n m : ℕ} {A s a f : Tm 0} {B C : Tm 1}
    {L : Finset String}
    (hA : JEqH H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqH H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, JEqH H (Γ.cons x (.wtype A B)) (.univ m) (C.open x) (C.open x))
    (hs : JEqH H Γ (wStepType A B C) s s)
    (ha : JEqH H Γ A a a) (hf : JEqH H Γ (arr (B.lst a) (.wtype A B)) f f)
    : JEqH H Γ (C.lst (.sup A B a f)) (.wrec A B C s (.sup A B a f))
        (.app (.app (.app s a) f) (recChildren A B C s a f))

/-- Derivability with no judgment hypotheses. -/
abbrev Ctx.JEq : Ctx → Tm 0 → Tm 0 → Tm 0 → Prop := Ctx.JEqH ∅

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
