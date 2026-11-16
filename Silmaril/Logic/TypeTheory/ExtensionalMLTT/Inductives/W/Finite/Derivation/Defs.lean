module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Rules.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.RuleBudget.Defs

@[expose] public section

/-!
# Uniformly universe-bounded extensional MLTT derivations

`JEqB levels H` retains every rule of `JEqH`, including equality reflection,
UIP and extensionality. Every explicit universe parameter used anywhere in a
rule is below `levels`; the universe rule also bounds its successor. The same
bound applies to every member of each cofinite premise family.

Hypotheses are arbitrary judgments, with validity supplied by the soundness
contract. The finite institution uses bounded sentences for its theories.
A bounded conclusion alone is not evidence of a bounded derivation. Nor do we
assert every cofinite `JEqH` derivation has a uniform finite bound.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Tm in
/-- All extensional MLTT rules with a common bound on their universe parameters. -/
inductive Ctx.JEqB (levels : RuleBudget) (H : Set Jdg) : Ctx → Tm 0 → Tm 0 → Tm 0 → Prop
  | hyp {Γ : Ctx} {A a b : Tm 0} (h : (⟨Γ, A, a, b⟩ : Jdg) ∈ H) :
      JEqB levels H Γ A a b
  -- Context well-formedness
  | nil_ok : JEqB levels H .nil .unit .star .star
  | cons_ok {Γ : Ctx} {x : String} {A : Tm 0} {n : ℕ} (hn : RuleBudget.Allows levels n)
    (hΓ : JEqB levels H Γ .unit .star .star) (hx : x ∉ Γ.dv) (hA : JEqB levels H Γ (.univ n) A A)
    : JEqB levels H (Γ.cons x A) .unit .star .star
  -- Variables and constants
  | var {Γ : Ctx} {x : String} {A : Tm 0} (hΓ : JEqB levels H Γ .unit .star .star) (hx : Γ.Lookup x A)
    : JEqB levels H Γ A (.fv x) (.fv x)
  | univ {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels (n + 1)) (hΓ : JEqB levels H Γ .unit .star .star)
    : JEqB levels H Γ (.univ (n + 1)) (.univ n) (.univ n)
  | empty {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) (hΓ : JEqB levels H Γ .unit .star .star) : JEqB levels H Γ (.univ n) .empty .empty
  | unit {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) (hΓ : JEqB levels H Γ .unit .star .star) : JEqB levels H Γ (.univ n) .unit .unit
  | nats {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) (hΓ : JEqB levels H Γ .unit .star .star) : JEqB levels H Γ (.univ n) .nats .nats
  | zero {Γ : Ctx} (hΓ : JEqB levels H Γ .unit .star .star) : JEqB levels H Γ .nats .zero .zero
  -- Congruence
  | succ {Γ : Ctx} {m m' : Tm 0} (h : JEqB levels H Γ .nats m m') : JEqB levels H Γ .nats (.succ m) (.succ m')
  | pi {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A A' : Tm 0} {B B' : Tm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
    : JEqB levels H Γ (.univ n) (.pi A B) (.pi A' B')
  | sigma {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A A' : Tm 0} {B B' : Tm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
    : JEqB levels H Γ (.univ n) (.sigma A B) (.sigma A' B')
  | id {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A A' a a' b b' : Tm 0}
    (hA : JEqB levels H Γ (.univ n) A A') (ha : JEqB levels H Γ A a a') (hb : JEqB levels H Γ A b b')
    : JEqB levels H Γ (.univ n) (.id A a b) (.id A' a' b')
  | abs {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A A' : Tm 0} {B b b' : Tm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hb : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (B.open x) (b.open x) (b'.open x))
    : JEqB levels H Γ (.pi A B) (.abs A b) (.abs A' b')
  | app {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A f f' a a' : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : JEqB levels H Γ (.pi A B) f f') (ha : JEqB levels H Γ A a a')
    : JEqB levels H Γ (B.lst a) (.app f a) (.app f' a')
  | pair {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A a a' b b' : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEqB levels H Γ A a a') (hb : JEqB levels H Γ (B.lst a) b b')
    : JEqB levels H Γ (.sigma A B) (.pair a b) (.pair a' b')
  | fst {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A p p' : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEqB levels H Γ (.sigma A B) p p')
    : JEqB levels H Γ A (.fst p) (.fst p')
  | snd {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A p p' : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEqB levels H Γ (.sigma A B) p p')
    : JEqB levels H Γ (B.lst (.fst p)) (.snd p) (.snd p')
  | natrec {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {C C' s s' : Tm 1} {z z' m m' : Tm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEqB levels H (Γ.cons x .nats) (.univ n) (C.open x) (C'.open x))
    (hz : JEqB levels H Γ (C.lst .zero) z z')
    (hs : ∀ x ∉ L, JEqB levels H (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s'.open x))
    (hm : JEqB levels H Γ .nats m m')
    : JEqB levels H Γ (C.lst m) (.natrec C s z m) (.natrec C' s' z' m')
  | refl {Γ : Ctx} {A a a' : Tm 0} (ha : JEqB levels H Γ A a a') : JEqB levels H Γ (.id A a a) (.refl a) (.refl a')
  | absurd {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {C C' e e' : Tm 0}
    (hC : JEqB levels H Γ (.univ n) C C') (he : JEqB levels H Γ .empty e e')
    : JEqB levels H Γ C (.absurd C e) (.absurd C' e')
  -- Computation
  | beta_app {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A a : Tm 0} {B b : Tm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hb : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (B.open x) (b.open x) (b.open x))
    (ha : JEqB levels H Γ A a a)
    : JEqB levels H Γ (B.lst a) (.app (.abs A b) a) (b.lst a)
  | beta_fst {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A a b : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEqB levels H Γ A a a) (hb : JEqB levels H Γ (B.lst a) b b)
    : JEqB levels H Γ A (.fst (.pair a b)) a
  | beta_snd {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A a b : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEqB levels H Γ A a a) (hb : JEqB levels H Γ (B.lst a) b b)
    : JEqB levels H Γ (B.lst a) (.snd (.pair a b)) b
  | beta_natrec_zero {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {C s : Tm 1} {z : Tm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEqB levels H (Γ.cons x .nats) (.univ n) (C.open x) (C.open x))
    (hz : JEqB levels H Γ (C.lst .zero) z z)
    (hs : ∀ x ∉ L, JEqB levels H (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s.open x))
    : JEqB levels H Γ (C.lst .zero) (.natrec C s z .zero) z
  | beta_natrec_succ {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {C s : Tm 1} {z m : Tm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEqB levels H (Γ.cons x .nats) (.univ n) (C.open x) (C.open x))
    (hz : JEqB levels H Γ (C.lst .zero) z z)
    (hs : ∀ x ∉ L, JEqB levels H (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s.open x))
    (hm : JEqB levels H Γ .nats m m)
    : JEqB levels H Γ (C.lst (.succ m)) (.natrec C s z (.succ m)) (.app (s.lst m) (.natrec C s z m))
  -- Extensionality
  | reflect {Γ : Ctx} {A a b p : Tm 0} (ha : JEqB levels H Γ A a a) (hb : JEqB levels H Γ A b b)
    (hp : JEqB levels H Γ (.id A a b) p p) : JEqB levels H Γ A a b
  | id_uip {Γ : Ctx} {A a b p : Tm 0} (ha : JEqB levels H Γ A a a) (hb : JEqB levels H Γ A b b)
    (hp : JEqB levels H Γ (.id A a b) p p) : JEqB levels H Γ (.id A a b) p (.refl a)
  | unit_ext {Γ : Ctx} {a : Tm 0} (ha : JEqB levels H Γ .unit a a) : JEqB levels H Γ .unit a .star
  | pi_ext {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A f g : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : JEqB levels H Γ (.pi A B) f f) (hg : JEqB levels H Γ (.pi A B) g g)
    (hfg : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (B.open x) (.app f (.fv x)) (.app g (.fv x)))
    : JEqB levels H Γ (.pi A B) f g
  | sigma_ext {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A p q : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEqB levels H Γ (.sigma A B) p p) (hq : JEqB levels H Γ (.sigma A B) q q)
    (h1 : JEqB levels H Γ A (.fst p) (.fst q)) (h2 : JEqB levels H Γ (B.lst (.fst p)) (.snd p) (.snd q))
    : JEqB levels H Γ (.sigma A B) p q
  -- Equivalence, conversion and cumulativity
  | symm {Γ : Ctx} {A a b : Tm 0} (h : JEqB levels H Γ A a b) : JEqB levels H Γ A b a
  | trans {Γ : Ctx} {A a b c : Tm 0} (hab : JEqB levels H Γ A a b) (hbc : JEqB levels H Γ A b c) : JEqB levels H Γ A a c
  | conv {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A A' a a' : Tm 0} (hA : JEqB levels H Γ (.univ n) A A') (ha : JEqB levels H Γ A a a')
    : JEqB levels H Γ A' a a'
  | cumul {Γ : Ctx} {m n : ℕ} (hn : RuleBudget.Allows levels n) {A A' : Tm 0} (hmn : m ≤ n) (hA : JEqB levels H Γ (.univ m) A A')
    : JEqB levels H Γ (.univ n) A A'

  -- W formation, introduction, dependent elimination and computation.
  | wtype {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A A' : Tm 0} {B B' : Tm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
    : JEqB levels H Γ (.univ n) (.wtype A B) (.wtype A' B')
  | sup {Γ : Ctx} {n : ℕ} (hn : RuleBudget.Allows levels n) {A a a' f f' : Tm 0} {B : Tm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEqB levels H Γ A a a') (hf : JEqB levels H Γ (arr (B.lst a) (.wtype A B)) f f')
    : JEqB levels H Γ (.wtype A B) (.sup A B a f) (.sup A B a' f')
  | wrec {Γ : Ctx} {n m : ℕ} (hn : RuleBudget.Allows levels n) (hm : RuleBudget.Allows levels m) {A s s' t t' : Tm 0} {B C C' : Tm 1}
    {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, JEqB levels H (Γ.cons x (.wtype A B)) (.univ m) (C.open x) (C'.open x))
    (hs : JEqB levels H Γ (wStepType A B C) s s') (ht : JEqB levels H Γ (.wtype A B) t t')
    : JEqB levels H Γ (C.lst t) (.wrec A B C s t) (.wrec A B C' s' t')
  | beta_wrec {Γ : Ctx} {n m : ℕ} (hn : RuleBudget.Allows levels n) (hm : RuleBudget.Allows levels m) {A s a f : Tm 0} {B C : Tm 1}
    {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hC : ∀ x ∉ L, JEqB levels H (Γ.cons x (.wtype A B)) (.univ m) (C.open x) (C.open x))
    (hs : JEqB levels H Γ (wStepType A B C) s s)
    (ha : JEqB levels H Γ A a a) (hf : JEqB levels H Γ (arr (B.lst a) (.wtype A B)) f f)
    : JEqB levels H Γ (C.lst (.sup A B a f)) (.wrec A B C s (.sup A B a f))
        (.app (.app (.app s a) f) (recChildren A B C s a f))


end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
