module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Derivation
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Defs

@[expose] public section

/-!
# Uniformly universe-bounded extensional MLTT derivations

`JEqB levels H` retains every rule of `JEqH`, including equality reflection,
UIP and extensionality. Every explicit universe parameter used anywhere in a
rule is below `levels`; the universe rule also bounds its successor. The same
bound applies to every member of each cofinite premise family.

Hypotheses remain arbitrary judgments. Bounds on their sentence syntax are
separate premises; `Finite.Sentence` provides those when needed. A bounded
conclusion alone is not evidence of a bounded derivation. We do not assert
that every cofinite `JEqH` proof has a uniform finite bound. Finite-tower
soundness is proved in `Finite.Soundness`; the source `ExtensionalHeight`
API proves fixed successor-height intensional-to-extensional preservation.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

open ETm in
/-- All extensional MLTT rules with a common bound on their universe parameters. -/
inductive ECtx.JEqB (levels : ℕ) (H : Set EJdg) : ECtx → ETm 0 → ETm 0 → ETm 0 → Prop
  | hyp {Γ : ECtx} {A a b : ETm 0} (h : (⟨Γ, A, a, b⟩ : EJdg) ∈ H) :
      JEqB levels H Γ A a b
  -- Context well-formedness
  | nil_ok : JEqB levels H .nil .unit .star .star
  | cons_ok {Γ : ECtx} {x : String} {A : ETm 0} {n : ℕ} (hn : n < levels)
    (hΓ : JEqB levels H Γ .unit .star .star) (hx : x ∉ Γ.dv) (hA : JEqB levels H Γ (.univ n) A A)
    : JEqB levels H (Γ.cons x A) .unit .star .star
  -- Variables and constants
  | var {Γ : ECtx} {x : String} {A : ETm 0} (hΓ : JEqB levels H Γ .unit .star .star) (hx : Γ.Lookup x A)
    : JEqB levels H Γ A (.fv x) (.fv x)
  | univ {Γ : ECtx} {n : ℕ} (hn : n + 1 < levels) (hΓ : JEqB levels H Γ .unit .star .star)
    : JEqB levels H Γ (.univ (n + 1)) (.univ n) (.univ n)
  | empty {Γ : ECtx} {n : ℕ} (hn : n < levels) (hΓ : JEqB levels H Γ .unit .star .star) : JEqB levels H Γ (.univ n) .empty .empty
  | unit {Γ : ECtx} {n : ℕ} (hn : n < levels) (hΓ : JEqB levels H Γ .unit .star .star) : JEqB levels H Γ (.univ n) .unit .unit
  | nats {Γ : ECtx} {n : ℕ} (hn : n < levels) (hΓ : JEqB levels H Γ .unit .star .star) : JEqB levels H Γ (.univ n) .nats .nats
  | zero {Γ : ECtx} (hΓ : JEqB levels H Γ .unit .star .star) : JEqB levels H Γ .nats .zero .zero
  -- Congruence
  | succ {Γ : ECtx} {m m' : ETm 0} (h : JEqB levels H Γ .nats m m') : JEqB levels H Γ .nats (.succ m) (.succ m')
  | pi {Γ : ECtx} {n : ℕ} (hn : n < levels) {A A' : ETm 0} {B B' : ETm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
    : JEqB levels H Γ (.univ n) (.pi A B) (.pi A' B')
  | sigma {Γ : ECtx} {n : ℕ} (hn : n < levels) {A A' : ETm 0} {B B' : ETm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B'.open x))
    : JEqB levels H Γ (.univ n) (.sigma A B) (.sigma A' B')
  | id {Γ : ECtx} {n : ℕ} (hn : n < levels) {A A' a a' b b' : ETm 0}
    (hA : JEqB levels H Γ (.univ n) A A') (ha : JEqB levels H Γ A a a') (hb : JEqB levels H Γ A b b')
    : JEqB levels H Γ (.univ n) (.id A a b) (.id A' a' b')
  | abs {Γ : ECtx} {n : ℕ} (hn : n < levels) {A A' : ETm 0} {B b b' : ETm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A')
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hb : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (B.open x) (b.open x) (b'.open x))
    : JEqB levels H Γ (.pi A B) (.abs A b) (.abs A' b')
  | app {Γ : ECtx} {n : ℕ} (hn : n < levels) {A f f' a a' : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : JEqB levels H Γ (.pi A B) f f') (ha : JEqB levels H Γ A a a')
    : JEqB levels H Γ (B.lst a) (.app f a) (.app f' a')
  | pair {Γ : ECtx} {n : ℕ} (hn : n < levels) {A a a' b b' : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEqB levels H Γ A a a') (hb : JEqB levels H Γ (B.lst a) b b')
    : JEqB levels H Γ (.sigma A B) (.pair a b) (.pair a' b')
  | fst {Γ : ECtx} {n : ℕ} (hn : n < levels) {A p p' : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEqB levels H Γ (.sigma A B) p p')
    : JEqB levels H Γ A (.fst p) (.fst p')
  | snd {Γ : ECtx} {n : ℕ} (hn : n < levels) {A p p' : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEqB levels H Γ (.sigma A B) p p')
    : JEqB levels H Γ (B.lst (.fst p)) (.snd p) (.snd p')
  | natrec {Γ : ECtx} {n : ℕ} (hn : n < levels) {C C' s s' : ETm 1} {z z' m m' : ETm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEqB levels H (Γ.cons x .nats) (.univ n) (C.open x) (C'.open x))
    (hz : JEqB levels H Γ (C.lst .zero) z z')
    (hs : ∀ x ∉ L, JEqB levels H (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s'.open x))
    (hm : JEqB levels H Γ .nats m m')
    : JEqB levels H Γ (C.lst m) (.natrec C s z m) (.natrec C' s' z' m')
  | refl {Γ : ECtx} {A a a' : ETm 0} (ha : JEqB levels H Γ A a a') : JEqB levels H Γ (.id A a a) (.refl a) (.refl a')
  | absurd {Γ : ECtx} {n : ℕ} (hn : n < levels) {C C' e e' : ETm 0}
    (hC : JEqB levels H Γ (.univ n) C C') (he : JEqB levels H Γ .empty e e')
    : JEqB levels H Γ C (.absurd C e) (.absurd C' e')
  -- Computation
  | beta_app {Γ : ECtx} {n : ℕ} (hn : n < levels) {A a : ETm 0} {B b : ETm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hb : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (B.open x) (b.open x) (b.open x))
    (ha : JEqB levels H Γ A a a)
    : JEqB levels H Γ (B.lst a) (.app (.abs A b) a) (b.lst a)
  | beta_fst {Γ : ECtx} {n : ℕ} (hn : n < levels) {A a b : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEqB levels H Γ A a a) (hb : JEqB levels H Γ (B.lst a) b b)
    : JEqB levels H Γ A (.fst (.pair a b)) a
  | beta_snd {Γ : ECtx} {n : ℕ} (hn : n < levels) {A a b : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (ha : JEqB levels H Γ A a a) (hb : JEqB levels H Γ (B.lst a) b b)
    : JEqB levels H Γ (B.lst a) (.snd (.pair a b)) b
  | beta_natrec_zero {Γ : ECtx} {n : ℕ} (hn : n < levels) {C s : ETm 1} {z : ETm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEqB levels H (Γ.cons x .nats) (.univ n) (C.open x) (C.open x))
    (hz : JEqB levels H Γ (C.lst .zero) z z)
    (hs : ∀ x ∉ L, JEqB levels H (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s.open x))
    : JEqB levels H Γ (C.lst .zero) (.natrec C s z .zero) z
  | beta_natrec_succ {Γ : ECtx} {n : ℕ} (hn : n < levels) {C s : ETm 1} {z m : ETm 0} {L : Finset String}
    (hC : ∀ x ∉ L, JEqB levels H (Γ.cons x .nats) (.univ n) (C.open x) (C.open x))
    (hz : JEqB levels H Γ (C.lst .zero) z z)
    (hs : ∀ x ∉ L, JEqB levels H (Γ.cons x .nats) (arr (C.open x) (C.lst (.succ (.fv x))))
      (s.open x) (s.open x))
    (hm : JEqB levels H Γ .nats m m)
    : JEqB levels H Γ (C.lst (.succ m)) (.natrec C s z (.succ m)) (.app (s.lst m) (.natrec C s z m))
  -- Extensionality
  | reflect {Γ : ECtx} {A a b p : ETm 0} (ha : JEqB levels H Γ A a a) (hb : JEqB levels H Γ A b b)
    (hp : JEqB levels H Γ (.id A a b) p p) : JEqB levels H Γ A a b
  | id_uip {Γ : ECtx} {A a b p : ETm 0} (ha : JEqB levels H Γ A a a) (hb : JEqB levels H Γ A b b)
    (hp : JEqB levels H Γ (.id A a b) p p) : JEqB levels H Γ (.id A a b) p (.refl a)
  | unit_ext {Γ : ECtx} {a : ETm 0} (ha : JEqB levels H Γ .unit a a) : JEqB levels H Γ .unit a .star
  | pi_ext {Γ : ECtx} {n : ℕ} (hn : n < levels) {A f g : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : JEqB levels H Γ (.pi A B) f f) (hg : JEqB levels H Γ (.pi A B) g g)
    (hfg : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (B.open x) (.app f (.fv x)) (.app g (.fv x)))
    : JEqB levels H Γ (.pi A B) f g
  | sigma_ext {Γ : ECtx} {n : ℕ} (hn : n < levels) {A p q : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : JEqB levels H Γ (.univ n) A A)
    (hB : ∀ x ∉ L, JEqB levels H (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hp : JEqB levels H Γ (.sigma A B) p p) (hq : JEqB levels H Γ (.sigma A B) q q)
    (h1 : JEqB levels H Γ A (.fst p) (.fst q)) (h2 : JEqB levels H Γ (B.lst (.fst p)) (.snd p) (.snd q))
    : JEqB levels H Γ (.sigma A B) p q
  -- Equivalence, conversion and cumulativity
  | symm {Γ : ECtx} {A a b : ETm 0} (h : JEqB levels H Γ A a b) : JEqB levels H Γ A b a
  | trans {Γ : ECtx} {A a b c : ETm 0} (hab : JEqB levels H Γ A a b) (hbc : JEqB levels H Γ A b c) : JEqB levels H Γ A a c
  | conv {Γ : ECtx} {n : ℕ} (hn : n < levels) {A A' a a' : ETm 0} (hA : JEqB levels H Γ (.univ n) A A') (ha : JEqB levels H Γ A a a')
    : JEqB levels H Γ A' a a'
  | cumul {Γ : ECtx} {m n : ℕ} (hn : n < levels) {A A' : ETm 0} (hmn : m ≤ n) (hA : JEqB levels H Γ (.univ m) A A')
    : JEqB levels H Γ (.univ n) A A'


end Silmaril.Logic.TypeTheory.ExtensionalMLTT
