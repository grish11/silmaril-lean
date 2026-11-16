module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Structural

@[expose] public section

/-!
# Intensional beta conversion and typing rules

Conversion is the congruence/equivalence closure of computational beta laws.
The typing rules include cumulative Russell universes and intensional Id/J.
They include neither equality reflection, UIP nor judgmental eta rules.
Semantic soundness, admissible substitution and normalization are subsequent
metatheorems, rather than fields assumed by this definition.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Intensional beta conversion, closed under every term constructor. -/
inductive Conversion : {n : ℕ} → Term n → Term n → Type
  | refl {n : ℕ} (t : Term n) : Conversion t t
  | symm {n : ℕ} {t u : Term n} (h : Conversion t u) : Conversion u t
  | trans {n : ℕ} {t u v : Term n} (h : Conversion t u) (k : Conversion u v) : Conversion t v
  | beta {n : ℕ} (A : Term n) (body : Term (n + 1)) (a : Term n) :
      Conversion (.app (.lam A body) a) (body.instantiate a)
  | fst_pair {n : ℕ} (a b : Term n) : Conversion (.fst (.pair a b)) a
  | snd_pair {n : ℕ} (a b : Term n) : Conversion (.snd (.pair a b)) b
  | nat_zero {n : ℕ} (C : Term (n + 1)) (z s : Term n) :
      Conversion (.natrec C z s .zero) z
  | nat_succ {n : ℕ} (C : Term (n + 1)) (z s t : Term n) :
      Conversion (.natrec C z s (.succ t)) (.app (.app s t) (.natrec C z s t))
  | j_refl {n : ℕ} (A a : Term n) (C : Term (n + 2)) (d : Term n) :
      Conversion (.j A a C d a (.refl a)) d
  | congr_succ {n : ℕ} {t t' : Term n}
      (ht: Conversion t t') :
      Conversion (.succ t) (.succ t')
  | congr_pi {n : ℕ} {A A' : Term n} {B B' : Term (n + 1)}
      (hA: Conversion A A') (hB: Conversion B B') :
      Conversion (.pi A B) (.pi A' B')
  | congr_sigma {n : ℕ} {A A' : Term n} {B B' : Term (n + 1)}
      (hA: Conversion A A') (hB: Conversion B B') :
      Conversion (.sigma A B) (.sigma A' B')
  | congr_lam {n : ℕ} {A A' : Term n} {body body' : Term (n + 1)}
      (hA: Conversion A A') (hbody: Conversion body body') :
      Conversion (.lam A body) (.lam A' body')
  | congr_app {n : ℕ} {f f' : Term n} {a a' : Term n}
      (hf: Conversion f f') (ha: Conversion a a') :
      Conversion (.app f a) (.app f' a')
  | congr_pair {n : ℕ} {a a' : Term n} {b b' : Term n}
      (ha: Conversion a a') (hb: Conversion b b') :
      Conversion (.pair a b) (.pair a' b')
  | congr_fst {n : ℕ} {p p' : Term n}
      (hp: Conversion p p') :
      Conversion (.fst p) (.fst p')
  | congr_snd {n : ℕ} {p p' : Term n}
      (hp: Conversion p p') :
      Conversion (.snd p) (.snd p')
  | congr_natrec {n : ℕ} {C C' : Term (n + 1)} {z z' : Term n} {s s' : Term n} {t t' : Term n}
      (hC: Conversion C C') (hz: Conversion z z') (hs: Conversion s s') (ht: Conversion t t') :
      Conversion (.natrec C z s t) (.natrec C' z' s' t')
  | congr_absurd {n : ℕ} {A A' : Term n} {e e' : Term n}
      (hA: Conversion A A') (he: Conversion e e') :
      Conversion (.absurd A e) (.absurd A' e')
  | congr_id {n : ℕ} {A A' : Term n} {a a' : Term n} {b b' : Term n}
      (hA: Conversion A A') (ha: Conversion a a') (hb: Conversion b b') :
      Conversion (.id A a b) (.id A' a' b')
  | congr_refl {n : ℕ} {a a' : Term n}
      (ha: Conversion a a') :
      Conversion (.refl a) (.refl a')
  | congr_j {n : ℕ} {A A' : Term n} {a a' : Term n} {C C' : Term (n + 2)} {d d' : Term n} {b b' : Term n} {p p' : Term n}
      (hA: Conversion A A') (ha: Conversion a a') (hC: Conversion C C') (hd: Conversion d d') (hb: Conversion b b') (hp: Conversion p p') :
      Conversion (.j A a C d b p) (.j A' a' C' d' b' p')

namespace Term

/-- Type of the ordinary step function for a motive scoped over a natural. -/
def natStepType {n : ℕ} (C : Term (n + 1)) : Term n :=
  .pi .nat (.pi C (C.subst (Fin.cons (.succ (.var 1)) (fun i => .var i.succ.succ))))

end Term

/-- The context of an endpoint and a path from the fixed left endpoint. -/
def motiveContext {n : ℕ} (Γ : Context n) (A a : Term n) : Context (n + 2) :=
  (Γ.snoc A).snoc (.id A.weaken a.weaken (.var 0))

mutual

/-- Well-formed telescopes; every declaration inhabits an explicit universe. -/
inductive ContextDerivation : {n : ℕ} → Context n → Type
  | nil : ContextDerivation .nil
  | snoc {n i : ℕ} {Γ : Context n} {A : Term n}
      (hΓ : ContextDerivation Γ) (hA : Derivation Γ A (.univ i)) : ContextDerivation (Γ.snoc A)

/-- Declarative typing for the beta-only cumulative intensional core. -/
inductive Derivation : {n : ℕ} → Context n → Term n → Term n → Type
  | univ {n : ℕ} {Γ : Context n} (hΓ : ContextDerivation Γ) (i : ℕ) :
      Derivation Γ (.univ i) (.univ (i + 1))
  | nat {n : ℕ} {Γ : Context n} (hΓ : ContextDerivation Γ) : Derivation Γ .nat (.univ 0)
  | empty {n : ℕ} {Γ : Context n} (hΓ : ContextDerivation Γ) : Derivation Γ .empty (.univ 0)
  | unit {n : ℕ} {Γ : Context n} (hΓ : ContextDerivation Γ) : Derivation Γ .unit (.univ 0)
  | var {n : ℕ} {Γ : Context n} {i : Fin n} {A : Term n}
      (hΓ : ContextDerivation Γ) (hi : Lookup Γ i A) : Derivation Γ (.var i) A
  | pi {n i j : ℕ} {Γ : Context n} {A : Term n} {B : Term (n + 1)}
      (hA : Derivation Γ A (.univ i)) (hB : Derivation (Γ.snoc A) B (.univ j)) :
      Derivation Γ (.pi A B) (.univ (max i j))
  | sigma {n i j : ℕ} {Γ : Context n} {A : Term n} {B : Term (n + 1)}
      (hA : Derivation Γ A (.univ i)) (hB : Derivation (Γ.snoc A) B (.univ j)) :
      Derivation Γ (.sigma A B) (.univ (max i j))
  | lam {n i j : ℕ} {Γ : Context n} {A : Term n} {B body : Term (n + 1)}
      (hA : Derivation Γ A (.univ i)) (hB : Derivation (Γ.snoc A) B (.univ j))
      (ht : Derivation (Γ.snoc A) body B) : Derivation Γ (.lam A body) (.pi A B)
  | app {n : ℕ} {Γ : Context n} {A f a : Term n} {B : Term (n + 1)}
      (hf : Derivation Γ f (.pi A B)) (ha : Derivation Γ a A) :
      Derivation Γ (.app f a) (B.instantiate a)
  | pair {n i j : ℕ} {Γ : Context n} {A a b : Term n} {B : Term (n + 1)}
      (hA : Derivation Γ A (.univ i)) (hB : Derivation (Γ.snoc A) B (.univ j))
      (ha : Derivation Γ a A) (hb : Derivation Γ b (B.instantiate a)) :
      Derivation Γ (.pair a b) (.sigma A B)
  | fst {n : ℕ} {Γ : Context n} {A p : Term n} {B : Term (n + 1)}
      (hp : Derivation Γ p (.sigma A B)) : Derivation Γ (.fst p) A
  | snd {n : ℕ} {Γ : Context n} {A p : Term n} {B : Term (n + 1)}
      (hp : Derivation Γ p (.sigma A B)) : Derivation Γ (.snd p) (B.instantiate (.fst p))
  | zero {n : ℕ} {Γ : Context n} (hΓ : ContextDerivation Γ) : Derivation Γ .zero .nat
  | succ {n : ℕ} {Γ : Context n} {t : Term n}
      (ht : Derivation Γ t .nat) : Derivation Γ (.succ t) .nat
  | natrec {n i : ℕ} {Γ : Context n} {C : Term (n + 1)} {z s t : Term n}
      (hC : Derivation (Γ.snoc .nat) C (.univ i))
      (hz : Derivation Γ z (C.instantiate .zero)) (hs : Derivation Γ s C.natStepType)
      (ht : Derivation Γ t .nat) : Derivation Γ (.natrec C z s t) (C.instantiate t)
  | star {n : ℕ} {Γ : Context n} (hΓ : ContextDerivation Γ) : Derivation Γ .star .unit
  | absurd {n i : ℕ} {Γ : Context n} {A e : Term n}
      (hA : Derivation Γ A (.univ i)) (he : Derivation Γ e .empty) : Derivation Γ (.absurd A e) A
  | id {n i : ℕ} {Γ : Context n} {A a b : Term n}
      (hA : Derivation Γ A (.univ i)) (ha : Derivation Γ a A) (hb : Derivation Γ b A) :
      Derivation Γ (.id A a b) (.univ i)
  | refl {n i : ℕ} {Γ : Context n} {A a : Term n}
      (hA : Derivation Γ A (.univ i)) (ha : Derivation Γ a A) : Derivation Γ (.refl a) (.id A a a)
  | j {n i j : ℕ} {Γ : Context n} {A a d b p : Term n} {C : Term (n + 2)}
      (hA : Derivation Γ A (.univ i)) (ha : Derivation Γ a A)
      (hC : Derivation (motiveContext Γ A a) C (.univ j))
      (hd : Derivation Γ d (C.instantiate₂ a (.refl a)))
      (hb : Derivation Γ b A) (hp : Derivation Γ p (.id A a b)) :
      Derivation Γ (.j A a C d b p) (C.instantiate₂ b p)
  | conv {n i : ℕ} {Γ : Context n} {t A B : Term n}
      (ht : Derivation Γ t A) (hB : Derivation Γ B (.univ i)) (hAB : Conversion A B) : Derivation Γ t B
  | cumulative {n i j : ℕ} {Γ : Context n} {A : Term n}
      (hA : Derivation Γ A (.univ i)) (hij : i ≤ j) : Derivation Γ A (.univ j)

end

/-- The context judgment forgets the proof-relevant derivation tree. -/
abbrev WellFormed {n : ℕ} (Γ : Context n) : Prop := Nonempty (ContextDerivation Γ)

/-- The typing proposition forgets the proof-relevant derivation tree. -/
abbrev Typing {n : ℕ} (Γ : Context n) (t A : Term n) : Prop := Nonempty (Derivation Γ t A)

/-- The conversion proposition forgets its computational equality tree. -/
abbrev Convertible {n : ℕ} (t u : Term n) : Prop := Nonempty (Conversion t u)

/-- Typed beta equality requires both endpoint typings as well as conversion. -/
def TypedEq {n : ℕ} (Γ : Context n) (t u A : Term n) : Prop :=
  Typing Γ t A ∧ Typing Γ u A ∧ Convertible t u

end Silmaril.Logic.TypeTheory.IntensionalMLTT
