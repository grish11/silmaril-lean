module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Budget

@[expose] public section

/-!
# The original cumulative calculus with typing hypotheses

Every constructor below is the unchanged original ContextDerivation/Derivation
rule, with the same terms, premises and raw Conversion. The added hyp leaf
assumes a scoped typing judgment. These are typing hypotheses, not hypothetical
raw conversion axioms or a new equality-reflection rule.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- A scoped original typing sentence, independent of a proof or universe cap. -/
structure ScopedTyping : Type where
  scope : ℕ
  Γ : Context scope
  term : Term scope
  carrier : Term scope

/-- Every universe occurrence in the full scoped typing judgment. -/
def ScopedTyping.universeBound (q : ScopedTyping) : ℕ :=
  max q.Γ.universeBound (max q.term.universeBound q.carrier.universeBound)

/-- The full scoped typing sentence uses at most the supplied universe count. -/
def ScopedTyping.UsesBelow (q : ScopedTyping) (levels : ℕ) : Prop :=
  q.universeBound ≤ levels

mutual

/-- Original well-formed telescopes with typing hypotheses available under every binder. -/
inductive ContextDerivationH (H : Set ScopedTyping) : {n : ℕ} → Context n → Type
  | nil : ContextDerivationH H .nil
  | snoc {n i : ℕ} {Γ : Context n} {A : Term n}
      (hΓ : ContextDerivationH H Γ) (hA : DerivationH H Γ A (.univ i)) : ContextDerivationH H (Γ.snoc A)

/-- Exactly the original typing rules, with explicit scoped typing-hypothesis leaves. -/
inductive DerivationH (H : Set ScopedTyping) : {n : ℕ} → Context n → Term n → Term n → Type
  | hyp {n : ℕ} {Γ : Context n} {t A : Term n}
      (h : (⟨n, Γ, t, A⟩ : ScopedTyping) ∈ H) : DerivationH H Γ t A
  | univ {n : ℕ} {Γ : Context n} (hΓ : ContextDerivationH H Γ) (i : ℕ) :
      DerivationH H Γ (.univ i) (.univ (i + 1))
  | nat {n : ℕ} {Γ : Context n} (hΓ : ContextDerivationH H Γ) : DerivationH H Γ .nat (.univ 0)
  | empty {n : ℕ} {Γ : Context n} (hΓ : ContextDerivationH H Γ) : DerivationH H Γ .empty (.univ 0)
  | unit {n : ℕ} {Γ : Context n} (hΓ : ContextDerivationH H Γ) : DerivationH H Γ .unit (.univ 0)
  | var {n : ℕ} {Γ : Context n} {i : Fin n} {A : Term n}
      (hΓ : ContextDerivationH H Γ) (hi : Lookup Γ i A) : DerivationH H Γ (.var i) A
  | pi {n i j : ℕ} {Γ : Context n} {A : Term n} {B : Term (n + 1)}
      (hA : DerivationH H Γ A (.univ i)) (hB : DerivationH H (Γ.snoc A) B (.univ j)) :
      DerivationH H Γ (.pi A B) (.univ (max i j))
  | sigma {n i j : ℕ} {Γ : Context n} {A : Term n} {B : Term (n + 1)}
      (hA : DerivationH H Γ A (.univ i)) (hB : DerivationH H (Γ.snoc A) B (.univ j)) :
      DerivationH H Γ (.sigma A B) (.univ (max i j))
  | lam {n i j : ℕ} {Γ : Context n} {A : Term n} {B body : Term (n + 1)}
      (hA : DerivationH H Γ A (.univ i)) (hB : DerivationH H (Γ.snoc A) B (.univ j))
      (ht : DerivationH H (Γ.snoc A) body B) : DerivationH H Γ (.lam A body) (.pi A B)
  | app {n : ℕ} {Γ : Context n} {A f a : Term n} {B : Term (n + 1)}
      (hf : DerivationH H Γ f (.pi A B)) (ha : DerivationH H Γ a A) :
      DerivationH H Γ (.app f a) (B.instantiate a)
  | pair {n i j : ℕ} {Γ : Context n} {A a b : Term n} {B : Term (n + 1)}
      (hA : DerivationH H Γ A (.univ i)) (hB : DerivationH H (Γ.snoc A) B (.univ j))
      (ha : DerivationH H Γ a A) (hb : DerivationH H Γ b (B.instantiate a)) :
      DerivationH H Γ (.pair a b) (.sigma A B)
  | fst {n : ℕ} {Γ : Context n} {A p : Term n} {B : Term (n + 1)}
      (hp : DerivationH H Γ p (.sigma A B)) : DerivationH H Γ (.fst p) A
  | snd {n : ℕ} {Γ : Context n} {A p : Term n} {B : Term (n + 1)}
      (hp : DerivationH H Γ p (.sigma A B)) : DerivationH H Γ (.snd p) (B.instantiate (.fst p))
  | zero {n : ℕ} {Γ : Context n} (hΓ : ContextDerivationH H Γ) : DerivationH H Γ .zero .nat
  | succ {n : ℕ} {Γ : Context n} {t : Term n}
      (ht : DerivationH H Γ t .nat) : DerivationH H Γ (.succ t) .nat
  | natrec {n i : ℕ} {Γ : Context n} {C : Term (n + 1)} {z s t : Term n}
      (hC : DerivationH H (Γ.snoc .nat) C (.univ i))
      (hz : DerivationH H Γ z (C.instantiate .zero)) (hs : DerivationH H Γ s C.natStepType)
      (ht : DerivationH H Γ t .nat) : DerivationH H Γ (.natrec C z s t) (C.instantiate t)
  | star {n : ℕ} {Γ : Context n} (hΓ : ContextDerivationH H Γ) : DerivationH H Γ .star .unit
  | absurd {n i : ℕ} {Γ : Context n} {A e : Term n}
      (hA : DerivationH H Γ A (.univ i)) (he : DerivationH H Γ e .empty) : DerivationH H Γ (.absurd A e) A
  | id {n i : ℕ} {Γ : Context n} {A a b : Term n}
      (hA : DerivationH H Γ A (.univ i)) (ha : DerivationH H Γ a A) (hb : DerivationH H Γ b A) :
      DerivationH H Γ (.id A a b) (.univ i)
  | refl {n i : ℕ} {Γ : Context n} {A a : Term n}
      (hA : DerivationH H Γ A (.univ i)) (ha : DerivationH H Γ a A) : DerivationH H Γ (.refl a) (.id A a a)
  | j {n i j : ℕ} {Γ : Context n} {A a d b p : Term n} {C : Term (n + 2)}
      (hA : DerivationH H Γ A (.univ i)) (ha : DerivationH H Γ a A)
      (hC : DerivationH H (motiveContext Γ A a) C (.univ j))
      (hd : DerivationH H Γ d (C.instantiate₂ a (.refl a)))
      (hb : DerivationH H Γ b A) (hp : DerivationH H Γ p (.id A a b)) :
      DerivationH H Γ (.j A a C d b p) (C.instantiate₂ b p)
  | conv {n i : ℕ} {Γ : Context n} {t A B : Term n}
      (ht : DerivationH H Γ t A) (hB : DerivationH H Γ B (.univ i)) (hAB : Conversion A B) : DerivationH H Γ t B
  | cumulative {n i j : ℕ} {Γ : Context n} {A : Term n}
      (hA : DerivationH H Γ A (.univ i)) (hij : i ≤ j) : DerivationH H Γ A (.univ j)

end

mutual

/-- Budget of every declaration's typing proof, including all its premises. -/
def ContextDerivationH.universeBudget {H : Set ScopedTyping} : {n : ℕ} → {Γ : Context n} → ContextDerivationH H Γ → ℕ
  | _, _, .nil => 0
  | _, _, .snoc hΓ hA => max hΓ.universeBudget hA.universeBudget

/-- A whole-proof budget including context, endpoints, rules and conversions. -/
def DerivationH.universeBudget {H : Set ScopedTyping} : {n : ℕ} → {Γ : Context n} → {t A : Term n} →
    DerivationH H Γ t A → ℕ
  | _, Γ, t, A, h => max (max Γ.universeBound (max t.universeBound A.universeBound))
      (match h with
    | .hyp _ => 0
    | .univ hΓ _ | .nat hΓ | .empty hΓ | .unit hΓ | .var hΓ _ |
        .zero hΓ | .star hΓ => hΓ.universeBudget
    | .pi h k | .sigma h k | .app h k | .absurd h k | .refl h k =>
        max h.universeBudget k.universeBudget
    | .lam h k l | .id h k l => max h.universeBudget (max k.universeBudget l.universeBudget)
    | .pair h k l m | .natrec h k l m =>
        max (max h.universeBudget k.universeBudget) (max l.universeBudget m.universeBudget)
    | .fst h | .snd h | .succ h | .cumulative h _ => h.universeBudget
    | .j h k l m p q => max (max h.universeBudget k.universeBudget)
        (max (max l.universeBudget m.universeBudget) (max p.universeBudget q.universeBudget))
    | .conv h k c => max h.universeBudget (max k.universeBudget c.universeBudget))

end


/-- Original hypothetical proof data with a bound on every proof-tree occurrence. -/
abbrev BoundedDerivationH (levels : ℕ) (H : Set ScopedTyping) {n : ℕ}
    (Γ : Context n) (t A : Term n) :=
  {d : DerivationH H Γ t A // d.universeBudget ≤ levels}

end Silmaril.Logic.TypeTheory.IntensionalMLTT
