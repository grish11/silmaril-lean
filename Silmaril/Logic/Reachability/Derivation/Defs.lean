module

public import Silmaril.Logic.Reachability.RuleSystem.Thms

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation

abbrev Assignment {J : Type} (D : J → Type) := (j : J) → D j
abbrev Predicate {J : Type} (D : J → Type) (W : Type) := Assignment D → W → Prop

structure Claim {J : Type} (D : J → Type) (W : Type) where
  pre : Predicate D W
  post : Predicate D W

def AgreeOutside {J : Type} {D : J → Type} (X : Set J)
    (a b : Assignment D) : Prop := ∀ j, j ∉ X → a j = b j

def Abstract {J : Type} {D : J → Type} {W : Type} (X : Set J)
    (P : Predicate D W) : Predicate D W :=
  fun a w => ∃ b, AgreeOutside X a b ∧ P b w

def Independent {J : Type} {D : J → Type} {W : Type} (X : Set J)
    (Q : Predicate D W) : Prop :=
  ∀ a b, AgreeOutside X a b → ∀ w, Q a w ↔ Q b w

/-- All eight Fig. 1 rules. A contains axioms; C contains pending circularities.
Only Transitivity promotes C. No constructor assumes a reachability conclusion. -/
inductive Derives {J W ι : Type} {D : J → Type}
    (rules : ι → RuleSystem.Scheme W) :
    Set (Claim D W) → Set (Claim D W) → Claim D W → Type where
  | step {A C P Q}
      (cover : ∀ a, RuleSystem.Covers rules (P a))
      (successors : ∀ a, RuleSystem.SuccessorsIn rules (P a) (Q a)) :
      Derives rules A C ⟨P, Q⟩
  | useAxiom {A C c} (member : c ∈ A) : Derives rules A C c
  | reflexivity {A P} : Derives rules A ∅ ⟨P, P⟩
  | transitivity {A C P B Q} :
      Derives rules A C ⟨P, B⟩ → Derives rules (A ∪ C) ∅ ⟨B, Q⟩ →
      Derives rules A C ⟨P, Q⟩
  | cases {A C P₁ P₂ Q} :
      Derives rules A C ⟨P₁, Q⟩ → Derives rules A C ⟨P₂, Q⟩ →
      Derives rules A C ⟨fun a w => P₁ a w ∨ P₂ a w, Q⟩
  | abstraction {A C P Q} (X : Set J) :
      Derives rules A C ⟨P, Q⟩ → Independent X Q →
      Derives rules A C ⟨Abstract X P, Q⟩
  | consequence {A C P Q P₀ Q₀}
      (pre : ∀ a w, P a w → P₀ a w) :
      Derives rules A C ⟨P₀, Q₀⟩ → (∀ a w, Q₀ a w → Q a w) →
      Derives rules A C ⟨P, Q⟩
  | circularity {A C c} : Derives rules A (C ∪ {c}) c → Derives rules A C c

/-- A finite complete path; length counts transitions. Bounded validity below
uses length+1, matching the source's count of vertices. -/
structure CompletePath {W : Type} (R : W → W → Prop) where
  length : Nat
  point : Nat → W
  edge : ∀ i, i < length → R (point i) (point (i + 1))
  terminal : ∀ v, ¬ R (point length) v

def Hit {W : Type} {R : W → W → Prop} (positive : Bool)
    (Q : W → Prop) (p : CompletePath R) : Prop :=
  ∃ i, i ≤ p.length ∧ Q (p.point i) ∧ (positive = true → 0 < i)

/-- Source pp.7–8: at most n vertices, with a noninitial hit in positive mode. -/
def Bounded {J W : Type} {D : J → Type} (R : W → W → Prop)
    (positive : Bool) (n : Nat) (c : Claim D W) : Prop :=
  ∀ a (p : CompletePath R), p.length + 1 ≤ n → c.pre a (p.point 0) → Hit positive (c.post a) p

def Environment {J W : Type} {D : J → Type} (R : W → W → Prop)
    (positive : Bool) (n : Nat) (E : Set (Claim D W)) : Prop :=
  ∀ c, c ∈ E → Bounded R positive n c

end Silmaril.Logic.Reachability.Derivation
