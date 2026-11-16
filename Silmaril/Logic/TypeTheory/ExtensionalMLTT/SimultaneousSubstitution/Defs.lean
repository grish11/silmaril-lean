module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Simultaneously replace free names by bound-closed object terms in any de Bruijn scope. -/
def ETm.fmap {k : ℕ} (t : ETm k) (σ : String → ETm 0) : ETm k :=
  match t with
  | .fv y => (σ y).castLE (Nat.zero_le k)
  | .bv i => .bv i
  | .univ n => .univ n
  | .empty => .empty
  | .unit => .unit
  | .star => .star
  | .nats => .nats
  | .zero => .zero
  | .succ t => .succ (t.fmap σ)
  | .natrec C s z t => .natrec (C.fmap σ) (s.fmap σ)
      (z.fmap σ) (t.fmap σ)
  | .pi A B => .pi (A.fmap σ) (B.fmap σ)
  | .sigma A B => .sigma (A.fmap σ) (B.fmap σ)
  | .abs A b => .abs (A.fmap σ) (b.fmap σ)
  | .app f a => .app (f.fmap σ) (a.fmap σ)
  | .pair a b => .pair (a.fmap σ) (b.fmap σ)
  | .fst t => .fst (t.fmap σ)
  | .snd t => .snd (t.fmap σ)
  | .id A a b => .id (A.fmap σ) (a.fmap σ) (b.fmap σ)
  | .refl a => .refl (a.fmap σ)
  | .absurd C e => .absurd (C.fmap σ) (e.fmap σ)



/-- An explicit finite set outside which an assignment fixes every name. -/
def ETm.Supported (σ : String → ETm 0) (K : Finset String) : Prop :=
  ∀ y ∉ K, σ y = .fv y

/-- Actual target typings for the images of every source lookup. -/
def ECtx.Assignment (σ : String → ETm 0) (Γ Δ : ECtx) : Prop :=
  ∀ {y B}, Γ.Lookup y B → ECtx.JEqH ∅ Δ (B.fmap σ) (σ y) (σ y)

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
