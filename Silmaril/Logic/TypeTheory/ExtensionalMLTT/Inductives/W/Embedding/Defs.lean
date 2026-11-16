module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Derivation
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Rules.Defs

@[expose] public section

/-! # Inclusion of the original extensional MLTT in its W extension

The inclusion retains every original term and inference constructor. Bound
variables, universe indices, free names, and context order are unchanged.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Embedding

/-- Include an original term in the extended grammar. -/
def term {k : ℕ} : ETm k → Tm k
  | .fv x => .fv x
  | .bv i => .bv i
  | .univ n => .univ n
  | .empty => .empty
  | .unit => .unit
  | .star => .star
  | .nats => .nats
  | .zero => .zero
  | .succ n => .succ (term n)
  | .natrec C s z n => .natrec (term C) (term s) (term z) (term n)
  | .pi A B => .pi (term A) (term B)
  | .sigma A B => .sigma (term A) (term B)
  | .abs A b => .abs (term A) (term b)
  | .app f a => .app (term f) (term a)
  | .pair a b => .pair (term a) (term b)
  | .fst p => .fst (term p)
  | .snd p => .snd (term p)
  | .id A a b => .id (term A) (term a) (term b)
  | .refl a => .refl (term a)
  | .absurd C e => .absurd (term C) (term e)

/-- Include an original context. -/
def context : ECtx → Ctx
  | .nil => .nil
  | .cons Γ x A => .cons (context Γ) x (term A)

/-- Include an original judgment. -/
def judgment (j : EJdg) : Jdg := ⟨context j.Γ, term j.A, term j.a, term j.b⟩

/-- Map an arbitrary theory of original judgments into the extension. -/
def theory (H : Set EJdg) : Set Jdg := judgment '' H

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Embedding
