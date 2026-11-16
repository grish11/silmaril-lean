module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure.Defs

@[expose] public section

/-!
# Context transport for actual theory leaves

Only original hypothesis judgments receive a separate transport contract.
The full derivation is rebuilt by induction on the existing rules. Context
formation in the target is explicit; no regularity of arbitrary theory leaves
is assumed.

`ContextClosure` is an explicitly enlarged theory. It preserves the carrier
and endpoints of each original leaf, and makes no semantic-conservativity
claim about arbitrary source theories.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Transport original theory leaves through actual typed lookup embeddings. -/
def HypothesisTransport (H K : Set EJdg) : Prop :=
  ∀ {Γ Δ : ECtx} {A a b : ETm 0}, (⟨Γ, A, a, b⟩ : EJdg) ∈ H → Γ.Embeds Δ →
    ECtx.JEqH K Δ .unit .star .star → ECtx.JEqH K Δ A a b

/-- Enlarge a theory by preserving each original leaf under context embeddings. -/
def ContextClosure (H : Set EJdg) : Set EJdg :=
  {j | ∃ Γ, (⟨Γ, j.A, j.a, j.b⟩ : EJdg) ∈ H ∧ Γ.Embeds j.Γ}

namespace TheoryStructure

/-- A fixed closed type equation, satisfied by the existing set interpretation. -/
def fixedAxiom : EJdg :=
  ⟨.nil, .univ 0, .unit, .id .nats .zero .zero⟩

/-- Contextual instances of the same fixed carrier and endpoints. -/
def fixedTheory : Set EJdg := ContextClosure {fixedAxiom}

/-- A lambda whose body uses the axiom by conversion, not as the final conclusion. -/
def fixedLambda : ETm 0 := .abs .nats .star

/-- The actual result type of the axiom-using lambda. -/
def fixedLambdaType : ETm 0 := ETm.arr .nats (.id .nats .zero .zero)

end TheoryStructure

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
