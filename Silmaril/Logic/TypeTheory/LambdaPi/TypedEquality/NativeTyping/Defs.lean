module

public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeConversion.Thms
public import Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.EqualSubstitution.Thms
public import Silmaril.Logic.TypeTheory.LambdaPi.ContextConversion.Thms
public import Silmaril.Logic.TypeTheory.LambdaPi.Eta.Typing.Thms

@[expose] public section
namespace Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeTyping
open NativeConversion

/-- Actual native typings for all source variable images, including globals.
This interprets declarations only; it assumes no compiled endpoint typing. -/
def Assignment {n : ℕ} (Γ : IntensionalMLTT.Context n)
    (declared : String → LambdaPi.Term → Prop) (Δ : List LambdaPi.Term)
    (σ : Fin n → LambdaPi.Term) : Prop :=
  ∀ {i A}, IntensionalMLTT.Lookup Γ i A →
    Derives (Calculus.lfBetaEta declared) ∅ ⟨Δ, σ i, term σ A⟩

end Silmaril.Logic.TypeTheory.LambdaPi.TypedEquality.NativeTyping
