module

public import Silmaril.Semantics.RuntimeWires.Nullary.Defs
import Silmaril.Proofs.Semantics.RuntimeWires.Nullary.Scalar

public section

namespace Silmaril.RuntimeWires.Nullary

open CategoryTheory Presentation

/-- The nullary effect differs from the identity. -/
theorem scalar_ne_identity : effectfulScalar ≠ 𝟙 unitWord := Proofs.scalar_ne_identity

/-- Both orders of the sequential tensor agree with the nullary effect in either position.
Together with `scalar_ne_identity`, this is a counterexample to the trivial-centre assertion
preceding Lemma 5.3. -/
theorem scalar_central :
    ∀ {A B : Computations signatureWithScalar} (f : A ⟶ B),
      ((Computations.whiskerRight A).map effectfulScalar ≫ (Computations.whiskerLeft unitWord).map f =
        (Computations.whiskerLeft unitWord).map f ≫ (Computations.whiskerRight B).map effectfulScalar) ∧
      ((Computations.whiskerRight unitWord).map f ≫ (Computations.whiskerLeft B).map effectfulScalar =
        (Computations.whiskerLeft A).map effectfulScalar ≫ (Computations.whiskerRight unitWord).map f) :=
  Proofs.scalar_exchanges

end Silmaril.RuntimeWires.Nullary
