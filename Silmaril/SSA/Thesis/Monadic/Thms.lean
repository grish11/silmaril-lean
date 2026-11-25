module

public import Silmaril.Raw.SSA.Thesis.LambdaIter.Models.Monadic.Alg

/-! # Soundness of the exact λiter equations in monadic models

`Monadic.sound` validates exact typed equations in a lawful Elgot monad using
a model of the type formers and instructions. The type-former injectivity
hypothesis supplies coherence across typing derivations. `Alg.ofModel` gives
the associated presentation algebra.
-/
