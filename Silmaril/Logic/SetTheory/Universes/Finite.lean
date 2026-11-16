module

public import Silmaril.Logic.SetTheory.Universes.Finite.Defs
public import Silmaril.Proofs.Logic.SetTheory.FiniteUniverses

@[expose] public section

/-!
# Concrete finite universe supplies

`FiniteTower.raise` adds one level in a larger Lean universe. The supplied
`HasFiniteTower` instances have heights 1, 2 and 3, in carriers at Lean levels
`u + 1`, `u + 2` and `u + 3`. These are model-existence results. A consistency
result for a bounded type theory also needs that theory's soundness proof.
-/
