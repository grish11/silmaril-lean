module

public import Silmaril.Semantics.Calco2019.Examples.Probability.Kleisli.Thms
public import Silmaril.Semantics.Calco2019.Examples.Probability.Subdistribution.Thms

/-! # CALCO 2019, Example 20(3)

Theorems in `Silmaril.Calco2019.Examples.Probability` compute the least
subdistribution for the printed chain, refute the proposed normalization, and
show that the guard from Example 10(3) is incompatible with pure naturality and
pure uniformity of probability-valued fixpoints.
-/

public section

namespace Silmaril.Papers.Calco2019

open CategoryTheory
open Silmaril.Calco2019 Silmaril.Calco2019.Examples.Probability

/-- Example 20(3)'s proposed operator fails on a guarded loop with the printed
transition probabilities and two distinct exit labels. -/
theorem example20_3_counterexample :
    pmfGuard.guarded (computation PMF (chain coloredExit)) ∧
      ¬ Guardedness.IsFixpoint (P := typeCoproducts.kleisli (ofTypeMonad PMF))
        (computation PMF (chain coloredExit))
        (computation PMF (normalized (chain coloredExit) (chain_guarded coloredExit))) :=
  ⟨(pmf_guarded_iff _).mpr (chain_guarded coloredExit), normalized_pmf_counterexample⟩

end Silmaril.Papers.Calco2019
