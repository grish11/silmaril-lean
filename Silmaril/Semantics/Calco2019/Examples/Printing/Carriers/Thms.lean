module

public import Silmaril.Semantics.Calco2019.Examples.Printing.Carriers.Defs
import Silmaril.Proofs.Semantics.Calco2019.Examples.PrintingCarriers

/-! # The introductory printing fixpoints in CALCO 2019 -/

public section

universe u

namespace Silmaril.Calco2019.Examples.Printing.Carriers

open CategoryTheory.Limits

/-- Finite words with returns form the initial algebra of `X + A × -`. -/
noncomputable def initial (A X : Type u) : IsInitial (algebra A X) :=
  Proofs.initial A X

/-- Finite returns and infinite streams form the final coalgebra of `X + A × -`. -/
noncomputable def terminal (A X : Type u) : IsTerminal (coalgebra A X) :=
  Proofs.terminal A X

/-- The chosen inductive identity-base resumption for the printing signature. -/
@[expose] noncomputable def inductiveResumptions (A : Type u) : InitialResumptions (family A) where
  algebra := algebra A
  initial := initial A

/-- The chosen coinductive identity-base resumption for the printing signature. -/
@[expose] noncomputable def coinductiveResumptions (A : Type u) : FinalResumptions (family A) where
  coalgebra := coalgebra A
  final := terminal A

end Silmaril.Calco2019.Examples.Printing.Carriers
