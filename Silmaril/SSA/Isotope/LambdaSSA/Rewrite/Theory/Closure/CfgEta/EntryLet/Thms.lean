module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.EntryLet.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.EntryLet

/-! # Moving a typed let past a zero- or one-block CFG -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.CfgEta

universe u v

variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]

/-- Zero-block elimination and one-block CFG η give entry-let sequencing
for tables with at most one local label. -/
theorem entryLet_of_le_one {n : Nat} (h : n ≤ 1) : EntryLet (Eqv (τ := τ) (Φ := Φ)) n :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgEta.entryLet_of_le_one h

end Silmaril.Isotope.LambdaSSA.Region.CfgEta
