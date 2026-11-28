module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Generation.PackedTerm.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedPackedTerm

/-! # Opening a typed packed term -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.PackedBody

open Silmaril Silmaril.Isotope.LambdaSSA

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {X A D : τ}

/-- Supply the original input and scrutinee result to a packed singleton term. -/
theorem applyPackedTerm_typed {t : Tm Φ} (ht : Tm.HasType [product X A] t D) :
    Tm.HasType [A, X] (applyPackedTerm t) D :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RetainedPackedTerm.applyPackedTerm_typed ht

end Silmaril.Isotope.LambdaSSA.Region.Paper.PackedBody
