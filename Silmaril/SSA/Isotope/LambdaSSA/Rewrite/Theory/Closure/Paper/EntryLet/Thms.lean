module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.EntryLet.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLet

/-! # Sequencing from literal entry η -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper

universe u v

variable {τ : Type u} {Φ : Type v} [TypeFormers τ] [HasTy Φ τ]

/-- Literal entry η at the same arity gives entry-let sequencing. -/
theorem entryLet_of_entryEta {n : Nat} (h : EntryEta τ Φ n) :
    CfgEta.EntryLet (Eqv (τ := τ) (Φ := Φ)) n :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLet.of_entryEta h

/-- A literal instance of the existing flattening endpoint and an outgoing
substitution keep the single remaining local label. -/
theorem flattened_lsubst_ne_flat {n : Nat} (hn : n ≠ 1)
    (entry body : Region Φ) (σ : Nat → Region Φ) (e : Region Φ) (blocks : Fin n → Region Φ) :
    ((CfgEta.Codiagonal.flattened entry body).lsubst σ) ≠ .cfg e n blocks :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLet.flattened_lsubst_ne_flat hn entry body σ e blocks

end Silmaril.Isotope.LambdaSSA.Region.Paper
