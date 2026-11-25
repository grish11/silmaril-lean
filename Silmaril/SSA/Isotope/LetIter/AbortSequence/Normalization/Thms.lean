module

public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Normalization.Defs
public import Silmaril.SSA.Isotope.LetIter.AbortSequence.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.AbortSequence.Normalization

/-! # Equality and pure uniformity after sequencing aborts -/

public section

universe u v w r

namespace Silmaril.Isotope.LetIter.LocallyNameless.AbortNormalization

variable {ν : Type w} {Φ : Type v} {n m : Nat}

/-- Sequencing aborts commutes with renaming bound variables. -/
theorem sequenceAborts_rename (ρ : Fin n → Fin m) (t : Tm ν Φ n) :
    sequenceAborts (Tm.rename ρ t) = Tm.rename ρ (sequenceAborts t) :=
  Proofs.sequenceAborts_rename ρ t

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ] [DecidableEq ν]
  {Γ : Isotope.Ctx ν τ} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}

/-- Sequencing aborts preserves exact typing. -/
theorem sequenceAborts_typing (h : HasType Φ Γ β t A) : HasType Φ Γ β (sequenceAborts t) A :=
  Proofs.sequenceAborts_typing h

variable {ε : Type r} [HasEff Φ ε] {pe : ε}

omit [DecidableEq ν] in
/-- Sequencing a pure term preserves syntactic purity. -/
theorem sequenceAborts_pure (h : Pure pe t) : Pure pe (sequenceAborts t) :=
  Proofs.sequenceAborts_pure h

/-- Sequencing aborts preserves the exact typed equations. -/
theorem sequenceAborts_exact {a b : Tm ν Φ n} (eq : Equiv pe Γ β a b A) :
    Equiv pe Γ β (sequenceAborts a) (sequenceAborts b) A :=
  Proofs.sequenceAborts_exact eq

/-- Sequencing aborts turns repaired equivalences into exact typed equations. -/
theorem sequenceAborts_repaired {a b : Tm ν Φ n} (eq : AbortEquiv pe Γ β a b A) :
    Equiv pe Γ β (sequenceAborts a) (sequenceAborts b) A :=
  Proofs.sequenceAborts_repaired eq

/-- A typed term and its sequenced form are equivalent in the abort extension. -/
theorem repaired_sequenceAborts (ht : HasType Φ Γ β t A) :
    AbortEquiv pe Γ β t (sequenceAborts t) A :=
  Proofs.repaired_sequenceAborts ht

/-- On typed terms, repaired equality is exact equality of the sequenced forms. -/
theorem repaired_iff_sequenceAborts_exact {a b : Tm ν Φ n}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b A) :
    AbortEquiv pe Γ β a b A ↔ Equiv pe Γ β (sequenceAborts a) (sequenceAborts b) A :=
  Proofs.repaired_iff_sequenceAborts_exact ha hb

/-- Pure uniformity is admissible with a square in the existing abort relation. -/
theorem repaired_uniformity {a : Tm ν Φ n} {h b b' : Tm ν Φ (n + 1)}
    {A' B : τ}
    (ha : HasType Φ Γ β a A)
    (hh : HasType Φ Γ (β.snoc A) h A') (hp : Pure pe h)
    (hb : HasType Φ Γ (β.snoc A) b (coprod B A))
    (hb' : HasType Φ Γ (β.snoc A') b' (coprod B A'))
    (square : AbortEquiv pe Γ (β.snoc A)
      (.case b (.inl (.bv (0 : Fin (n + 2)))) (.inr (Tm.underBinder h)))
      (Tm.instantiate (Tm.underBinder b') h) (coprod B A')) :
    AbortEquiv pe Γ β (.iter a b) (.iter (.let₁ a h) b') B :=
  Proofs.repaired_uniformity ha hh hp hb hb' square

end Silmaril.Isotope.LetIter.LocallyNameless.AbortNormalization
