module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses.Defs
public import Silmaril.Logic.TypeTheory.IntensionalMLTT.RawRealizability.Soundness
import Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses

public section

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Substitute actual proof trees at hypothesis leaves beneath every original rule. -/
noncomputable def DerivationH.bind {H K : Set ScopedTyping} {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : DerivationH H Γ t A)
    (hH : ∀ q ∈ H, DerivationH K q.Γ q.term q.carrier) : DerivationH K Γ t A :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses.bind d hH

/-- Original typing hypotheses can be enlarged. -/
noncomputable def DerivationH.mono {H K : Set ScopedTyping} {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : DerivationH H Γ t A) (hHK : H ⊆ K) : DerivationH K Γ t A :=
  d.bind (fun _ hq => .hyp (hHK hq))

/-- Every unchanged original derivation embeds rule for rule into the hypothetical system. -/
noncomputable def DerivationH.ofOriginal {H : Set ScopedTyping} {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : Derivation Γ t A) : DerivationH H Γ t A :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses.ofOriginal d

/-- Interpreting the hypotheses by original proof data recovers an actual original proof. -/
noncomputable def DerivationH.toOriginal {H : Set ScopedTyping} {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : DerivationH H Γ t A)
    (hH : ∀ q ∈ H, Derivation q.Γ q.term q.carrier) : Derivation Γ t A :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses.toOriginal d hH

/-- No-hypothesis proof trees recover exactly the original source calculus. -/
noncomputable def DerivationH.erase {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : DerivationH ∅ Γ t A) : Derivation Γ t A := d.toOriginal (fun _ hq => False.elim hq)

/-- The hypothetical extension does not add any closed-hypothesis source judgment. -/
theorem DerivationH.empty_iff {n : ℕ} {Γ : Context n} {t A : Term n} :
    Nonempty (DerivationH ∅ Γ t A) ↔ Typing Γ t A := by
  constructor
  · rintro ⟨d⟩; exact ⟨d.erase⟩
  · rintro ⟨d⟩; exact ⟨.ofOriginal d⟩

/-- Actual sentence realization is preserved by every original rule with hypothesis leaves. -/
theorem DerivationH.realizes {H : Set ScopedTyping} {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : DerivationH H Γ t A)
    (hH : ∀ q ∈ H, RawRealizability.Valid q.Γ q.term q.carrier) : RawRealizability.Valid Γ t A :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses.realizes d hH

/-- The entire scoped conclusion is included in the proof-tree budget. -/
theorem DerivationH.judgment_le_budget {H : Set ScopedTyping} {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : DerivationH H Γ t A) : (⟨n, Γ, t, A⟩ : ScopedTyping).universeBound ≤ d.universeBudget := by
  rw [DerivationH.universeBudget.eq_def, ScopedTyping.universeBound]
  exact Nat.le_max_left _ _

/-- A bounded proof can be viewed at a larger whole-proof cap without changing its tree. -/
def BoundedDerivationH.include {levels more : ℕ} {H : Set ScopedTyping} {n : ℕ}
    {Γ : Context n} {t A : Term n} (h : levels ≤ more) (d : BoundedDerivationH levels H Γ t A) :
    BoundedDerivationH more H Γ t A := ⟨d.val, d.property.trans h⟩

/-- A bounded scoped assumption has its own actual hypothesis leaf. -/
def BoundedDerivationH.hyp {levels : ℕ} {H : Set ScopedTyping} (q : ScopedTyping)
    (hq : q ∈ H) (hBound : q.UsesBelow levels) : BoundedDerivationH levels H q.Γ q.term q.carrier :=
  ⟨.hyp hq, by
    have hScope : max q.Γ.universeBound (max q.term.universeBound q.carrier.universeBound) ≤ levels := by
      simpa only [ScopedTyping.UsesBelow, ScopedTyping.universeBound] using hBound
    simpa only [DerivationH.universeBudget] using max_le hScope (Nat.zero_le levels)⟩

/-- Substitute bounded proof trees at all leaves while allowing a larger finite cap. -/
noncomputable def BoundedDerivationH.transform {levels more : ℕ} {H K : Set ScopedTyping} {n : ℕ}
    {Γ : Context n} {t A : Term n} (d : BoundedDerivationH levels H Γ t A) (h : levels ≤ more)
    (hH : ∀ q ∈ H, BoundedDerivationH more K q.Γ q.term q.carrier) :
    BoundedDerivationH more K Γ t A :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses.bindBoundedCore d.val more
    (d.property.trans h) hH

/-- Hypothesis substitution preserves a common bound on the complete proof trees. -/
noncomputable def BoundedDerivationH.bind {levels : ℕ} {H K : Set ScopedTyping} {n : ℕ}
    {Γ : Context n} {t A : Term n} (d : BoundedDerivationH levels H Γ t A)
    (hH : ∀ q ∈ H, BoundedDerivationH levels K q.Γ q.term q.carrier) :
    BoundedDerivationH levels K Γ t A := d.transform (Nat.le_refl _) hH

/-- Original bounded trees embed without increasing their universe count. -/
noncomputable def BoundedDerivationH.ofOriginal {levels : ℕ} {H : Set ScopedTyping} {n : ℕ}
    {Γ : Context n} {t A : Term n} (d : BoundedDerivation levels Γ t A) :
    BoundedDerivationH levels H Γ t A :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses.ofOriginalBoundedCore
    d.val levels d.property

/-- Removing empty hypotheses also preserves the complete original proof budget. -/
noncomputable def BoundedDerivationH.toOriginal {levels : ℕ} {n : ℕ} {Γ : Context n} {t A : Term n}
    (d : BoundedDerivationH levels ∅ Γ t A) : BoundedDerivation levels Γ t A :=
  Silmaril.Proofs.Logic.TypeTheory.IntensionalMLTT.OriginalHypotheses.toOriginalBoundedCore
    d.val levels d.property

/-- At each fixed proof cap, empty-hypothesis derivability is exactly original derivability. -/
theorem BoundedDerivationH.empty_iff {levels n : ℕ} {Γ : Context n} {t A : Term n} :
    Nonempty (BoundedDerivationH levels ∅ Γ t A) ↔ Nonempty (BoundedDerivation levels Γ t A) := by
  constructor
  · rintro ⟨d⟩; exact ⟨d.toOriginal⟩
  · rintro ⟨d⟩; exact ⟨.ofOriginal d⟩

/-- Every bounded hypothetical conclusion is a genuinely bounded scoped sentence. -/
theorem BoundedDerivationH.usesBelow {levels : ℕ} {H : Set ScopedTyping} {n : ℕ}
    {Γ : Context n} {t A : Term n} (d : BoundedDerivationH levels H Γ t A) :
    (⟨n, Γ, t, A⟩ : ScopedTyping).UsesBelow levels :=
  d.val.judgment_le_budget.trans d.property

/-- Valid actual typing assumptions cannot produce an original closed Empty inhabitant. -/
theorem DerivationH.no_closed_empty {H : Set ScopedTyping}
    (hH : ∀ q ∈ H, RawRealizability.Valid q.Γ q.term q.carrier) (t : Term 0) :
    ¬ Nonempty (DerivationH H .nil t .empty) := by
  rintro ⟨d⟩
  rcases d.realizes hH Fin.elim0 trivial with ⟨i, X, hX, ht⟩
  exact hX.no_empty_realizer _ ht

end Silmaril.Logic.TypeTheory.IntensionalMLTT
